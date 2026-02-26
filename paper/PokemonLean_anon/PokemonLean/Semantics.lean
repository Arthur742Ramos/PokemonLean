import PokemonLean.Basic

namespace PokemonLean.Semantics

open PokemonLean

def benchLimit : Nat := 5

inductive Action
  | playPokemonToBench (card : Card)
  | playItem (card : Card)
  | playSupporter (card : Card)
  | playTool (card : Card)
  | playSupporterDraw (card : Card) (count : Nat)
  | playItemHeal (card : Card) (amount : Nat)
  | evolveActive (card : Card)
  | useAbilityHeal (amount : Nat)
  | useAbilityDraw (count : Nat)
  | attachEnergy (energyType : EnergyType)
  | attack (attackIndex : Nat)
  | retreat
  | endTurn
  | drawCard
  deriving Repr, BEq, DecidableEq

inductive StepError
  | cardNotInHand
  | benchFull
  | noActivePokemon
  | evolutionHpTooLow
  | noDefenderPokemon
  | invalidAttackIndex
  | insufficientEnergy
  | emptyEffectStack
  | noBenchPokemon
  | emptyDeck
  deriving Repr, BEq, DecidableEq

def playTrainer (state : GameState) (card : Card) : Except StepError GameState :=
  let player := state.activePlayer
  let playerState := getPlayerState state player
  if isTrainer card then
    match removeFirst card playerState.hand with
    | none => .error .cardNotInHand
    | some newHand =>
      let updatedPlayerState := { playerState with hand := newHand, discard := card :: playerState.discard }
      .ok (setPlayerState state player updatedPlayerState)
  else
    .error .cardNotInHand

-- Helper function for drawing cards from deck
def drawFromDeck (playerState : PlayerState) (n : Nat) : Option (List Card × List Card) :=
  if n ≤ playerState.deck.length then
    let drawn := playerState.deck.take n
    let rest := playerState.deck.drop n
    some (drawn, rest)
  else
    none

-- Play a trainer card that draws cards
def playTrainerDraw (state : GameState) (card : Card) (drawCount : Nat) : Except StepError GameState :=
  let player := state.activePlayer
  let playerState := getPlayerState state player
  if isTrainer card then
    match removeFirst card playerState.hand with
    | none => .error .cardNotInHand
    | some newHand =>
      match drawFromDeck playerState drawCount with
      | none => .error .emptyDeck
      | some (drawn, rest) =>
        let updatedPlayerState :=
          { playerState with
            deck := rest
            hand := newHand ++ drawn
            discard := card :: playerState.discard }
        .ok (setPlayerState state player updatedPlayerState)
  else
    .error .cardNotInHand

-- Play a trainer card that heals
def playTrainerHeal (state : GameState) (card : Card) (healAmount : Nat) : Except StepError GameState :=
  let player := state.activePlayer
  let playerState := getPlayerState state player
  if isTrainer card then
    match removeFirst card playerState.hand with
    | none => .error .cardNotInHand
    | some newHand =>
      match playerState.active with
      | none => .error .noActivePokemon
      | some active =>
        let newDamage := Nat.sub active.damage healAmount
        let updatedActive := { active with damage := newDamage }
        let updatedPlayerState :=
          { playerState with
            hand := newHand
            active := some updatedActive
            discard := card :: playerState.discard }
        .ok (setPlayerState state player updatedPlayerState)
  else
    .error .cardNotInHand

-- Main step function: execute a single action
def step (state : GameState) (action : Action) : Except StepError GameState :=
  match action with
  | .endTurn =>
    .ok { state with activePlayer := otherPlayer state.activePlayer }
  | .playPokemonToBench card =>
    let player := state.activePlayer
    let playerState := getPlayerState state player
    match removeFirst card playerState.hand with
    | none => .error .cardNotInHand
    | some newHand =>
      if playerState.bench.length < benchLimit then
        let pokemon := toPokemonInPlay card
        let updatedPlayerState :=
          { playerState with hand := newHand, bench := playerState.bench ++ [pokemon] }
        .ok (setPlayerState state player updatedPlayerState)
      else
        .error .benchFull
  | .playItem card =>
    playTrainer state card
  | .playSupporter card =>
    playTrainer state card
  | .playTool card =>
    playTrainer state card
  | .playSupporterDraw card count =>
    playTrainerDraw state card count
  | .playItemHeal card amount =>
    playTrainerHeal state card amount
  | .evolveActive card =>
    let player := state.activePlayer
    let playerState := getPlayerState state player
    match playerState.active with
    | none => .error .noActivePokemon
    | some active =>
      match removeFirst card playerState.hand with
      | none => .error .cardNotInHand
      | some newHand =>
        if active.card.hp ≤ card.hp then
          let evolved := { active with card := card }
          -- Discard the old card (the pre-evolution) to maintain card conservation
          let updatedPlayerState := { playerState with
            hand := newHand,
            active := some evolved,
            discard := active.card :: playerState.discard }
          .ok (setPlayerState state player updatedPlayerState)
        else
          .error .evolutionHpTooLow
  | .useAbilityHeal amount =>
    let player := state.activePlayer
    let playerState := getPlayerState state player
    match playerState.active with
    | none => .error .noActivePokemon
    | some active =>
      let newDamage := Nat.sub active.damage amount
      let updatedActive := { active with damage := newDamage }
      let updatedPlayerState := { playerState with active := some updatedActive }
      .ok (setPlayerState state player updatedPlayerState)
  | .useAbilityDraw count =>
    let player := state.activePlayer
    let playerState := getPlayerState state player
    match drawFromDeck playerState count with
    | none => .error .emptyDeck
    | some (drawn, rest) =>
      let updatedPlayerState :=
        { playerState with deck := rest, hand := playerState.hand ++ drawn }
      .ok (setPlayerState state player updatedPlayerState)
  | .attachEnergy energyType =>
    let player := state.activePlayer
    let playerState := getPlayerState state player
    match playerState.active with
    | none => .error .noActivePokemon
    | some active =>
      let updatedActive := { active with energy := energyType :: active.energy }
      let updatedPlayerState := { playerState with active := some updatedActive }
      .ok (setPlayerState state player updatedPlayerState)
  | .attack attackIndex =>
    let attackerPlayer := state.activePlayer
    let defenderPlayer := otherPlayer attackerPlayer
    let attackerState := getPlayerState state attackerPlayer
    let defenderState := getPlayerState state defenderPlayer
    match attackerState.active with
    | none => .error .noActivePokemon
    | some attacker =>
      match defenderState.active with
      | none => .error .noDefenderPokemon
      | some defender =>
        match listGet? attacker.card.attacks attackIndex with
        | none => .error .invalidAttackIndex
        | some attack =>
          if hasEnergyCost attack attacker.energy then
            let damage := calculateDamage attack attacker.card.energyType defender.card
            let damagedDefender := applyDamage defender damage
            let effectedDefender := applyAttackEffects damagedDefender attack.effects
            if effectedDefender.damage >= effectedDefender.card.hp then
              let (updatedAttacker, updatedDefender) := takePrize attackerState defenderState
              let newDefenderState :=
                { updatedDefender with active := none, discard := defender.card :: updatedDefender.discard }
              let newState := setPlayerState state attackerPlayer updatedAttacker
              let finalState := setPlayerState newState defenderPlayer newDefenderState
              .ok { finalState with activePlayer := otherPlayer state.activePlayer }
            else
              let newDefenderState := { defenderState with active := some effectedDefender }
              let newState := setPlayerState state defenderPlayer newDefenderState
              .ok { newState with activePlayer := otherPlayer state.activePlayer }
          else
            .error .insufficientEnergy
  | .retreat =>
    let player := state.activePlayer
    let playerState := getPlayerState state player
    match playerState.active with
    | none => .error .noActivePokemon
    | some active =>
      match playerState.bench with
      | [] => .error .noBenchPokemon
      | newActive :: rest =>
        let updatedBench := rest ++ [active]
        let updatedPlayerState := { playerState with active := some newActive, bench := updatedBench }
        .ok (setPlayerState state player updatedPlayerState)
  | .drawCard =>
    let player := state.activePlayer
    let playerState := getPlayerState state player
    match playerState.deck with
    | [] => .error .emptyDeck
    | top :: rest =>
      let updatedPlayerState := { playerState with deck := rest, hand := top :: playerState.hand }
      .ok (setPlayerState state player updatedPlayerState)

-- stepMany: execute a list of actions
def stepMany (state : GameState) (actions : List Action) : Except StepError GameState :=
  actions.foldlM (fun st action => step st action) state

-- Theorems about step preserving/changing active player
theorem step_activePlayer_endTurn (state state' : GameState)
    (hStep : step state .endTurn = .ok state') :
    state'.activePlayer = otherPlayer state.activePlayer := by
  simp [step] at hStep
  cases hStep
  rfl

theorem step_activePlayer_playPokemonToBench (state : GameState) (card : Card) (state' : GameState)
    (hStep : step state (.playPokemonToBench card) = .ok state') :
    state'.activePlayer = state.activePlayer := by
  cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
  · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
    by_cases hBench : state.playerOne.bench.length < benchLimit
    · simp [hBench] at hStep
      cases hStep
      rfl
    · simp [hBench] at hStep
  · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
    by_cases hBench : state.playerTwo.bench.length < benchLimit
    · simp [hBench] at hStep
      cases hStep
      rfl
    · simp [hBench] at hStep

theorem step_activePlayer_playItem (state : GameState) (card : Card) (state' : GameState)
    (hStep : step state (.playItem card) = .ok state') :
    state'.activePlayer = state.activePlayer := by
  cases hPlayer : state.activePlayer <;> simp only [step, playTrainer, hPlayer, getPlayerState, setPlayerState] at hStep
  · split at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      cases hStep
      rfl
    · simp at hStep
  · split at hStep
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      cases hStep
      rfl
    · simp at hStep

theorem step_activePlayer_playSupporter (state : GameState) (card : Card) (state' : GameState)
    (hStep : step state (.playSupporter card) = .ok state') :
    state'.activePlayer = state.activePlayer := by
  cases hPlayer : state.activePlayer <;> simp only [step, playTrainer, hPlayer, getPlayerState, setPlayerState] at hStep
  · split at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      cases hStep
      rfl
    · simp at hStep
  · split at hStep
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      cases hStep
      rfl
    · simp at hStep

theorem step_activePlayer_playSupporterDraw (state : GameState) (card : Card) (count : Nat) (state' : GameState)
    (hStep : step state (.playSupporterDraw card count) = .ok state') :
    state'.activePlayer = state.activePlayer := by
  simp only [step, playTrainerDraw, drawFromDeck, getPlayerState, setPlayerState] at hStep
  cases hPlayer : state.activePlayer <;> simp [hPlayer] at hStep
  all_goals split at hStep <;> try simp at hStep
  all_goals split at hStep <;> try simp at hStep
  all_goals split at hStep <;> try simp at hStep
  all_goals first | exact hStep.symm | rfl | (cases hStep; rfl)

theorem step_activePlayer_playItemHeal (state : GameState) (card : Card) (amount : Nat) (state' : GameState)
    (hStep : step state (.playItemHeal card amount) = .ok state') :
    state'.activePlayer = state.activePlayer := by
  cases hPlayer : state.activePlayer <;>
    simp only [step, playTrainerHeal, hPlayer, getPlayerState, setPlayerState] at hStep
  · split at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      cases hActive : state.playerOne.active <;> simp [hActive] at hStep
      cases hStep
      rfl
    · simp at hStep
  · split at hStep
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
      cases hStep
      rfl
    · simp at hStep

theorem step_activePlayer_evolveActive (state : GameState) (card : Card) (state' : GameState)
    (hStep : step state (.evolveActive card) = .ok state') :
    state'.activePlayer = state.activePlayer := by
  cases hPlayer : state.activePlayer <;>
    simp only [step, hPlayer, getPlayerState, setPlayerState] at hStep
  · cases hActive : state.playerOne.active <;> simp [hActive] at hStep
    cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
    split at hStep
    · cases hStep; rfl
    · simp at hStep
  · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
    cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
    split at hStep
    · cases hStep; rfl
    · simp at hStep

theorem step_activePlayer_useAbilityHeal (state : GameState) (amount : Nat) (state' : GameState)
    (hStep : step state (.useAbilityHeal amount) = .ok state') :
    state'.activePlayer = state.activePlayer := by
  cases hPlayer : state.activePlayer <;>
    simp only [step, hPlayer, getPlayerState, setPlayerState] at hStep
  · cases hActive : state.playerOne.active <;> simp [hActive] at hStep
    cases hStep
    rfl
  · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
    cases hStep
    rfl

theorem step_activePlayer_useAbilityDraw (state : GameState) (count : Nat) (state' : GameState)
    (hStep : step state (.useAbilityDraw count) = .ok state') :
    state'.activePlayer = state.activePlayer := by
  simp only [step] at hStep
  cases hPlayer : state.activePlayer <;>
    simp only [hPlayer, getPlayerState] at hStep
  · cases hDraw : drawFromDeck state.playerOne count with
    | none => simp [hDraw] at hStep
    | some result =>
      simp only [hDraw] at hStep
      cases result with
      | mk drawn rest =>
        simp only [Except.ok.injEq] at hStep
        rw [← hStep]
        simp only [setPlayerState]
        exact hPlayer
  · cases hDraw : drawFromDeck state.playerTwo count with
    | none => simp [hDraw] at hStep
    | some result =>
      simp only [hDraw] at hStep
      cases result with
      | mk drawn rest =>
        simp only [Except.ok.injEq] at hStep
        rw [← hStep]
        simp only [setPlayerState]
        exact hPlayer

theorem step_activePlayer_playTool (state : GameState) (card : Card) (state' : GameState)
    (hStep : step state (.playTool card) = .ok state') :
    state'.activePlayer = state.activePlayer := by
  cases hPlayer : state.activePlayer <;> simp only [step, playTrainer, hPlayer, getPlayerState, setPlayerState] at hStep
  · split at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      cases hStep
      rfl
    · simp at hStep
  · split at hStep
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      cases hStep
      rfl
    · simp at hStep

theorem step_activePlayer_attachEnergy (state : GameState) (energyType : EnergyType) (state' : GameState)
    (hStep : step state (.attachEnergy energyType) = .ok state') :
    state'.activePlayer = state.activePlayer := by
  cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
  · cases hActive : state.playerOne.active <;> simp [hActive] at hStep
    cases hStep
    rfl
  · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
    cases hStep
    rfl

theorem step_activePlayer_retreat (state : GameState) (state' : GameState)
    (hStep : step state .retreat = .ok state') :
    state'.activePlayer = state.activePlayer := by
  cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
  · cases hActive : state.playerOne.active <;> simp [hActive] at hStep
    cases hBench : state.playerOne.bench <;> simp [hBench] at hStep
    cases hStep
    rfl
  · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
    cases hBench : state.playerTwo.bench <;> simp [hBench] at hStep
    cases hStep
    rfl

theorem step_activePlayer_drawCard (state : GameState) (state' : GameState)
    (hStep : step state .drawCard = .ok state') :
    state'.activePlayer = state.activePlayer := by
  cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
  · cases hDeck : state.playerOne.deck <;> simp [hDeck] at hStep
    cases hStep
    rfl
  · cases hDeck : state.playerTwo.deck <;> simp [hDeck] at hStep
    cases hStep
    rfl

theorem step_activePlayer_attack (state : GameState) (attackIndex : Nat) (state' : GameState)
    (hStep : step state (.attack attackIndex) = .ok state') :
    state'.activePlayer = otherPlayer state.activePlayer := by
  simp only [step] at hStep
  cases hPlayer : state.activePlayer <;>
    simp only [hPlayer, getPlayerState, otherPlayer] at hStep ⊢
  · -- playerOne is active
    cases hAttacker : state.playerOne.active with
    | none => simp [hAttacker] at hStep
    | some attacker =>
      simp only [hAttacker] at hStep
      cases hDefender : state.playerTwo.active with
      | none => simp [hDefender] at hStep
      | some defender =>
        simp only [hDefender] at hStep
        cases hGetAttack : listGet? attacker.card.attacks attackIndex with
        | none => simp [hGetAttack] at hStep
        | some attack =>
          simp only [hGetAttack] at hStep
          split at hStep
          · split at hStep <;> simp only [Except.ok.injEq] at hStep <;> rw [← hStep] <;> rfl
          · simp at hStep
  · -- playerTwo is active
    cases hAttacker : state.playerTwo.active with
    | none => simp [hAttacker] at hStep
    | some attacker =>
      simp only [hAttacker] at hStep
      cases hDefender : state.playerOne.active with
      | none => simp [hDefender] at hStep
      | some defender =>
        simp only [hDefender] at hStep
        cases hGetAttack : listGet? attacker.card.attacks attackIndex with
        | none => simp [hGetAttack] at hStep
        | some attack =>
          simp only [hGetAttack] at hStep
          split at hStep
          · split at hStep <;> simp only [Except.ok.injEq] at hStep <;> rw [← hStep] <;> rfl
          · simp at hStep

-- Turn structure: at most one energy attachment, and the turn ends with attack or endTurn.
-- Turn structure: at most one energy attachment and one supporter, items/tools unlimited.
inductive TurnActionsAux : Bool → Bool → List Action → Prop
  | endTurn (energyAttached supporterUsed : Bool) : TurnActionsAux energyAttached supporterUsed [.endTurn]
  | attack (energyAttached supporterUsed : Bool) (attackIndex : Nat) :
      TurnActionsAux energyAttached supporterUsed [.attack attackIndex]
  | playPokemon {energyAttached supporterUsed : Bool} {card : Card} {actions : List Action}
      (h : TurnActionsAux energyAttached supporterUsed actions) :
      TurnActionsAux energyAttached supporterUsed (.playPokemonToBench card :: actions)
  | playItem {energyAttached supporterUsed : Bool} {card : Card} {actions : List Action}
      (h : TurnActionsAux energyAttached supporterUsed actions) :
      TurnActionsAux energyAttached supporterUsed (.playItem card :: actions)
  | playTool {energyAttached supporterUsed : Bool} {card : Card} {actions : List Action}
      (h : TurnActionsAux energyAttached supporterUsed actions) :
      TurnActionsAux energyAttached supporterUsed (.playTool card :: actions)
  | playSupporter {energyAttached : Bool} {card : Card} {actions : List Action}
      (h : TurnActionsAux energyAttached true actions) :
      TurnActionsAux energyAttached false (.playSupporter card :: actions)
  | playSupporterDraw {energyAttached : Bool} {card : Card} {count : Nat} {actions : List Action}
      (h : TurnActionsAux energyAttached true actions) :
      TurnActionsAux energyAttached false (.playSupporterDraw card count :: actions)
  | playItemHeal {energyAttached supporterUsed : Bool} {card : Card} {amount : Nat} {actions : List Action}
      (h : TurnActionsAux energyAttached supporterUsed actions) :
      TurnActionsAux energyAttached supporterUsed (.playItemHeal card amount :: actions)
  | evolveActive {energyAttached supporterUsed : Bool} {card : Card} {actions : List Action}
      (h : TurnActionsAux energyAttached supporterUsed actions) :
      TurnActionsAux energyAttached supporterUsed (.evolveActive card :: actions)
  | useAbilityHeal {energyAttached supporterUsed : Bool} {amount : Nat} {actions : List Action}
      (h : TurnActionsAux energyAttached supporterUsed actions) :
      TurnActionsAux energyAttached supporterUsed (.useAbilityHeal amount :: actions)
  | useAbilityDraw {energyAttached supporterUsed : Bool} {count : Nat} {actions : List Action}
      (h : TurnActionsAux energyAttached supporterUsed actions) :
      TurnActionsAux energyAttached supporterUsed (.useAbilityDraw count :: actions)
  | attachEnergy {energyType : EnergyType} {supporterUsed : Bool} {actions : List Action}
      (h : TurnActionsAux true supporterUsed actions) :
      TurnActionsAux false supporterUsed (.attachEnergy energyType :: actions)
  | retreat {energyAttached supporterUsed : Bool} {actions : List Action}
      (h : TurnActionsAux energyAttached supporterUsed actions) :
      TurnActionsAux energyAttached supporterUsed (.retreat :: actions)
  | drawCard {energyAttached supporterUsed : Bool} {actions : List Action}
      (h : TurnActionsAux energyAttached supporterUsed actions) :
      TurnActionsAux energyAttached supporterUsed (.drawCard :: actions)

def TurnActions (actions : List Action) : Prop :=
  TurnActionsAux false false actions

def applyEffect (state : GameState) (effect : Effect) : GameState :=
  match effect with
  | .applyStatus condition =>
    let player := state.activePlayer
    let playerState := getPlayerState state player
    match playerState.active with
    | none => state
    | some active =>
      let updatedActive := { active with status := some condition }
      setPlayerState state player { playerState with active := some updatedActive }
  | .heal amount =>
    let player := state.activePlayer
    let playerState := getPlayerState state player
    match playerState.active with
    | none => state
    | some active =>
      let updatedActive := { active with damage := Nat.sub active.damage amount }
      setPlayerState state player { playerState with active := some updatedActive }
  | .addDamage amount =>
    let player := otherPlayer state.activePlayer
    let playerState := getPlayerState state player
    match playerState.active with
    | none => state
    | some active =>
      let updatedActive := applyDamage active amount
      setPlayerState state player { playerState with active := some updatedActive }

def runEffectStack (state : GameState) : EffectStack → GameState
  | [] => state
  | effect :: rest => runEffectStack (applyEffect state effect) rest

theorem runEffectStack_progress (state : GameState) (stack : EffectStack) :
    ∃ state', state' = runEffectStack state stack := by
  exact ⟨runEffectStack state stack, rfl⟩


theorem runEffectStack_terminates (state : GameState) (stack : EffectStack) :
    ∃ state', runEffectStack state stack = state' := by
  exact ⟨runEffectStack state stack, rfl⟩

abbrev CoinFlipStream := List Bool

abbrev GameRand := StateM CoinFlipStream

def nextFlip : GameRand Bool := do
  let stream ← get
  match stream with
  | [] => return false
  | head :: tail =>
    set tail
    return head

def runWithFlips {α : Type} (flips : CoinFlipStream) (action : GameRand α) : α :=
  (action.run flips).1

def attachEnergyCount : List Action → Nat
  | [] => 0
  | .attachEnergy _ :: rest => attachEnergyCount rest + 1
  | _ :: rest => attachEnergyCount rest

def supporterCount : List Action → Nat
  | [] => 0
  | .playSupporter _ :: rest => supporterCount rest + 1
  | .playSupporterDraw _ _ :: rest => supporterCount rest + 1
  | _ :: rest => supporterCount rest

def evolutionCount : List Action → Nat
  | [] => 0
  | .evolveActive _ :: rest => evolutionCount rest + 1
  | _ :: rest => evolutionCount rest

def EndsTurn : List Action → Prop
  | [] => False
  | [.endTurn] => True
  | [.attack _] => True
  | _ :: rest => EndsTurn rest

theorem turnActionsAux_attachEnergyCount_zero :
    ∀ {supporterUsed : Bool} {actions : List Action},
      TurnActionsAux true supporterUsed actions → attachEnergyCount actions = 0 := by
  intro supporterUsed actions h
  generalize hE : true = energyAttached at h
  induction h with
  | endTurn => rfl
  | attack => rfl
  | playPokemon _ ih => exact ih hE
  | playItem _ ih => exact ih hE
  | playTool _ ih => exact ih hE
  | playSupporter _ ih => exact ih hE
  | playSupporterDraw _ ih => exact ih hE
  | playItemHeal _ ih => exact ih hE
  | evolveActive _ ih => exact ih hE
  | useAbilityHeal _ ih => exact ih hE
  | useAbilityDraw _ ih => exact ih hE
  | @attachEnergy _ _ actions' h ih =>
    -- attachEnergy requires energyAttached = false, but we have true
    exact absurd hE.symm Bool.noConfusion
  | retreat _ ih => exact ih hE
  | drawCard _ ih => exact ih hE

-- Helper to induct on TurnActionsAux with arbitrary indices
theorem turnActionsAux_attachEnergyCount_le_one :
    ∀ {energyAttached supporterUsed : Bool} {actions : List Action},
      TurnActionsAux energyAttached supporterUsed actions →
      (if energyAttached then attachEnergyCount actions = 0 else attachEnergyCount actions ≤ 1) := by
  intro energyAttached supporterUsed actions h
  induction h with
  | endTurn => simp [attachEnergyCount]
  | attack => simp [attachEnergyCount]
  | playPokemon _ ih => exact ih
  | playItem _ ih => exact ih
  | playTool _ ih => exact ih
  | playSupporter _ ih => exact ih
  | playSupporterDraw _ ih => exact ih
  | playItemHeal _ ih => exact ih
  | evolveActive _ ih => exact ih
  | useAbilityHeal _ ih => exact ih
  | useAbilityDraw _ ih => exact ih
  | @attachEnergy energyType supporterUsed' actions' h ih =>
    simp only [Bool.false_eq_true, ↓reduceIte] at ih ⊢
    simp only [attachEnergyCount]
    have hZero := turnActionsAux_attachEnergyCount_zero h
    omega
  | retreat _ ih => exact ih
  | drawCard _ ih => exact ih

theorem turnActions_attachEnergyCount_le_one (actions : List Action) (h : TurnActions actions) :
    attachEnergyCount actions ≤ 1 := by
  unfold TurnActions at h
  have := turnActionsAux_attachEnergyCount_le_one h
  simp at this
  exact this

theorem turnActionsAux_supporterCount_zero :
    ∀ {energyAttached : Bool} {actions : List Action},
      TurnActionsAux energyAttached true actions → supporterCount actions = 0 := by
  intro energyAttached actions h
  generalize hS : true = supporterUsed at h
  induction h with
  | endTurn => rfl
  | attack => rfl
  | playPokemon _ ih => exact ih hS
  | playItem _ ih => exact ih hS
  | playTool _ ih => exact ih hS
  | @playSupporter _ card actions' h ih =>
    -- playSupporter requires supporterUsed = false, but we have true
    exact absurd hS.symm Bool.noConfusion
  | @playSupporterDraw _ card count actions' h ih =>
    exact absurd hS.symm Bool.noConfusion
  | playItemHeal _ ih => exact ih hS
  | evolveActive _ ih => exact ih hS
  | useAbilityHeal _ ih => exact ih hS
  | useAbilityDraw _ ih => exact ih hS
  | attachEnergy _ ih => exact ih hS
  | retreat _ ih => exact ih hS
  | drawCard _ ih => exact ih hS

-- Helper to induct on TurnActionsAux for supporter count
theorem turnActionsAux_supporterCount_le_one :
    ∀ {energyAttached supporterUsed : Bool} {actions : List Action},
      TurnActionsAux energyAttached supporterUsed actions →
      (if supporterUsed then supporterCount actions = 0 else supporterCount actions ≤ 1) := by
  intro energyAttached supporterUsed actions h
  induction h with
  | endTurn => simp [supporterCount]
  | attack => simp [supporterCount]
  | playPokemon _ ih => exact ih
  | playItem _ ih => exact ih
  | playTool _ ih => exact ih
  | @playSupporter energyAttached card actions' h ih =>
    simp only [Bool.false_eq_true, ↓reduceIte] at ih ⊢
    simp only [supporterCount]
    have hZero := turnActionsAux_supporterCount_zero h
    omega
  | @playSupporterDraw energyAttached card count actions' h ih =>
    simp only [Bool.false_eq_true, ↓reduceIte] at ih ⊢
    simp only [supporterCount]
    have hZero := turnActionsAux_supporterCount_zero h
    omega
  | playItemHeal _ ih => exact ih
  | evolveActive _ ih => exact ih
  | useAbilityHeal _ ih => exact ih
  | useAbilityDraw _ ih => exact ih
  | attachEnergy _ ih => exact ih
  | retreat _ ih => exact ih
  | drawCard _ ih => exact ih

theorem turnActions_supporterCount_le_one (actions : List Action) (h : TurnActions actions) :
    supporterCount actions ≤ 1 := by
  unfold TurnActions at h
  have := turnActionsAux_supporterCount_le_one h
  simp at this
  exact this

-- Helper for EndsTurn
theorem turnActionsAux_ends_turn :
    ∀ {energyAttached supporterUsed : Bool} {actions : List Action},
      TurnActionsAux energyAttached supporterUsed actions → EndsTurn actions := by
  intro energyAttached supporterUsed actions h
  induction h with
  | endTurn => simp [EndsTurn]
  | attack => simp [EndsTurn]
  | playPokemon _ ih => exact ih
  | playItem _ ih => exact ih
  | playTool _ ih => exact ih
  | playSupporter _ ih => exact ih
  | playSupporterDraw _ ih => exact ih
  | playItemHeal _ ih => exact ih
  | evolveActive _ ih => exact ih
  | useAbilityHeal _ ih => exact ih
  | useAbilityDraw _ ih => exact ih
  | attachEnergy _ ih => exact ih
  | retreat _ ih => exact ih
  | drawCard _ ih => exact ih

theorem turnActions_ends_turn (actions : List Action) (h : TurnActions actions) :
    EndsTurn actions := by
  exact turnActionsAux_ends_turn h

theorem stepMany_activePlayer_turnAux :
    ∀ {energyAttached supporterUsed actions state state'},
      TurnActionsAux energyAttached supporterUsed actions →
      stepMany state actions = .ok state' →
      state'.activePlayer = otherPlayer state.activePlayer := by
  intro energyAttached supporterUsed actions state state' hTurn hRun
  induction hTurn generalizing state state' with
  | endTurn _ _ =>
    simp only [stepMany, List.foldlM_cons, List.foldlM_nil, step] at hRun
    cases hRun
    rfl
  | attack _ _ attackIndex =>
    simp only [stepMany, List.foldlM_cons, List.foldlM_nil, step] at hRun
    cases hPlayer : state.activePlayer <;>
      simp only [hPlayer, getPlayerState, otherPlayer] at hRun
    -- Handle playerOne case
    · cases hA1 : state.playerOne.active with
      | none => simp only [hA1] at hRun; exact (nomatch hRun)
      | some a1 =>
        simp only [hA1] at hRun
        cases hA2 : state.playerTwo.active with
        | none => simp only [hA2] at hRun; exact (nomatch hRun)
        | some a2 =>
          simp only [hA2] at hRun
          cases hAtk : listGet? a1.card.attacks attackIndex with
          | none => simp only [hAtk] at hRun; exact (nomatch hRun)
          | some atk =>
            simp only [hAtk] at hRun
            split at hRun
            case isTrue =>
              split at hRun <;> (cases hRun; rfl)
            case isFalse => exact (nomatch hRun)
    -- Handle playerTwo case
    · cases hA2 : state.playerTwo.active with
      | none => simp only [hA2] at hRun; exact (nomatch hRun)
      | some a2 =>
        simp only [hA2] at hRun
        cases hA1 : state.playerOne.active with
        | none => simp only [hA1] at hRun; exact (nomatch hRun)
        | some a1 =>
          simp only [hA1] at hRun
          cases hAtk : listGet? a2.card.attacks attackIndex with
          | none => simp only [hAtk] at hRun; exact (nomatch hRun)
          | some atk =>
            simp only [hAtk] at hRun
            split at hRun
            case isTrue =>
              split at hRun <;> (cases hRun; rfl)
            case isFalse => exact (nomatch hRun)
  | playPokemon _ ih =>
    simp only [stepMany, List.foldlM_cons, bind, Except.bind] at hRun
    cases hStep : step state (.playPokemonToBench _) with
    | error e => rw [hStep] at hRun; exact (nomatch hRun)
    | ok intermediate =>
      rw [hStep] at hRun
      have hPlayer := step_activePlayer_playPokemonToBench state _ intermediate hStep
      rw [ih hRun, hPlayer]
  | playItem _ ih =>
    simp only [stepMany, List.foldlM_cons, bind, Except.bind] at hRun
    cases hStep : step state (.playItem _) with
    | error e => rw [hStep] at hRun; exact (nomatch hRun)
    | ok intermediate =>
      rw [hStep] at hRun
      have hPlayer := step_activePlayer_playItem state _ intermediate hStep
      rw [ih hRun, hPlayer]
  | playTool _ ih =>
    simp only [stepMany, List.foldlM_cons, bind, Except.bind] at hRun
    cases hStep : step state (.playTool _) with
    | error e => rw [hStep] at hRun; exact (nomatch hRun)
    | ok intermediate =>
      rw [hStep] at hRun
      have hPlayer := step_activePlayer_playTool state _ intermediate hStep
      rw [ih hRun, hPlayer]
  | playSupporter _ ih =>
    simp only [stepMany, List.foldlM_cons, bind, Except.bind] at hRun
    cases hStep : step state (.playSupporter _) with
    | error e => rw [hStep] at hRun; exact (nomatch hRun)
    | ok intermediate =>
      rw [hStep] at hRun
      have hPlayer := step_activePlayer_playSupporter state _ intermediate hStep
      rw [ih hRun, hPlayer]
  | playSupporterDraw _ ih =>
    simp only [stepMany, List.foldlM_cons, bind, Except.bind] at hRun
    cases hStep : step state (.playSupporterDraw _ _) with
    | error e => rw [hStep] at hRun; exact (nomatch hRun)
    | ok intermediate =>
      rw [hStep] at hRun
      have hPlayer := step_activePlayer_playSupporterDraw state _ _ intermediate hStep
      rw [ih hRun, hPlayer]
  | playItemHeal _ ih =>
    simp only [stepMany, List.foldlM_cons, bind, Except.bind] at hRun
    cases hStep : step state (.playItemHeal _ _) with
    | error e => rw [hStep] at hRun; exact (nomatch hRun)
    | ok intermediate =>
      rw [hStep] at hRun
      have hPlayer := step_activePlayer_playItemHeal state _ _ intermediate hStep
      rw [ih hRun, hPlayer]
  | evolveActive _ ih =>
    simp only [stepMany, List.foldlM_cons, bind, Except.bind] at hRun
    cases hStep : step state (.evolveActive _) with
    | error e => rw [hStep] at hRun; exact (nomatch hRun)
    | ok intermediate =>
      rw [hStep] at hRun
      have hPlayer := step_activePlayer_evolveActive state _ intermediate hStep
      rw [ih hRun, hPlayer]
  | useAbilityHeal _ ih =>
    simp only [stepMany, List.foldlM_cons, bind, Except.bind] at hRun
    cases hStep : step state (.useAbilityHeal _) with
    | error e => rw [hStep] at hRun; exact (nomatch hRun)
    | ok intermediate =>
      rw [hStep] at hRun
      have hPlayer := step_activePlayer_useAbilityHeal state _ intermediate hStep
      rw [ih hRun, hPlayer]
  | useAbilityDraw _ ih =>
    simp only [stepMany, List.foldlM_cons, bind, Except.bind] at hRun
    cases hStep : step state (.useAbilityDraw _) with
    | error e => rw [hStep] at hRun; exact (nomatch hRun)
    | ok intermediate =>
      rw [hStep] at hRun
      have hPlayer := step_activePlayer_useAbilityDraw state _ intermediate hStep
      rw [ih hRun, hPlayer]
  | attachEnergy _ ih =>
    simp only [stepMany, List.foldlM_cons, bind, Except.bind] at hRun
    cases hStep : step state (.attachEnergy _) with
    | error e => rw [hStep] at hRun; exact (nomatch hRun)
    | ok intermediate =>
      rw [hStep] at hRun
      have hPlayer := step_activePlayer_attachEnergy state _ intermediate hStep
      rw [ih hRun, hPlayer]
  | retreat _ ih =>
    simp only [stepMany, List.foldlM_cons, bind, Except.bind] at hRun
    cases hStep : step state .retreat with
    | error e => rw [hStep] at hRun; exact (nomatch hRun)
    | ok intermediate =>
      rw [hStep] at hRun
      have hPlayer := step_activePlayer_retreat state intermediate hStep
      rw [ih hRun, hPlayer]
  | drawCard _ ih =>
    simp only [stepMany, List.foldlM_cons, bind, Except.bind] at hRun
    cases hStep : step state .drawCard with
    | error e => rw [hStep] at hRun; exact (nomatch hRun)
    | ok intermediate =>
      rw [hStep] at hRun
      have hPlayer := step_activePlayer_drawCard state intermediate hStep
      rw [ih hRun, hPlayer]

theorem stepMany_activePlayer_turn (state state' : GameState) (actions : List Action)
    (hTurn : TurnActions actions) (hRun : stepMany state actions = .ok state') :
    state'.activePlayer = otherPlayer state.activePlayer := by
  exact stepMany_activePlayer_turnAux hTurn hRun

def Legal (state : GameState) (action : Action) : Prop :=
  ∃ nextState, step state action = .ok nextState

def activePlayerState (state : GameState) : PlayerState :=
  getPlayerState state state.activePlayer

def canPlayPokemonToBench (state : GameState) (card : Card) : Prop :=
  let playerState := activePlayerState state
  ∃ newHand, removeFirst card playerState.hand = some newHand ∧
    playerState.bench.length < benchLimit

def canPlayTrainer (state : GameState) (card : Card) : Prop :=
  let playerState := activePlayerState state
  ∃ newHand, removeFirst card playerState.hand = some newHand ∧ isTrainer card

def canPlayTrainerDraw (state : GameState) (card : Card) (drawCount : Nat) : Prop :=
  let playerState := activePlayerState state
  ∃ newHand, removeFirst card playerState.hand = some newHand ∧
    drawCount ≤ playerState.deck.length ∧ isTrainer card

def canPlayTrainerHeal (state : GameState) (card : Card) : Prop :=
  let playerState := activePlayerState state
  ∃ newHand active, removeFirst card playerState.hand = some newHand ∧
    playerState.active = some active ∧ isTrainer card

def canEvolveActive (state : GameState) (card : Card) : Prop :=
  let playerState := activePlayerState state
  ∃ newHand active, removeFirst card playerState.hand = some newHand ∧
    playerState.active = some active ∧ active.card.hp ≤ card.hp

def canUseAbilityHeal (state : GameState) : Prop :=
  let playerState := activePlayerState state
  ∃ active, playerState.active = some active

def canUseAbilityDraw (state : GameState) (count : Nat) : Prop :=
  let playerState := activePlayerState state
  count ≤ playerState.deck.length

def canAttachEnergy (state : GameState) : Prop :=
  let playerState := activePlayerState state
  ∃ active, playerState.active = some active

def canRetreat (state : GameState) : Prop :=
  let playerState := activePlayerState state
  ∃ active newActive rest,
    playerState.active = some active ∧ playerState.bench = newActive :: rest

def canDrawCard (state : GameState) : Prop :=
  let playerState := activePlayerState state
  ∃ top rest, playerState.deck = top :: rest

def canAttack (state : GameState) (attackIndex : Nat) : Prop :=
  let attackerPlayer := state.activePlayer
  let defenderPlayer := otherPlayer attackerPlayer
  let attackerState := getPlayerState state attackerPlayer
  let defenderState := getPlayerState state defenderPlayer
  ∃ attacker defender attack,
    attackerState.active = some attacker ∧
      defenderState.active = some defender ∧
      listGet? attacker.card.attacks attackIndex = some attack ∧
      hasEnergyCost attack attacker.energy = true

instance (state : GameState) (action : Action) : Decidable (Legal state action) := by
  cases h : step state action with
  | ok next =>
    exact isTrue ⟨next, h⟩
  | error err =>
    refine isFalse ?_
    intro hLegal
    rcases hLegal with ⟨next, hStep⟩
    simp [h] at hStep

theorem step_deterministic (state : GameState) (action : Action) (s1 s2 : GameState)
    (h1 : step state action = .ok s1) (h2 : step state action = .ok s2) : s1 = s2 := by
  simpa [h1] using h2

theorem legal_progress (state : GameState) (action : Action) (h : Legal state action) :
    ∃ nextState, step state action = .ok nextState := by
  exact h

theorem legal_no_error (state : GameState) (action : Action) (err : StepError)
    (h : Legal state action) : step state action ≠ .error err := by
  rcases h with ⟨nextState, hStep⟩
  simp [hStep]

theorem legal_endTurn (state : GameState) : Legal state .endTurn := by
  refine ⟨{ state with activePlayer := otherPlayer state.activePlayer }, ?_⟩
  simp [step]

theorem legal_playItem_iff (state : GameState) (card : Card) :
    Legal state (.playItem card) ↔ canPlayTrainer state card := by
  constructor
  · intro ⟨nextState, hStep⟩
    simp only [step, playTrainer] at hStep
    unfold canPlayTrainer activePlayerState
    split at hStep
    case isTrue hTrainer =>
      match hRemove : removeFirst card (getPlayerState state state.activePlayer).hand with
      | none => simp [hRemove] at hStep
      | some newHand =>
        refine ⟨newHand, hRemove, hTrainer⟩
    case isFalse => simp at hStep
  · intro ⟨newHand, hRemove, hTrainer⟩
    simp only [Legal, step, playTrainer]
    simp only [activePlayerState] at hRemove
    split
    case isTrue hT =>
      simp only [hRemove]
      exact ⟨_, rfl⟩
    case isFalse hT =>
      exact absurd hTrainer hT

theorem legal_playSupporter_iff (state : GameState) (card : Card) :
    Legal state (.playSupporter card) ↔ canPlayTrainer state card := by
  constructor
  · intro ⟨nextState, hStep⟩
    simp only [step, playTrainer] at hStep
    unfold canPlayTrainer activePlayerState
    split at hStep
    case isTrue hTrainer =>
      match hRemove : removeFirst card (getPlayerState state state.activePlayer).hand with
      | none => simp [hRemove] at hStep
      | some newHand =>
        refine ⟨newHand, hRemove, hTrainer⟩
    case isFalse => simp at hStep
  · intro ⟨newHand, hRemove, hTrainer⟩
    simp only [Legal, step, playTrainer]
    simp only [activePlayerState] at hRemove
    split
    case isTrue hT =>
      simp only [hRemove]
      exact ⟨_, rfl⟩
    case isFalse hT =>
      exact absurd hTrainer hT

theorem legal_playTool_iff (state : GameState) (card : Card) :
    Legal state (.playTool card) ↔ canPlayTrainer state card := by
  constructor
  · intro ⟨nextState, hStep⟩
    simp only [step, playTrainer] at hStep
    unfold canPlayTrainer activePlayerState
    split at hStep
    case isTrue hTrainer =>
      match hRemove : removeFirst card (getPlayerState state state.activePlayer).hand with
      | none => simp [hRemove] at hStep
      | some newHand =>
        refine ⟨newHand, hRemove, hTrainer⟩
    case isFalse => simp at hStep
  · intro ⟨newHand, hRemove, hTrainer⟩
    simp only [Legal, step, playTrainer]
    simp only [activePlayerState] at hRemove
    split
    case isTrue hT =>
      simp only [hRemove]
      exact ⟨_, rfl⟩
    case isFalse hT =>
      exact absurd hTrainer hT

theorem legal_playSupporterDraw_iff (state : GameState) (card : Card) (count : Nat) :
    Legal state (.playSupporterDraw card count) ↔ canPlayTrainerDraw state card count := by
  constructor
  · intro ⟨nextState, hStep⟩
    simp only [step, playTrainerDraw] at hStep
    unfold canPlayTrainerDraw activePlayerState
    split at hStep
    case isTrue hTrainer =>
      match hRemove : removeFirst card (getPlayerState state state.activePlayer).hand with
      | none => simp [hRemove] at hStep
      | some newHand =>
        match hDraw : drawFromDeck (getPlayerState state state.activePlayer) count with
        | none =>
          simp [hRemove, hDraw] at hStep
        | some (drawn, rest) =>
          simp only [drawFromDeck] at hDraw
          split at hDraw
          case isTrue hLen =>
            refine ⟨newHand, hRemove, hLen, hTrainer⟩
          case isFalse => simp at hDraw
    case isFalse => simp at hStep
  · intro ⟨newHand, hRemove, hLen, hTrainer⟩
    simp only [Legal, step, playTrainerDraw]
    simp only [activePlayerState] at hRemove hLen
    split
    case isTrue hT =>
      simp only [hRemove]
      simp only [drawFromDeck, hLen, ↓reduceIte]
      exact ⟨_, rfl⟩
    case isFalse hT =>
      exact absurd hTrainer hT

theorem legal_playItemHeal_iff (state : GameState) (card : Card) (amount : Nat) :
    Legal state (.playItemHeal card amount) ↔ canPlayTrainerHeal state card := by
  constructor
  · intro ⟨nextState, hStep⟩
    simp only [step, playTrainerHeal] at hStep
    unfold canPlayTrainerHeal activePlayerState
    split at hStep
    case isTrue hTrainer =>
      match hRemove : removeFirst card (getPlayerState state state.activePlayer).hand with
      | none => simp [hRemove] at hStep
      | some newHand =>
        match hActive : (getPlayerState state state.activePlayer).active with
        | none => simp [hRemove, hActive] at hStep
        | some active =>
          refine ⟨newHand, active, hRemove, hActive, hTrainer⟩
    case isFalse => simp at hStep
  · intro ⟨newHand, active, hRemove, hActive, hTrainer⟩
    simp only [Legal, step, playTrainerHeal]
    simp only [activePlayerState] at hRemove hActive
    split
    case isTrue hT =>
      simp only [hRemove, hActive]
      exact ⟨_, rfl⟩
    case isFalse hT =>
      exact absurd hTrainer hT

theorem legal_evolveActive_iff (state : GameState) (card : Card) :
    Legal state (.evolveActive card) ↔ canEvolveActive state card := by
  constructor
  · intro ⟨nextState, hStep⟩
    simp only [step] at hStep
    unfold canEvolveActive activePlayerState
    match hActive : (getPlayerState state state.activePlayer).active with
    | none => simp [hActive] at hStep
    | some active =>
      simp only [hActive] at hStep
      match hRemove : removeFirst card (getPlayerState state state.activePlayer).hand with
      | none => simp [hRemove] at hStep
      | some newHand =>
        simp only [hRemove] at hStep
        split at hStep
        case isTrue hHp =>
          refine ⟨newHand, active, hRemove, hActive, hHp⟩
        case isFalse => simp at hStep
  · intro ⟨newHand, active, hRemove, hActive, hHp⟩
    simp only [Legal, step]
    simp only [activePlayerState] at hRemove hActive
    simp only [hActive, hRemove, hHp, ↓reduceIte]
    exact ⟨_, rfl⟩

theorem legal_useAbilityHeal_iff (state : GameState) (amount : Nat) :
    Legal state (.useAbilityHeal amount) ↔ canUseAbilityHeal state := by
  constructor
  · intro ⟨nextState, hStep⟩
    simp only [step] at hStep
    unfold canUseAbilityHeal activePlayerState
    match hActive : (getPlayerState state state.activePlayer).active with
    | none => simp [hActive] at hStep
    | some active =>
      exact ⟨active, hActive⟩
  · intro ⟨active, hActive⟩
    simp only [Legal, step]
    simp only [activePlayerState] at hActive
    simp only [hActive]
    exact ⟨_, rfl⟩

theorem legal_useAbilityDraw_iff (state : GameState) (count : Nat) :
    Legal state (.useAbilityDraw count) ↔ canUseAbilityDraw state count := by
  constructor
  · intro ⟨nextState, hStep⟩
    simp only [step] at hStep
    unfold canUseAbilityDraw activePlayerState
    match hDraw : drawFromDeck (getPlayerState state state.activePlayer) count with
    | none =>
      simp [hDraw] at hStep
    | some (drawn, rest) =>
      simp only [drawFromDeck] at hDraw
      split at hDraw
      case isTrue hLen => exact hLen
      case isFalse => simp at hDraw
  · intro hLen
    unfold canUseAbilityDraw activePlayerState at hLen
    simp only [Legal, step]
    have hDraw : drawFromDeck (getPlayerState state state.activePlayer) count =
      some ((getPlayerState state state.activePlayer).deck.take count,
            (getPlayerState state state.activePlayer).deck.drop count) := by
      simp only [drawFromDeck, hLen, ↓reduceIte]
    simp only [hDraw]
    exact ⟨_, rfl⟩

theorem legal_playPokemonToBench_iff (state : GameState) (card : Card) :
    Legal state (.playPokemonToBench card) ↔ canPlayPokemonToBench state card := by
  constructor
  · intro ⟨nextState, hStep⟩
    simp only [step] at hStep
    unfold canPlayPokemonToBench activePlayerState
    match hRemove : removeFirst card (getPlayerState state state.activePlayer).hand with
    | none => simp [hRemove] at hStep
    | some newHand =>
      simp only [hRemove] at hStep
      split at hStep
      case isTrue hBench =>
        exact ⟨newHand, hRemove, hBench⟩
      case isFalse => simp at hStep
  · intro ⟨newHand, hRemove, hBench⟩
    simp only [Legal, step]
    simp only [activePlayerState] at hRemove hBench
    simp only [hRemove, hBench, ↓reduceIte]
    exact ⟨_, rfl⟩

theorem legal_attachEnergy_iff (state : GameState) (energyType : EnergyType) :
    Legal state (.attachEnergy energyType) ↔ canAttachEnergy state := by
  constructor
  · intro ⟨nextState, hStep⟩
    simp only [step] at hStep
    unfold canAttachEnergy activePlayerState
    match hActive : (getPlayerState state state.activePlayer).active with
    | none => simp [hActive] at hStep
    | some active =>
      exact ⟨active, hActive⟩
  · intro ⟨active, hActive⟩
    simp only [Legal, step]
    simp only [activePlayerState] at hActive
    simp only [hActive]
    exact ⟨_, rfl⟩

theorem legal_retreat_iff (state : GameState) :
    Legal state .retreat ↔ canRetreat state := by
  constructor
  · intro ⟨nextState, hStep⟩
    simp only [step] at hStep
    unfold canRetreat activePlayerState
    match hActive : (getPlayerState state state.activePlayer).active with
    | none => simp [hActive] at hStep
    | some active =>
      simp only [hActive] at hStep
      match hBench : (getPlayerState state state.activePlayer).bench with
      | [] => simp [hBench] at hStep
      | newActive :: rest =>
        exact ⟨active, newActive, rest, hActive, hBench⟩
  · intro ⟨active, newActive, rest, hActive, hBench⟩
    simp only [Legal, step]
    simp only [activePlayerState] at hActive hBench
    simp only [hActive, hBench]
    exact ⟨_, rfl⟩

theorem legal_drawCard_iff (state : GameState) :
    Legal state .drawCard ↔ canDrawCard state := by
  constructor
  · intro ⟨nextState, hStep⟩
    simp only [step] at hStep
    unfold canDrawCard activePlayerState
    match hDeck : (getPlayerState state state.activePlayer).deck with
    | [] => simp [hDeck] at hStep
    | top :: rest =>
      exact ⟨top, rest, hDeck⟩
  · intro ⟨top, rest, hDeck⟩
    simp only [Legal, step]
    simp only [activePlayerState] at hDeck
    simp only [hDeck]
    exact ⟨_, rfl⟩

theorem legal_attack_iff (state : GameState) (attackIndex : Nat) :
    Legal state (.attack attackIndex) ↔ canAttack state attackIndex := by
  constructor
  · intro ⟨nextState, hStep⟩
    simp only [step] at hStep
    unfold canAttack
    match hAttacker : (getPlayerState state state.activePlayer).active with
    | none => simp [hAttacker] at hStep
    | some attacker =>
      simp only [hAttacker] at hStep
      match hDefender : (getPlayerState state (otherPlayer state.activePlayer)).active with
      | none => simp [hDefender] at hStep
      | some defender =>
        simp only [hDefender] at hStep
        match hAttack : listGet? attacker.card.attacks attackIndex with
        | none => simp [hAttack] at hStep
        | some attack =>
          simp only [hAttack] at hStep
          split at hStep
          case isTrue hEnergy =>
            exact ⟨attacker, defender, attack, hAttacker, hDefender, hAttack, hEnergy⟩
          case isFalse => simp at hStep
  · intro ⟨attacker, defender, attack, hAttacker, hDefender, hAttack, hEnergy⟩
    simp only [Legal, step]
    simp only [hAttacker, hDefender, hAttack, hEnergy, ↓reduceIte]
    split <;> exact ⟨_, rfl⟩

def ValidState (state : GameState) : Prop :=
  state.playerOne.bench.length ≤ benchLimit ∧
  state.playerTwo.bench.length ≤ benchLimit ∧
  state.playerOne.prizes.length ≤ standardPrizeCount ∧
  state.playerTwo.prizes.length ≤ standardPrizeCount

def CardConservation (start state : GameState) : Prop :=
  totalCardCount state = totalCardCount start

def pokemonDamageBound (pokemon : PokemonInPlay) : Prop :=
  pokemon.damage ≤ pokemon.card.hp

def DamageBounds (state : GameState) : Prop :=
  (∀ p ∈ state.playerOne.bench, pokemonDamageBound p) ∧
    (∀ p ∈ state.playerTwo.bench, pokemonDamageBound p) ∧
    (match state.playerOne.active with | some p => pokemonDamageBound p | none => True) ∧
    (match state.playerTwo.active with | some p => pokemonDamageBound p | none => True)

def playerZones (player : PlayerState) : List Card :=
  player.deck ++
  player.hand ++
  player.bench.map (fun p => p.card) ++
  (match player.active with | some p => [p.card] | none => []) ++
  player.discard ++
  player.prizes

def NoDuplicates (xs : List Card) : Prop :=
  xs.Nodup

def ZonesDisjoint (player : PlayerState) : Prop :=
  NoDuplicates (playerZones player)

def GlobalZonesDisjoint (state : GameState) : Prop :=
  ZonesDisjoint state.playerOne ∧ ZonesDisjoint state.playerTwo

-- Note: GlobalZonesDisjoint is not universally true for all GameState values,
-- since we can construct arbitrary states. It should be treated as a precondition
-- or invariant for well-formed game states.
theorem globalZonesDisjoint_of_hyp (state : GameState) (h : GlobalZonesDisjoint state) :
    GlobalZonesDisjoint state := h

theorem pokemonDamageBound_heal (pokemon : PokemonInPlay) (amount : Nat) :
    pokemonDamageBound pokemon → pokemonDamageBound { pokemon with damage := Nat.sub pokemon.damage amount } := by
  intro hBound
  exact Nat.le_trans (Nat.sub_le _ _) hBound


def initialPlayer : PlayerState :=
  standardStartingPlayer [] [] (List.replicate standardPrizeCount samplePikachu)

def initialState : GameState :=
  { playerOne := initialPlayer, playerTwo := initialPlayer, activePlayer := .playerOne }

theorem initial_valid : ValidState initialState := by
  simp [ValidState, initialState, initialPlayer, standardStartingPlayer, benchLimit]


theorem playBench_preserves_player_cards (playerState : PlayerState) (card : Card) (newHand : List Card)
    (h : removeFirst card playerState.hand = some newHand) :
    let pokemon := toPokemonInPlay card
    let newState := { playerState with hand := newHand, bench := playerState.bench ++ [pokemon] }
    playerCardCount newState = playerCardCount playerState := by
  have hLen : newHand.length + 1 = playerState.hand.length := removeFirst_length card playerState.hand newHand h
  simp only [playerCardCount]
  rw [bench_card_count, bench_card_count]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

theorem drawCard_preserves_player_cards (playerState : PlayerState) (card : Card) (rest : List Card)
    (h : playerState.deck = card :: rest) :
    let newState := { playerState with deck := rest, hand := card :: playerState.hand }
    playerCardCount newState = playerCardCount playerState := by
  simp only [playerCardCount, h, List.length_cons]
  rw [bench_card_count]
  omega

theorem attachEnergy_preserves_player_cards (playerState : PlayerState) (active : PokemonInPlay) (energyType : EnergyType)
    (hActive : playerState.active = some active) :
    let newState := { playerState with active := some { active with energy := energyType :: active.energy } }
    playerCardCount newState = playerCardCount playerState := by
  simp [playerCardCount, bench_card_count, hActive]

theorem retreat_preserves_player_cards (playerState : PlayerState) (active newActive : PokemonInPlay)
    (rest : List PokemonInPlay) (hActive : playerState.active = some active)
    (hBench : playerState.bench = newActive :: rest) :
    let newState := { playerState with active := some newActive, bench := rest ++ [active] }
    playerCardCount newState = playerCardCount playerState := by
  simp only [playerCardCount, hActive, hBench]
  rw [bench_card_count, bench_card_count]
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem active_to_discard_preserves_player_cards (playerState : PlayerState) (pokemon : PokemonInPlay)
    (hActive : playerState.active = some pokemon) :
    playerCardCount { playerState with active := none, discard := pokemon.card :: playerState.discard } =
      playerCardCount playerState := by
  simp [playerCardCount, bench_card_count, hActive, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] <;> omega

theorem totalCardCount_setPlayerState (state : GameState) (player : PlayerId) (playerState : PlayerState)
    (hCards : playerCardCount playerState = playerCardCount (getPlayerState state player)) :
    totalCardCount (setPlayerState state player playerState) = totalCardCount state := by
  cases player <;> simp [totalCardCount, getPlayerState, setPlayerState, hCards]

theorem step_preserves_total_cards (state : GameState) (action : Action) (state' : GameState)
    (hStep : step state action = .ok state') :
    totalCardCount state' = totalCardCount state := by
  cases action with
  | endTurn =>
    simp only [step] at hStep
    cases hStep
    rfl
  | playPokemonToBench card =>
    simp only [step] at hStep
    match hRemove : removeFirst card (getPlayerState state state.activePlayer).hand with
    | none => simp [hRemove] at hStep
    | some newHand =>
      simp only [hRemove] at hStep
      split at hStep
      case isTrue hBench =>
        cases hStep
        apply totalCardCount_setPlayerState
        exact playBench_preserves_player_cards _ _ _ hRemove
      case isFalse => simp at hStep
  | playItem card | playSupporter card | playTool card =>
    simp only [step, playTrainer] at hStep
    split at hStep
    case isTrue hTrainer =>
      match hRemove : removeFirst card (getPlayerState state state.activePlayer).hand with
      | none => simp [hRemove] at hStep
      | some newHand =>
        simp only [hRemove] at hStep
        cases hStep
        apply totalCardCount_setPlayerState
        have hLen : newHand.length + 1 = (getPlayerState state state.activePlayer).hand.length :=
          removeFirst_length card _ _ hRemove
        simp only [playerCardCount, bench_card_count, List.length_cons]
        omega
    case isFalse => simp at hStep
  | playSupporterDraw card count =>
    simp only [step, playTrainerDraw] at hStep
    split at hStep
    case isTrue hTrainer =>
      match hRemove : removeFirst card (getPlayerState state state.activePlayer).hand with
      | none => simp [hRemove] at hStep
      | some newHand =>
        simp only [hRemove] at hStep
        match hDraw : drawFromDeck (getPlayerState state state.activePlayer) count with
        | none => simp [hDraw] at hStep
        | some (drawn, rest) =>
          simp only [hDraw] at hStep
          cases hStep
          apply totalCardCount_setPlayerState
          have hLen : newHand.length + 1 = (getPlayerState state state.activePlayer).hand.length :=
            removeFirst_length card _ _ hRemove
          simp only [drawFromDeck] at hDraw
          split at hDraw
          case isTrue hDeckLen =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hDraw
            obtain ⟨hDrawn, hRest⟩ := hDraw
            subst hDrawn hRest
            simp only [playerCardCount, bench_card_count]
            simp only [List.length_append, List.length_drop, List.length_take, List.length_cons,
              Nat.min_eq_left hDeckLen]
            omega
          case isFalse => simp at hDraw
    case isFalse => simp at hStep
  | playItemHeal card amount =>
    simp only [step, playTrainerHeal] at hStep
    split at hStep
    case isTrue hTrainer =>
      match hRemove : removeFirst card (getPlayerState state state.activePlayer).hand with
      | none => simp [hRemove] at hStep
      | some newHand =>
        simp only [hRemove] at hStep
        match hActive : (getPlayerState state state.activePlayer).active with
        | none => simp [hActive] at hStep
        | some active =>
          simp only [hActive] at hStep
          cases hStep
          apply totalCardCount_setPlayerState
          have hLen : newHand.length + 1 = (getPlayerState state state.activePlayer).hand.length :=
            removeFirst_length card _ _ hRemove
          simp only [playerCardCount, bench_card_count, hActive, List.length_cons]
          omega
    case isFalse => simp at hStep
  | evolveActive card =>
    simp only [step] at hStep
    match hActive : (getPlayerState state state.activePlayer).active with
    | none => simp [hActive] at hStep
    | some active =>
      simp only [hActive] at hStep
      match hRemove : removeFirst card (getPlayerState state state.activePlayer).hand with
      | none => simp [hRemove] at hStep
      | some newHand =>
        simp only [hRemove] at hStep
        split at hStep
        case isTrue hHp =>
          cases hStep
          apply totalCardCount_setPlayerState
          have hLen : newHand.length + 1 = (getPlayerState state state.activePlayer).hand.length :=
            removeFirst_length card _ _ hRemove
          -- Now with the fix: hand loses 1 (newHand), discard gains 1 (old active.card)
          -- deck + newHand.length + bench + 1 + (discard.length + 1) + prizes =
          -- deck + hand.length + bench + 1 + discard.length + prizes
          -- Using hLen: newHand.length + 1 = hand.length
          simp only [playerCardCount, bench_card_count]
          simp only [hActive, List.length_cons]
          omega
        case isFalse => simp at hStep
  | useAbilityHeal amount =>
    simp only [step] at hStep
    match hActive : (getPlayerState state state.activePlayer).active with
    | none => simp [hActive] at hStep
    | some active =>
      simp only [hActive] at hStep
      cases hStep
      apply totalCardCount_setPlayerState
      simp only [playerCardCount, bench_card_count, hActive]
  | useAbilityDraw count =>
    simp only [step] at hStep
    match hDraw : drawFromDeck (getPlayerState state state.activePlayer) count with
    | none => simp [hDraw] at hStep
    | some (drawn, rest) =>
      simp only [hDraw] at hStep
      cases hStep
      apply totalCardCount_setPlayerState
      simp only [drawFromDeck] at hDraw
      split at hDraw
      case isTrue hDeckLen =>
        -- hDraw : some (deck.take count, deck.drop count) = some (drawn, rest)
        simp only [Option.some.injEq, Prod.mk.injEq] at hDraw
        obtain ⟨hDrawn, hRest⟩ := hDraw
        subst hDrawn hRest
        simp only [playerCardCount, bench_card_count, List.length_append, List.length_drop,
          List.length_take, Nat.min_eq_left hDeckLen]
        -- The active match expressions are the same on both sides
        -- Split by active to reduce the matches
        cases hActive : (getPlayerState state state.activePlayer).active with
        | none => omega
        | some act => omega
      case isFalse => simp at hDraw
  | attachEnergy energyType =>
    simp only [step] at hStep
    match hActive : (getPlayerState state state.activePlayer).active with
    | none => simp [hActive] at hStep
    | some active =>
      simp only [hActive] at hStep
      cases hStep
      apply totalCardCount_setPlayerState
      simp only [playerCardCount, bench_card_count, hActive]
  | retreat =>
    simp only [step] at hStep
    match hActive : (getPlayerState state state.activePlayer).active with
    | none => simp [hActive] at hStep
    | some active =>
      simp only [hActive] at hStep
      match hBench : (getPlayerState state state.activePlayer).bench with
      | [] => simp [hBench] at hStep
      | newActive :: rest =>
        simp only [hBench] at hStep
        cases hStep
        apply totalCardCount_setPlayerState
        exact retreat_preserves_player_cards _ _ _ _ hActive hBench
  | drawCard =>
    simp only [step] at hStep
    match hDeck : (getPlayerState state state.activePlayer).deck with
    | [] => simp [hDeck] at hStep
    | top :: rest =>
      simp only [hDeck] at hStep
      cases hStep
      apply totalCardCount_setPlayerState
      exact drawCard_preserves_player_cards _ _ _ hDeck
  | attack attackIndex =>
    simp only [step] at hStep
    match hAttacker : (getPlayerState state state.activePlayer).active with
    | none => simp [hAttacker] at hStep
    | some attacker =>
      simp only [hAttacker] at hStep
      match hDefender : (getPlayerState state (otherPlayer state.activePlayer)).active with
      | none => simp [hDefender] at hStep
      | some defender =>
        simp only [hDefender] at hStep
        match hAttack : listGet? attacker.card.attacks attackIndex with
        | none => simp [hAttack] at hStep
        | some attack =>
          simp only [hAttack] at hStep
          split at hStep
          case isTrue hEnergy =>
            split at hStep
            case isTrue hKO =>
              cases hStep
              -- KO case: defender goes to discard, prize taken
              -- takePrize moves 1 prize from defender to attacker's hand
              -- Then defender's active (some defender) -> none, and defender.card added to discard
              -- Net: attacker.hand +1, defender.prizes -1, defender.active -1, defender.discard +1 = 0
              cases hPlayer : state.activePlayer with
              | playerOne =>
                simp only [totalCardCount, hPlayer, getPlayerState, setPlayerState, otherPlayer] at *
                have hPrize := takePrize_preserves_total_cards state.playerOne state.playerTwo
                simp only [playerCardCount, hAttacker, hDefender,
                  bench_card_count,
                  takePrize_attacker_deck_eq, takePrize_defender_deck_eq,
                  takePrize_attacker_bench_eq, takePrize_defender_bench_eq,
                  takePrize_attacker_active_eq, takePrize_defender_active_eq,
                  takePrize_attacker_discard_eq, takePrize_defender_discard_eq,
                  takePrize_defender_hand_eq, List.length_cons] at hPrize ⊢
                omega
              | playerTwo =>
                simp only [totalCardCount, hPlayer, getPlayerState, setPlayerState, otherPlayer] at *
                have hPrize := takePrize_preserves_total_cards state.playerTwo state.playerOne
                simp only [playerCardCount, hAttacker, hDefender,
                  bench_card_count,
                  takePrize_attacker_deck_eq, takePrize_defender_deck_eq,
                  takePrize_attacker_bench_eq, takePrize_defender_bench_eq,
                  takePrize_attacker_active_eq, takePrize_defender_active_eq,
                  takePrize_attacker_discard_eq, takePrize_defender_discard_eq,
                  takePrize_defender_hand_eq, List.length_cons] at hPrize ⊢
                omega
            case isFalse hNoKO =>
              cases hStep
              -- No KO case: just damage applied
              cases hPlayer : state.activePlayer with
              | playerOne =>
                simp only [totalCardCount, hPlayer, getPlayerState, setPlayerState, otherPlayer] at *
                simp only [playerCardCount, hDefender]
              | playerTwo =>
                simp only [totalCardCount, hPlayer, getPlayerState, setPlayerState, otherPlayer] at *
                simp only [playerCardCount, hDefender]
          case isFalse => simp at hStep

theorem step_prizes_nonincreasing (state : GameState) (action : Action) (state' : GameState)
    (hStep : step state action = .ok state') :
    state'.playerOne.prizes.length ≤ state.playerOne.prizes.length ∧
      state'.playerTwo.prizes.length ≤ state.playerTwo.prizes.length := by
  cases action with
  | endTurn =>
    simp only [step] at hStep
    cases hStep
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | playPokemonToBench card | playItem card | playSupporter card | playTool card
  | playSupporterDraw card _ | playItemHeal card _ | evolveActive card
  | useAbilityHeal _ | useAbilityDraw _ | attachEnergy _ | retreat | drawCard =>
    -- All these actions don't change prizes
    cases hPlayer : state.activePlayer <;>
    simp only [step, playTrainer, playTrainerDraw, playTrainerHeal, hPlayer,
      getPlayerState, setPlayerState, drawFromDeck] at hStep <;>
    (try split at hStep) <;>
    (try (cases hRemove : removeFirst _ _ <;> simp only [hRemove] at hStep)) <;>
    (try split at hStep) <;>
    (try (cases hActive : (getPlayerState state state.activePlayer).active <;> simp only [hActive] at hStep)) <;>
    (try (cases hDeck : (getPlayerState state state.activePlayer).deck <;> simp only [hDeck] at hStep)) <;>
    (try (cases hBench : (getPlayerState state state.activePlayer).bench <;> simp only [hBench] at hStep)) <;>
    (try (cases hDraw : drawFromDeck _ _ <;> simp only [hDraw] at hStep)) <;>
    (try split at hStep) <;>
    (try cases hStep) <;>
    simp only [Nat.le_refl, and_self]
  | attack attackIndex =>
    simp only [step] at hStep
    match hAttacker : (getPlayerState state state.activePlayer).active with
    | none => simp [hAttacker] at hStep
    | some attacker =>
      simp only [hAttacker] at hStep
      match hDefender : (getPlayerState state (otherPlayer state.activePlayer)).active with
      | none => simp [hDefender] at hStep
      | some defender =>
        simp only [hDefender] at hStep
        match hAttack : listGet? attacker.card.attacks attackIndex with
        | none => simp [hAttack] at hStep
        | some attack =>
          simp only [hAttack] at hStep
          split at hStep
          case isTrue hEnergy =>
            split at hStep
            case isTrue hKO =>
              cases hStep
              cases hPlayer : state.activePlayer with
              | playerOne =>
                simp only [hPlayer, getPlayerState, setPlayerState, otherPlayer] at *
                simp only [takePrize_attacker_prizes_length_eq, Nat.le_refl,
                  takePrize_prizes_length_le', and_self]
              | playerTwo =>
                simp only [hPlayer, getPlayerState, setPlayerState, otherPlayer] at *
                simp only [takePrize_attacker_prizes_length_eq, Nat.le_refl,
                  takePrize_prizes_length_le', and_self]
            case isFalse hNoKO =>
              cases hStep
              cases hPlayer : state.activePlayer with
              | playerOne =>
                simp only [hPlayer, getPlayerState, setPlayerState, otherPlayer] at *
                exact ⟨Nat.le_refl _, Nat.le_refl _⟩
              | playerTwo =>
                simp only [hPlayer, getPlayerState, setPlayerState, otherPlayer] at *
                exact ⟨Nat.le_refl _, Nat.le_refl _⟩
          case isFalse => simp at hStep

theorem step_preserves_valid (state : GameState) (action : Action) (state' : GameState)
    (hValid : ValidState state) (hStep : step state action = .ok state') :
    ValidState state' := by
  obtain ⟨hB1, hB2, hP1, hP2⟩ := hValid
  cases action with
  | endTurn =>
    simp only [step] at hStep
    cases hStep
    exact ⟨hB1, hB2, hP1, hP2⟩
  | playPokemonToBench card =>
    simp only [step] at hStep
    cases hRemove : removeFirst card (getPlayerState state state.activePlayer).hand with
    | none => simp [hRemove] at hStep
    | some newHand =>
      simp only [hRemove] at hStep
      split at hStep
      case isTrue hLen =>
        cases hStep
        cases hPlayer : state.activePlayer with
        | playerOne =>
          simp only [hPlayer, getPlayerState, setPlayerState] at *
          refine ⟨?_, hB2, hP1, hP2⟩
          simp only [List.length_append, List.length_singleton]
          omega
        | playerTwo =>
          simp only [hPlayer, getPlayerState, setPlayerState] at *
          refine ⟨hB1, ?_, hP1, hP2⟩
          simp only [List.length_append, List.length_singleton]
          omega
      case isFalse => simp at hStep
  | playItem card | playSupporter card | playTool card =>
    simp only [step, playTrainer] at hStep
    split at hStep
    case isTrue =>
      cases hRemove : removeFirst card (getPlayerState state state.activePlayer).hand with
      | none => simp [hRemove] at hStep
      | some newHand =>
        simp only [hRemove] at hStep
        cases hStep
        cases hPlayer : state.activePlayer <;>
        simp only [hPlayer, getPlayerState, setPlayerState] at * <;>
        exact ⟨hB1, hB2, hP1, hP2⟩
    case isFalse => simp at hStep
  | playSupporterDraw card count =>
    simp only [step, playTrainerDraw] at hStep
    split at hStep
    case isTrue =>
      cases hRemove : removeFirst card (getPlayerState state state.activePlayer).hand with
      | none => simp [hRemove] at hStep
      | some newHand =>
        simp only [hRemove] at hStep
        cases hDraw : drawFromDeck (getPlayerState state state.activePlayer) count with
        | none => simp [hDraw] at hStep
        | some res =>
          simp only [hDraw] at hStep
          cases hStep
          cases hPlayer : state.activePlayer <;>
          simp only [hPlayer, getPlayerState, setPlayerState] at * <;>
          exact ⟨hB1, hB2, hP1, hP2⟩
    case isFalse => simp at hStep
  | playItemHeal card amount =>
    simp only [step, playTrainerHeal] at hStep
    split at hStep
    case isTrue =>
      cases hRemove : removeFirst card (getPlayerState state state.activePlayer).hand with
      | none => simp [hRemove] at hStep
      | some newHand =>
        simp only [hRemove] at hStep
        cases hActive : (getPlayerState state state.activePlayer).active with
        | none => simp [hActive] at hStep
        | some active =>
          simp only [hActive] at hStep
          cases hStep
          cases hPlayer : state.activePlayer <;>
          simp only [hPlayer, getPlayerState, setPlayerState] at * <;>
          exact ⟨hB1, hB2, hP1, hP2⟩
    case isFalse => simp at hStep
  | evolveActive card =>
    simp only [step] at hStep
    cases hActive : (getPlayerState state state.activePlayer).active with
    | none => simp [hActive] at hStep
    | some active =>
      simp only [hActive] at hStep
      cases hRemove : removeFirst card (getPlayerState state state.activePlayer).hand with
      | none => simp [hRemove] at hStep
      | some newHand =>
        simp only [hRemove] at hStep
        split at hStep
        case isTrue =>
          cases hStep
          cases hPlayer : state.activePlayer <;>
          simp only [hPlayer, getPlayerState, setPlayerState] at * <;>
          exact ⟨hB1, hB2, hP1, hP2⟩
        case isFalse => simp at hStep
  | useAbilityHeal amount =>
    simp only [step] at hStep
    cases hActive : (getPlayerState state state.activePlayer).active with
    | none => simp [hActive] at hStep
    | some active =>
      simp only [hActive] at hStep
      cases hStep
      cases hPlayer : state.activePlayer <;>
      simp only [hPlayer, getPlayerState, setPlayerState] at * <;>
      exact ⟨hB1, hB2, hP1, hP2⟩
  | useAbilityDraw count =>
    simp only [step] at hStep
    cases hDraw : drawFromDeck (getPlayerState state state.activePlayer) count with
    | none => simp [hDraw] at hStep
    | some res =>
      simp only [hDraw] at hStep
      cases hStep
      cases hPlayer : state.activePlayer <;>
      simp only [hPlayer, getPlayerState, setPlayerState] at * <;>
      exact ⟨hB1, hB2, hP1, hP2⟩
  | attachEnergy energyType =>
    simp only [step] at hStep
    cases hActive : (getPlayerState state state.activePlayer).active with
    | none => simp [hActive] at hStep
    | some active =>
      simp only [hActive] at hStep
      cases hStep
      cases hPlayer : state.activePlayer <;>
      simp only [hPlayer, getPlayerState, setPlayerState] at * <;>
      exact ⟨hB1, hB2, hP1, hP2⟩
  | retreat =>
    simp only [step] at hStep
    cases hActive : (getPlayerState state state.activePlayer).active with
    | none => simp [hActive] at hStep
    | some active =>
      simp only [hActive] at hStep
      cases hBench : (getPlayerState state state.activePlayer).bench with
      | nil => simp [hBench] at hStep
      | cons newActive rest =>
        simp only [hBench] at hStep
        cases hStep
        cases hPlayer : state.activePlayer with
        | playerOne =>
          simp only [hPlayer, getPlayerState, setPlayerState] at *
          refine ⟨?_, hB2, hP1, hP2⟩
          simp only [List.length_append, List.length_singleton]
          simp only [hBench, List.length_cons] at hB1
          omega
        | playerTwo =>
          simp only [hPlayer, getPlayerState, setPlayerState] at *
          refine ⟨hB1, ?_, hP1, hP2⟩
          simp only [List.length_append, List.length_singleton]
          simp only [hBench, List.length_cons] at hB2
          omega
  | drawCard =>
    simp only [step] at hStep
    cases hDeck : (getPlayerState state state.activePlayer).deck with
    | nil => simp [hDeck] at hStep
    | cons top rest =>
      simp only [hDeck] at hStep
      cases hStep
      cases hPlayer : state.activePlayer <;>
      simp only [hPlayer, getPlayerState, setPlayerState] at * <;>
      exact ⟨hB1, hB2, hP1, hP2⟩
  | attack attackIndex =>
    simp only [step] at hStep
    match hAttacker : (getPlayerState state state.activePlayer).active with
    | none => simp [hAttacker] at hStep
    | some attacker =>
      simp only [hAttacker] at hStep
      match hDefender : (getPlayerState state (otherPlayer state.activePlayer)).active with
      | none => simp [hDefender] at hStep
      | some defender =>
        simp only [hDefender] at hStep
        match hAttack : listGet? attacker.card.attacks attackIndex with
        | none => simp [hAttack] at hStep
        | some attack =>
          simp only [hAttack] at hStep
          split at hStep
          case isTrue hEnergy =>
            split at hStep
            case isTrue hKO =>
              cases hStep
              cases hPlayer : state.activePlayer with
              | playerOne =>
                simp only [hPlayer, getPlayerState, setPlayerState, otherPlayer] at *
                refine ⟨?_, ?_, ?_, ?_⟩
                · simp only [takePrize_attacker_bench_eq]; exact hB1
                · simp only [takePrize_defender_bench_eq]; exact hB2
                · simp only [takePrize_attacker_prizes_length_eq]; exact hP1
                · exact Nat.le_trans (takePrize_prizes_length_le' _ _) hP2
              | playerTwo =>
                simp only [hPlayer, getPlayerState, setPlayerState, otherPlayer] at *
                refine ⟨?_, ?_, ?_, ?_⟩
                · simp only [takePrize_defender_bench_eq]; exact hB1
                · simp only [takePrize_attacker_bench_eq]; exact hB2
                · exact Nat.le_trans (takePrize_prizes_length_le' _ _) hP1
                · simp only [takePrize_attacker_prizes_length_eq]; exact hP2
            case isFalse hNoKO =>
              cases hStep
              cases hPlayer : state.activePlayer <;>
              simp only [hPlayer, getPlayerState, setPlayerState, otherPlayer] at * <;>
              exact ⟨hB1, hB2, hP1, hP2⟩
          case isFalse => simp at hStep

theorem step_preserves_hasWon (state : GameState) (action : Action) (state' : GameState) (player : PlayerId)
    (hStep : step state action = .ok state') (hWon : hasWon state player) : hasWon state' player := by
  cases player with
  | playerOne =>
    have hOppLe := (step_prizes_nonincreasing state action state' hStep).2
    have hOppZero : state.playerTwo.prizes.length = 0 := by
      simpa [hasWon, otherPlayer, getPlayerState] using hWon
    have hOppLe' : state'.playerTwo.prizes.length ≤ 0 := by
      simpa [hOppZero] using hOppLe
    have hOppZero' : state'.playerTwo.prizes.length = 0 :=
      Nat.le_antisymm hOppLe' (Nat.zero_le _)
    simp [hasWon, otherPlayer, getPlayerState, hOppZero']
  | playerTwo =>
    have hOppLe := (step_prizes_nonincreasing state action state' hStep).1
    have hOppZero : state.playerOne.prizes.length = 0 := by
      simpa [hasWon, otherPlayer, getPlayerState] using hWon
    have hOppLe' : state'.playerOne.prizes.length ≤ 0 := by
      simpa [hOppZero] using hOppLe
    have hOppZero' : state'.playerOne.prizes.length = 0 :=
      Nat.le_antisymm hOppLe' (Nat.zero_le _)
    simp [hasWon, otherPlayer, getPlayerState, hOppZero']

theorem stepMany_preserves_hasWon (state state' : GameState) (actions : List Action) (player : PlayerId)
    (hRun : stepMany state actions = .ok state') (hWon : hasWon state player) : hasWon state' player := by
  induction actions generalizing state with
  | nil =>
    simp [stepMany, List.foldlM] at hRun
    cases hRun
    exact hWon
  | cons action rest ih =>
    simp only [stepMany, List.foldlM] at hRun
    cases hStep : step state action with
    | error e =>
      simp only [hStep] at hRun
      cases hRun
    | ok mid =>
      simp only [hStep] at hRun
      have hMid := step_preserves_hasWon state action mid player hStep hWon
      exact ih mid hRun hMid

-- Reachability (minimal, for now)
inductive ReachableFrom (start : GameState) : GameState → Prop
  | initial : ReachableFrom start start
  | step {state state' : GameState} (h : ReachableFrom start state)
      (action : Action) (hLegal : Legal state action) (hStep : step state action = .ok state') :
      ReachableFrom start state'

def Reachable : GameState → Prop :=
  ReachableFrom initialState

theorem reachable_preserves_total_cards (start : GameState) :
    ∀ state, ReachableFrom start state → CardConservation start state := by
  intro state hReach
  induction hReach with
  | initial =>
    simp [CardConservation]
  | step hPrev _ _ hStep ih =>
    simpa [CardConservation] using (step_preserves_total_cards _ _ _ hStep).trans ih

theorem reachable_valid (start : GameState) (hStart : ValidState start) :
    ∀ state, ReachableFrom start state → ValidState state := by
  intro state hReach
  induction hReach with
  | initial => simpa using hStart
  | step hPrev _ hLegal hStep ih =>
    cases hLegal with
    | intro nextState hNext =>
      cases (step_deterministic _ _ _ _ hStep hNext)
      exact step_preserves_valid _ _ _ ih hStep

theorem reachable_valid_initial (state : GameState) (h : Reachable state) : ValidState state := by
  exact reachable_valid initialState initial_valid state h

theorem reachable_bench_one (state : GameState) (h : Reachable state) :
    state.playerOne.bench.length ≤ benchLimit := by
  exact (reachable_valid_initial state h).1

theorem reachable_bench_two (state : GameState) (h : Reachable state) :
    state.playerTwo.bench.length ≤ benchLimit := by
  exact (reachable_valid_initial state h).2.1

theorem reachable_prizes_one (state : GameState) (h : Reachable state) :
    state.playerOne.prizes.length ≤ standardPrizeCount := by
  exact (reachable_valid_initial state h).2.2.1

theorem reachable_prizes_two (state : GameState) (h : Reachable state) :
    state.playerTwo.prizes.length ≤ standardPrizeCount := by
  exact (reachable_valid_initial state h).2.2.2

theorem reachable_card_conservation (state : GameState) (h : Reachable state) :
    totalCardCount state = totalCardCount initialState := by
  have hCons := reachable_preserves_total_cards initialState state h
  simpa [CardConservation] using hCons

end PokemonLean.Semantics

