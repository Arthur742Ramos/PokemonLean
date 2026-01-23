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
  if h : n ≤ playerState.deck.length then
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
          let updatedPlayerState := { playerState with hand := newHand, active := some evolved }
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
      simp [setPlayerState]
    · simp [hBench] at hStep
  · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
    by_cases hBench : state.playerTwo.bench.length < benchLimit
    · simp [hBench] at hStep
      cases hStep
      simp [setPlayerState]
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
  sorry

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
    simp [setPlayerState]
  · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
    cases hStep
    simp [setPlayerState]

theorem step_activePlayer_retreat (state : GameState) (state' : GameState)
    (hStep : step state .retreat = .ok state') :
    state'.activePlayer = state.activePlayer := by
  cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
  · cases hActive : state.playerOne.active <;> simp [hActive] at hStep
    cases hBench : state.playerOne.bench <;> simp [hBench] at hStep
    cases hStep
    simp [setPlayerState]
  · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
    cases hBench : state.playerTwo.bench <;> simp [hBench] at hStep
    cases hStep
    simp [setPlayerState]

theorem step_activePlayer_drawCard (state : GameState) (state' : GameState)
    (hStep : step state .drawCard = .ok state') :
    state'.activePlayer = state.activePlayer := by
  cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
  · cases hDeck : state.playerOne.deck <;> simp [hDeck] at hStep
    cases hStep
    simp [setPlayerState]
  · cases hDeck : state.playerTwo.deck <;> simp [hDeck] at hStep
    cases hStep
    simp [setPlayerState]

theorem step_activePlayer_attack (state : GameState) (attackIndex : Nat) (state' : GameState)
    (hStep : step state (.attack attackIndex) = .ok state') :
    state'.activePlayer = otherPlayer state.activePlayer := by
  sorry

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

theorem runEffectStack_empty (state : GameState) :
    runEffectStack state ([] : EffectStack) = state := by
  rfl

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
  sorry

theorem turnActions_attachEnergyCount_le_one (actions : List Action) (h : TurnActions actions) :
    attachEnergyCount actions ≤ 1 := by
  sorry

theorem turnActionsAux_supporterCount_zero :
    ∀ {energyAttached : Bool} {actions : List Action},
      TurnActionsAux energyAttached true actions → supporterCount actions = 0 := by
  sorry

theorem turnActions_supporterCount_le_one (actions : List Action) (h : TurnActions actions) :
    supporterCount actions ≤ 1 := by
  sorry

theorem turnActions_ends_turn (actions : List Action) (h : TurnActions actions) :
    EndsTurn actions := by
  sorry

theorem stepMany_activePlayer_turnAux :
    ∀ {energyAttached supporterUsed actions state state'},
      TurnActionsAux energyAttached supporterUsed actions →
      stepMany state actions = .ok state' →
      state'.activePlayer = otherPlayer state.activePlayer := by
  sorry

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
    simpa [h] using hStep

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
  sorry

theorem legal_playSupporter_iff (state : GameState) (card : Card) :
    Legal state (.playSupporter card) ↔ canPlayTrainer state card := by
  sorry

theorem legal_playTool_iff (state : GameState) (card : Card) :
    Legal state (.playTool card) ↔ canPlayTrainer state card := by
  sorry

theorem legal_playSupporterDraw_iff (state : GameState) (card : Card) (count : Nat) :
    Legal state (.playSupporterDraw card count) ↔ canPlayTrainerDraw state card count := by
  sorry

theorem legal_playItemHeal_iff (state : GameState) (card : Card) (amount : Nat) :
    Legal state (.playItemHeal card amount) ↔ canPlayTrainerHeal state card := by
  sorry

theorem legal_evolveActive_iff (state : GameState) (card : Card) :
    Legal state (.evolveActive card) ↔ canEvolveActive state card := by
  sorry

theorem legal_useAbilityHeal_iff (state : GameState) (amount : Nat) :
    Legal state (.useAbilityHeal amount) ↔ canUseAbilityHeal state := by
  sorry

theorem legal_useAbilityDraw_iff (state : GameState) (count : Nat) :
    Legal state (.useAbilityDraw count) ↔ canUseAbilityDraw state count := by
  sorry

theorem legal_playPokemonToBench_iff (state : GameState) (card : Card) :
    Legal state (.playPokemonToBench card) ↔ canPlayPokemonToBench state card := by
  sorry

theorem legal_attachEnergy_iff (state : GameState) (energyType : EnergyType) :
    Legal state (.attachEnergy energyType) ↔ canAttachEnergy state := by
  sorry

theorem legal_retreat_iff (state : GameState) :
    Legal state .retreat ↔ canRetreat state := by
  sorry

theorem legal_drawCard_iff (state : GameState) :
    Legal state .drawCard ↔ canDrawCard state := by
  sorry

theorem legal_attack_iff (state : GameState) (attackIndex : Nat) :
    Legal state (.attack attackIndex) ↔ canAttack state attackIndex := by
  sorry

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

theorem globalZonesDisjoint_trivial (state : GameState) : GlobalZonesDisjoint state := by
  sorry

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

theorem takePrize_prizes_length_le' (attacker defender : PlayerState) :
    (takePrize attacker defender).2.prizes.length ≤ defender.prizes.length := by
  cases h : defender.prizes <;> simp [takePrize, h]

theorem playBench_preserves_player_cards (playerState : PlayerState) (card : Card) (newHand : List Card)
    (h : removeFirst card playerState.hand = some newHand) :
    let pokemon := toPokemonInPlay card
    let newState := { playerState with hand := newHand, bench := playerState.bench ++ [pokemon] }
    playerCardCount newState = playerCardCount playerState := by
  sorry

theorem drawCard_preserves_player_cards (playerState : PlayerState) (card : Card) (rest : List Card)
    (h : playerState.deck = card :: rest) :
    let newState := { playerState with deck := rest, hand := card :: playerState.hand }
    playerCardCount newState = playerCardCount playerState := by
  sorry

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
  sorry

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
  sorry

theorem step_preserves_valid (state : GameState) (action : Action) (state' : GameState)
    (hValid : ValidState state) (hStep : step state action = .ok state') :
    ValidState state' := by
  sorry

theorem step_prizes_nonincreasing (state : GameState) (action : Action) (state' : GameState)
    (hStep : step state action = .ok state') :
    state'.playerOne.prizes.length ≤ state.playerOne.prizes.length ∧
      state'.playerTwo.prizes.length ≤ state.playerTwo.prizes.length := by
  sorry

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
  sorry

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

