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
  if card.isTrainer then
    match removeFirst card playerState.hand with
    | none => .error .cardNotInHand
    | some newHand =>
      let updatedPlayerState := { playerState with hand := newHand, discard := card :: playerState.discard }
      .ok (setPlayerState state player updatedPlayerState)
  else
    .error .cardNotInHand

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

def stepMany (state : GameState) (actions : List Action) : Except StepError GameState :=
  actions.foldlM (fun st action => step st action) state

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

theorem runEffectStack_deterministic (state : GameState) (stack : EffectStack) (s1 s2 : GameState)
    (h1 : runEffectStack state stack = s1) (h2 : runEffectStack state stack = s2) : s1 = s2 := by
  simpa [h1] using h2

theorem runEffectStack_append (state : GameState) (stack₁ stack₂ : EffectStack) :
    runEffectStack state (stack₁ ++ stack₂) =
      runEffectStack (runEffectStack state stack₁) stack₂ := by
  induction stack₁ generalizing state with
  | nil => simp [runEffectStack]
  | cons effect rest ih =>
    simp [runEffectStack, ih]

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

theorem nextFlip_consumes (flips : CoinFlipStream) :
    (nextFlip.run flips).2 = flips.drop 1 := by
  cases flips with
  | nil =>
    simp [nextFlip, GameRand, StateM.run, List.drop]
  | cons head tail =>
    simp [nextFlip, GameRand, StateM.run, List.drop]

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
    ∀ {supporterUsed actions : List Action},
      TurnActionsAux true supporterUsed actions → attachEnergyCount actions = 0 := by
  intro supporterUsed actions hActions
  induction hActions with
  | endTurn =>
    simp [attachEnergyCount]
  | attack =>
    simp [attachEnergyCount]
  | playPokemon h ih =>
    simpa [attachEnergyCount] using ih
  | playItem h ih =>
    simpa [attachEnergyCount] using ih
  | playTool h ih =>
    simpa [attachEnergyCount] using ih
  | playSupporter h ih =>
    simpa [attachEnergyCount] using ih
  | playSupporterDraw h ih =>
    simpa [attachEnergyCount] using ih
  | playItemHeal h ih =>
    simpa [attachEnergyCount] using ih
  | evolveActive h ih =>
    simpa [attachEnergyCount] using ih
  | useAbilityHeal h ih =>
    simpa [attachEnergyCount] using ih
  | useAbilityDraw h ih =>
    simpa [attachEnergyCount] using ih
  | retreat h ih =>
    simpa [attachEnergyCount] using ih
  | drawCard h ih =>
    simpa [attachEnergyCount] using ih

theorem turnActions_attachEnergyCount_le_one (actions : List Action) (h : TurnActions actions) :
    attachEnergyCount actions ≤ 1 := by
  induction h with
  | endTurn =>
    simp [attachEnergyCount]
  | attack =>
    simp [attachEnergyCount]
  | playPokemon h ih =>
    simpa [attachEnergyCount] using ih
  | playItem h ih =>
    simpa [attachEnergyCount] using ih
  | playTool h ih =>
    simpa [attachEnergyCount] using ih
  | playSupporter h ih =>
    simpa [attachEnergyCount] using ih
  | playSupporterDraw h ih =>
    simpa [attachEnergyCount] using ih
  | playItemHeal h ih =>
    simpa [attachEnergyCount] using ih
  | evolveActive h ih =>
    simpa [attachEnergyCount] using ih
  | useAbilityHeal h ih =>
    simpa [attachEnergyCount] using ih
  | useAbilityDraw h ih =>
    simpa [attachEnergyCount] using ih
  | retreat h ih =>
    simpa [attachEnergyCount] using ih
  | drawCard h ih =>
    simpa [attachEnergyCount] using ih
  | attachEnergy h =>
    have hZero := turnActionsAux_attachEnergyCount_zero (actions := _) h
    simp [attachEnergyCount, hZero]

theorem turnActionsAux_supporterCount_zero :
    ∀ {energyAttached actions : List Action},
      TurnActionsAux energyAttached true actions → supporterCount actions = 0 := by
  intro energyAttached actions hActions
  induction hActions with
  | endTurn =>
    simp [supporterCount]
  | attack =>
    simp [supporterCount]
  | playPokemon h ih =>
    simpa [supporterCount] using ih
  | playItem h ih =>
    simpa [supporterCount] using ih
  | playTool h ih =>
    simpa [supporterCount] using ih
  | playSupporterDraw h ih =>
    simpa [supporterCount] using ih
  | playItemHeal h ih =>
    simpa [supporterCount] using ih
  | evolveActive h ih =>
    simpa [supporterCount] using ih
  | useAbilityHeal h ih =>
    simpa [supporterCount] using ih
  | useAbilityDraw h ih =>
    simpa [supporterCount] using ih
  | retreat h ih =>
    simpa [supporterCount] using ih
  | drawCard h ih =>
    simpa [supporterCount] using ih
  | attachEnergy h ih =>
    simpa [supporterCount] using ih

theorem turnActions_supporterCount_le_one (actions : List Action) (h : TurnActions actions) :
    supporterCount actions ≤ 1 := by
  induction h with
  | endTurn =>
    simp [supporterCount]
  | attack =>
    simp [supporterCount]
  | playPokemon h ih =>
    simpa [supporterCount] using ih
  | playItem h ih =>
    simpa [supporterCount] using ih
  | playTool h ih =>
    simpa [supporterCount] using ih
  | retreat h ih =>
    simpa [supporterCount] using ih
  | drawCard h ih =>
    simpa [supporterCount] using ih
  | attachEnergy h ih =>
    simpa [supporterCount] using ih
  | playItemHeal h ih =>
    simpa [supporterCount] using ih
  | evolveActive h ih =>
    simpa [supporterCount] using ih
  | useAbilityHeal h ih =>
    simpa [supporterCount] using ih
  | useAbilityDraw h ih =>
    simpa [supporterCount] using ih
  | playSupporter h =>
    have hZero := turnActionsAux_supporterCount_zero (actions := _) h
    simp [supporterCount, hZero]
  | playSupporterDraw h =>
    have hZero := turnActionsAux_supporterCount_zero (actions := _) h
    simp [supporterCount, hZero]

theorem turnActions_ends_turn (actions : List Action) (h : TurnActions actions) :
    EndsTurn actions := by
  induction h with
  | endTurn =>
    simp [EndsTurn]
  | attack =>
    simp [EndsTurn]
  | playPokemon h ih =>
    simpa [EndsTurn] using ih
  | playItem h ih =>
    simpa [EndsTurn] using ih
  | playTool h ih =>
    simpa [EndsTurn] using ih
  | playSupporter h ih =>
    simpa [EndsTurn] using ih
  | playSupporterDraw h ih =>
    simpa [EndsTurn] using ih
  | retreat h ih =>
    simpa [EndsTurn] using ih
  | drawCard h ih =>
    simpa [EndsTurn] using ih
  | attachEnergy h ih =>
    simpa [EndsTurn] using ih
  | playItemHeal h ih =>
    simpa [EndsTurn] using ih
  | evolveActive h ih =>
    simpa [EndsTurn] using ih
  | useAbilityHeal h ih =>
    simpa [EndsTurn] using ih
  | useAbilityDraw h ih =>
    simpa [EndsTurn] using ih

theorem stepMany_activePlayer_turnAux :
    ∀ {energyAttached supporterUsed actions state state'},
      TurnActionsAux energyAttached supporterUsed actions →
      stepMany state actions = .ok state' →
      state'.activePlayer = otherPlayer state.activePlayer := by
  intro energyAttached supporterUsed actions state state' hTurn hRun
  induction hTurn generalizing state state' with
  | endTurn energyAttached supporterUsed =>
    simp [stepMany, List.foldlM] at hRun
    exact step_activePlayer_endTurn _ _ hRun
  | attack energyAttached supporterUsed attackIndex =>
    simp [stepMany, List.foldlM] at hRun
    exact step_activePlayer_attack _ _ _ hRun
  | playPokemon h ih =>
    rename_i card actions
    cases hStep : step state (.playPokemonToBench card) <;>
      simp [stepMany, List.foldlM, hStep] at hRun
    have hActive := step_activePlayer_playPokemonToBench state card _ hStep
    have hFinal := ih hRun
    simpa [hActive] using hFinal
  | playItem h ih =>
    rename_i card actions
    cases hStep : step state (.playItem card) <;>
      simp [stepMany, List.foldlM, hStep] at hRun
    have hActive := step_activePlayer_playItem state card _ hStep
    have hFinal := ih hRun
    simpa [hActive] using hFinal
  | playTool h ih =>
    rename_i card actions
    cases hStep : step state (.playTool card) <;>
      simp [stepMany, List.foldlM, hStep] at hRun
    have hActive := step_activePlayer_playTool state card _ hStep
    have hFinal := ih hRun
    simpa [hActive] using hFinal
  | playSupporter h ih =>
    rename_i card actions
    cases hStep : step state (.playSupporter card) <;>
      simp [stepMany, List.foldlM, hStep] at hRun
    have hActive := step_activePlayer_playSupporter state card _ hStep
    have hFinal := ih hRun
    simpa [hActive] using hFinal
  | playSupporterDraw h ih =>
    rename_i card count actions
    cases hStep : step state (.playSupporterDraw card count) <;>
      simp [stepMany, List.foldlM, hStep] at hRun
    have hActive := step_activePlayer_playSupporterDraw state card count _ hStep
    have hFinal := ih hRun
    simpa [hActive] using hFinal
  | playItemHeal h ih =>
    rename_i card amount actions
    cases hStep : step state (.playItemHeal card amount) <;>
      simp [stepMany, List.foldlM, hStep] at hRun
    have hActive := step_activePlayer_playItemHeal state card amount _ hStep
    have hFinal := ih hRun
    simpa [hActive] using hFinal
  | evolveActive h ih =>
    rename_i card actions
    cases hStep : step state (.evolveActive card) <;>
      simp [stepMany, List.foldlM, hStep] at hRun
    have hActive := step_activePlayer_evolveActive state card _ hStep
    have hFinal := ih hRun
    simpa [hActive] using hFinal
  | useAbilityHeal h ih =>
    rename_i amount actions
    cases hStep : step state (.useAbilityHeal amount) <;>
      simp [stepMany, List.foldlM, hStep] at hRun
    have hActive := step_activePlayer_useAbilityHeal state amount _ hStep
    have hFinal := ih hRun
    simpa [hActive] using hFinal
  | useAbilityDraw h ih =>
    rename_i count actions
    cases hStep : step state (.useAbilityDraw count) <;>
      simp [stepMany, List.foldlM, hStep] at hRun
    have hActive := step_activePlayer_useAbilityDraw state count _ hStep
    have hFinal := ih hRun
    simpa [hActive] using hFinal
  | attachEnergy h ih =>
    rename_i energyType actions
    cases hStep : step state (.attachEnergy energyType) <;>
      simp [stepMany, List.foldlM, hStep] at hRun
    have hActive := step_activePlayer_attachEnergy state energyType _ hStep
    have hFinal := ih hRun
    simpa [hActive] using hFinal
  | retreat h ih =>
    cases hStep : step state .retreat <;>
      simp [stepMany, List.foldlM, hStep] at hRun
    have hActive := step_activePlayer_retreat state _ hStep
    have hFinal := ih hRun
    simpa [hActive] using hFinal
  | drawCard h ih =>
    cases hStep : step state .drawCard <;>
      simp [stepMany, List.foldlM, hStep] at hRun
    have hActive := step_activePlayer_drawCard state _ hStep
    have hFinal := ih hRun
    simpa [hActive] using hFinal

theorem stepMany_activePlayer_turn (state state' : GameState) (actions : List Action)
    (hTurn : TurnActions actions) (hRun : stepMany state actions = .ok state') :
    state'.activePlayer = otherPlayer state.activePlayer := by
  exact stepMany_activePlayer_turnAux hTurn hRun

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
        match payRetreatCost active with
        | none => .error .insufficientEnergy
        | some paidActive =>
          let updatedBench := rest ++ [paidActive]
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
  ∃ newHand, removeFirst card playerState.hand = some newHand ∧ card.isTrainer

def drawFromDeck (playerState : PlayerState) (n : Nat) : Option (List Card × List Card) :=
  if h : n ≤ playerState.deck.length then
    let drawn := playerState.deck.take n
    let rest := playerState.deck.drop n
    some (drawn, rest)
  else
    none

def playTrainerDraw (state : GameState) (card : Card) (drawCount : Nat) : Except StepError GameState :=
  let player := state.activePlayer
  let playerState := getPlayerState state player
  if card.isTrainer then
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

def playTrainerHeal (state : GameState) (card : Card) (healAmount : Nat) : Except StepError GameState :=
  let player := state.activePlayer
  let playerState := getPlayerState state player
  if card.isTrainer then
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

def canPlayTrainerDraw (state : GameState) (card : Card) (drawCount : Nat) : Prop :=
  let playerState := activePlayerState state
  ∃ newHand, removeFirst card playerState.hand = some newHand ∧
    drawCount ≤ playerState.deck.length ∧ card.isTrainer

def canPlayTrainerHeal (state : GameState) (card : Card) : Prop :=
  let playerState := activePlayerState state
  ∃ newHand active, removeFirst card playerState.hand = some newHand ∧
    playerState.active = some active ∧ card.isTrainer

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
  ∃ active newActive rest paid,
    playerState.active = some active ∧
      playerState.bench = newActive :: rest ∧
      payRetreatCost active = some paid

def canDrawCard (state : GameState) : Prop :=
  let playerState := activePlayerState state
  ∃ top rest, playerState.deck = top :: rest

def deckNonempty (state : GameState) : Prop :=
  let playerState := activePlayerState state
  playerState.deck.length > 0

theorem canDrawCard_iff_deckNonempty (state : GameState) :
    canDrawCard state ↔ deckNonempty state := by
  cases hPlayer : state.activePlayer <;>
    cases hDeck : (getPlayerState state state.activePlayer).deck <;>
    simp [canDrawCard, deckNonempty, activePlayerState, getPlayerState, hPlayer, hDeck]

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
  cases hPlayer : state.activePlayer <;>
    simp [Legal, canPlayTrainer, activePlayerState, step, playTrainer, hPlayer, getPlayerState, setPlayerState]

theorem legal_playSupporter_iff (state : GameState) (card : Card) :
    Legal state (.playSupporter card) ↔ canPlayTrainer state card := by
  cases hPlayer : state.activePlayer <;>
    simp [Legal, canPlayTrainer, activePlayerState, step, playTrainer, hPlayer, getPlayerState, setPlayerState]

theorem legal_playTool_iff (state : GameState) (card : Card) :
    Legal state (.playTool card) ↔ canPlayTrainer state card := by
  cases hPlayer : state.activePlayer <;>
    simp [Legal, canPlayTrainer, activePlayerState, step, playTrainer, hPlayer, getPlayerState, setPlayerState]

theorem legal_playSupporterDraw_iff (state : GameState) (card : Card) (count : Nat) :
    Legal state (.playSupporterDraw card count) ↔ canPlayTrainerDraw state card count := by
  cases hPlayer : state.activePlayer <;>
    simp [Legal, canPlayTrainerDraw, activePlayerState, step, playTrainerDraw,
      drawFromDeck, hPlayer, getPlayerState, setPlayerState]

theorem legal_playItemHeal_iff (state : GameState) (card : Card) (amount : Nat) :
    Legal state (.playItemHeal card amount) ↔ canPlayTrainerHeal state card := by
  cases hPlayer : state.activePlayer <;>
    cases hActive : (getPlayerState state state.activePlayer).active <;>
    simp [Legal, canPlayTrainerHeal, activePlayerState, step, playTrainerHeal, hPlayer, getPlayerState, setPlayerState,
      hActive]

theorem legal_evolveActive_iff (state : GameState) (card : Card) :
    Legal state (.evolveActive card) ↔ canEvolveActive state card := by
  cases hPlayer : state.activePlayer <;>
    cases hActive : (getPlayerState state state.activePlayer).active <;>
    simp [Legal, canEvolveActive, activePlayerState, step, hPlayer, getPlayerState, setPlayerState, hActive]

theorem legal_useAbilityHeal_iff (state : GameState) (amount : Nat) :
    Legal state (.useAbilityHeal amount) ↔ canUseAbilityHeal state := by
  cases hPlayer : state.activePlayer <;>
    cases hActive : (getPlayerState state state.activePlayer).active <;>
    simp [Legal, canUseAbilityHeal, activePlayerState, step, hPlayer, getPlayerState, setPlayerState, hActive]

theorem legal_useAbilityDraw_iff (state : GameState) (count : Nat) :
    Legal state (.useAbilityDraw count) ↔ canUseAbilityDraw state count := by
  cases hPlayer : state.activePlayer <;>
    simp [Legal, canUseAbilityDraw, activePlayerState, step, drawFromDeck, hPlayer, getPlayerState, setPlayerState]

theorem legal_playPokemonToBench_iff (state : GameState) (card : Card) :
    Legal state (.playPokemonToBench card) ↔ canPlayPokemonToBench state card := by
  cases hPlayer : state.activePlayer <;>
    simp [Legal, canPlayPokemonToBench, activePlayerState, step, hPlayer, getPlayerState, setPlayerState]

theorem legal_attachEnergy_iff (state : GameState) (energyType : EnergyType) :
    Legal state (.attachEnergy energyType) ↔ canAttachEnergy state := by
  cases hPlayer : state.activePlayer <;>
    cases hActive : (getPlayerState state state.activePlayer).active <;>
    simp [Legal, canAttachEnergy, activePlayerState, step, hPlayer, getPlayerState, setPlayerState, hActive]

theorem legal_retreat_iff (state : GameState) :
    Legal state .retreat ↔ canRetreat state := by
  cases hPlayer : state.activePlayer with
  | playerOne =>
    cases hActive : state.playerOne.active with
    | none =>
      cases hBench : state.playerOne.bench <;>
      simp [Legal, canRetreat, activePlayerState, step, hPlayer, getPlayerState, setPlayerState, hActive, hBench]
    | some active =>
      cases hBench : state.playerOne.bench <;>
      cases hPay : payRetreatCost active <;>
      simp [Legal, canRetreat, activePlayerState, step, hPlayer, getPlayerState, setPlayerState, hActive, hBench, hPay]
  | playerTwo =>
    cases hActive : state.playerTwo.active with
    | none =>
      cases hBench : state.playerTwo.bench <;>
      simp [Legal, canRetreat, activePlayerState, step, hPlayer, getPlayerState, setPlayerState, hActive, hBench]
    | some active =>
      cases hBench : state.playerTwo.bench <;>
      cases hPay : payRetreatCost active <;>
      simp [Legal, canRetreat, activePlayerState, step, hPlayer, getPlayerState, setPlayerState, hActive, hBench, hPay]

theorem legal_drawCard_iff (state : GameState) :
    Legal state .drawCard ↔ canDrawCard state := by
  cases hPlayer : state.activePlayer <;>
    cases hDeck : (getPlayerState state state.activePlayer).deck <;>
    simp [Legal, canDrawCard, activePlayerState, step, hPlayer, getPlayerState, setPlayerState, hDeck]

theorem legal_attack_iff (state : GameState) (attackIndex : Nat) :
    Legal state (.attack attackIndex) ↔ canAttack state attackIndex := by
  cases hPlayer : state.activePlayer <;>
    cases hAtt : (getPlayerState state state.activePlayer).active with
    | none =>
      simp [Legal, canAttack, step, hPlayer, getPlayerState, setPlayerState, hAtt]
    | some attacker =>
      cases hDef : (getPlayerState state (otherPlayer state.activePlayer)).active with
      | none =>
        simp [Legal, canAttack, step, hPlayer, getPlayerState, setPlayerState, hAtt, hDef]
      | some defender =>
        cases hAttack : listGet? attacker.card.attacks attackIndex with
        | none =>
          simp [Legal, canAttack, step, hPlayer, getPlayerState, setPlayerState, hAtt, hDef, hAttack]
        | some attack =>
          cases hCost : hasEnergyCost attack attacker.energy <;>
            simp [Legal, canAttack, step, hPlayer, getPlayerState, setPlayerState, hAtt, hDef, hAttack, hCost]

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
      cases hStep
  · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
    by_cases hBench : state.playerTwo.bench.length < benchLimit
    · simp [hBench] at hStep
      cases hStep
      simp [setPlayerState]
    · simp [hBench] at hStep
      cases hStep

theorem step_activePlayer_playItem (state : GameState) (card : Card) (state' : GameState)
    (hStep : step state (.playItem card) = .ok state') :
    state'.activePlayer = state.activePlayer := by
  cases hPlayer : state.activePlayer <;> simp [step, playTrainer, hPlayer, getPlayerState, setPlayerState] at hStep
  · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
    cases hStep
    simp [setPlayerState]
  · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
    cases hStep
    simp [setPlayerState]

theorem step_activePlayer_playSupporter (state : GameState) (card : Card) (state' : GameState)
    (hStep : step state (.playSupporter card) = .ok state') :
    state'.activePlayer = state.activePlayer := by
  cases hPlayer : state.activePlayer <;> simp [step, playTrainer, hPlayer, getPlayerState, setPlayerState] at hStep
  · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
    cases hStep
    simp [setPlayerState]
  · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
    cases hStep
    simp [setPlayerState]

theorem step_activePlayer_playSupporterDraw (state : GameState) (card : Card) (count : Nat) (state' : GameState)
    (hStep : step state (.playSupporterDraw card count) = .ok state') :
    state'.activePlayer = state.activePlayer := by
  cases hPlayer : state.activePlayer <;>
    simp [step, playTrainerDraw, drawFromDeck, hPlayer, getPlayerState, setPlayerState] at hStep
  · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
    by_cases hCount : count ≤ state.playerOne.deck.length
    · simp [hCount] at hStep
      cases hStep
      simp [setPlayerState]
    · simp [hCount] at hStep
  · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
    by_cases hCount : count ≤ state.playerTwo.deck.length
    · simp [hCount] at hStep
      cases hStep
      simp [setPlayerState]
    · simp [hCount] at hStep

theorem step_activePlayer_playItemHeal (state : GameState) (card : Card) (amount : Nat) (state' : GameState)
    (hStep : step state (.playItemHeal card amount) = .ok state') :
    state'.activePlayer = state.activePlayer := by
  cases hPlayer : state.activePlayer <;>
    simp [step, playTrainerHeal, hPlayer, getPlayerState, setPlayerState] at hStep
  · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
    cases hActive : state.playerOne.active <;> simp [hActive] at hStep
    cases hStep
    simp [setPlayerState]
  · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
    cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
    cases hStep
    simp [setPlayerState]

theorem step_activePlayer_evolveActive (state : GameState) (card : Card) (state' : GameState)
    (hStep : step state (.evolveActive card) = .ok state') :
    state'.activePlayer = state.activePlayer := by
  cases hPlayer : state.activePlayer <;>
    simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
  · cases hActive : state.playerOne.active <;> simp [hActive] at hStep
    cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
    cases hStep
    simp [setPlayerState]
  · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
    cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
    cases hStep
    simp [setPlayerState]

theorem step_activePlayer_useAbilityHeal (state : GameState) (amount : Nat) (state' : GameState)
    (hStep : step state (.useAbilityHeal amount) = .ok state') :
    state'.activePlayer = state.activePlayer := by
  cases hPlayer : state.activePlayer <;>
    simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
  · cases hActive : state.playerOne.active <;> simp [hActive] at hStep
    cases hStep
    simp [setPlayerState]
  · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
    cases hStep
    simp [setPlayerState]

theorem step_activePlayer_useAbilityDraw (state : GameState) (count : Nat) (state' : GameState)
    (hStep : step state (.useAbilityDraw count) = .ok state') :
    state'.activePlayer = state.activePlayer := by
  cases hPlayer : state.activePlayer <;>
    simp [step, drawFromDeck, hPlayer, getPlayerState, setPlayerState] at hStep
  · by_cases hCount : count ≤ state.playerOne.deck.length
    · simp [hCount] at hStep
      cases hStep
      simp [setPlayerState]
    · simp [hCount] at hStep
  · by_cases hCount : count ≤ state.playerTwo.deck.length
    · simp [hCount] at hStep
      cases hStep
      simp [setPlayerState]
    · simp [hCount] at hStep

theorem step_activePlayer_playTool (state : GameState) (card : Card) (state' : GameState)
    (hStep : step state (.playTool card) = .ok state') :
    state'.activePlayer = state.activePlayer := by
  cases hPlayer : state.activePlayer <;> simp [step, playTrainer, hPlayer, getPlayerState, setPlayerState] at hStep
  · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
    cases hStep
    simp [setPlayerState]
  · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
    cases hStep
    simp [setPlayerState]

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
    · cases hBench : state.playerOne.bench <;> simp [hBench] at hStep
    · cases hBench : state.playerOne.bench <;> simp [hBench] at hStep
      cases hPay : payRetreatCost hActive <;> simp [hPay] at hStep
      cases hStep
      simp [setPlayerState]
  · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
    · cases hBench : state.playerTwo.bench <;> simp [hBench] at hStep
    · cases hBench : state.playerTwo.bench <;> simp [hBench] at hStep
      cases hPay : payRetreatCost hActive <;> simp [hPay] at hStep
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
  cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
  · cases hAtt : state.playerOne.active <;> simp [hAtt] at hStep
    cases hDef : state.playerTwo.active <;> simp [hDef] at hStep
    cases hAttack : listGet? hAtt.card.attacks attackIndex <;> simp [hAttack] at hStep
    cases hCost : hasEnergyCost hAttack hAtt.energy <;> simp [hCost] at hStep
    by_cases hKo :
      (applyAttackEffects (applyDamage hDef
        (calculateDamage hAttack hAtt.card.energyType hDef.card)) hAttack.effects).damage >=
        (applyAttackEffects (applyDamage hDef
          (calculateDamage hAttack hAtt.card.energyType hDef.card)) hAttack.effects).card.hp
    · simp [hKo] at hStep
      cases hStep
      rfl
    · simp [hKo] at hStep
      cases hStep
      rfl
  · cases hAtt : state.playerTwo.active <;> simp [hAtt] at hStep
    cases hDef : state.playerOne.active <;> simp [hDef] at hStep
    cases hAttack : listGet? hAtt.card.attacks attackIndex <;> simp [hAttack] at hStep
    cases hCost : hasEnergyCost hAttack hAtt.energy <;> simp [hCost] at hStep
    by_cases hKo :
      (applyAttackEffects (applyDamage hDef
        (calculateDamage hAttack hAtt.card.energyType hDef.card)) hAttack.effects).damage >=
        (applyAttackEffects (applyDamage hDef
          (calculateDamage hAttack hAtt.card.energyType hDef.card)) hAttack.effects).card.hp
    · simp [hKo] at hStep
      cases hStep
      rfl
    · simp [hKo] at hStep
      cases hStep
      rfl

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
  simp [GlobalZonesDisjoint, ZonesDisjoint, NoDuplicates, playerZones]

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
  have hLen : newHand.length + 1 = playerState.hand.length :=
    removeFirst_length card playerState.hand newHand h
  simp [playerCardCount, bench_card_count, List.length_append, List.length_cons, List.length_nil,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, hLen] <;> omega

theorem drawCard_preserves_player_cards (playerState : PlayerState) (card : Card) (rest : List Card)
    (h : playerState.deck = card :: rest) :
    let newState := { playerState with deck := rest, hand := card :: playerState.hand }
    playerCardCount newState = playerCardCount playerState := by
  simp [playerCardCount, bench_card_count, h, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] <;> omega

theorem attachEnergy_preserves_player_cards (playerState : PlayerState) (active : PokemonInPlay) (energyType : EnergyType)
    (hActive : playerState.active = some active) :
    let newState := { playerState with active := some { active with energy := energyType :: active.energy } }
    playerCardCount newState = playerCardCount playerState := by
  simp [playerCardCount, bench_card_count, hActive]

theorem retreat_preserves_player_cards (playerState : PlayerState) (active newActive : PokemonInPlay)
    (rest : List PokemonInPlay) (hActive : playerState.active = some active)
    (hBench : playerState.bench = newActive :: rest) :
    ∀ paid, payRetreatCost active = some paid →
      let newState := { playerState with active := some newActive, bench := rest ++ [paid] }
      playerCardCount newState = playerCardCount playerState := by
  intro paid hPay
  simp [playerCardCount, bench_card_count, hActive, hBench, List.length_append, List.length_cons, List.length_nil,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] <;> omega

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
    simp [step] at hStep
    cases hStep
    rfl
  | playPokemonToBench card =>
    cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      by_cases hBench : state.playerOne.bench.length < benchLimit
      · simp [hBench] at hStep
        cases hStep
        have hCards := playBench_preserves_player_cards state.playerOne card _ hRemove
        simpa using (totalCardCount_setPlayerState state .playerOne _ (by simpa [getPlayerState] using hCards))
      · simp [hBench] at hStep
        cases hStep
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      by_cases hBench : state.playerTwo.bench.length < benchLimit
      · simp [hBench] at hStep
        cases hStep
        have hCards := playBench_preserves_player_cards state.playerTwo card _ hRemove
        simpa using (totalCardCount_setPlayerState state .playerTwo _ (by simpa [getPlayerState] using hCards))
      · simp [hBench] at hStep
        cases hStep
  | attachEnergy energyType =>
    cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hActive : state.playerOne.active <;> simp [hActive] at hStep
      cases hStep
      have hCards := attachEnergy_preserves_player_cards state.playerOne _ energyType hActive
      simpa using (totalCardCount_setPlayerState state .playerOne _ (by simpa [getPlayerState] using hCards))
    · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
      cases hStep
      have hCards := attachEnergy_preserves_player_cards state.playerTwo _ energyType hActive
      simpa using (totalCardCount_setPlayerState state .playerTwo _ (by simpa [getPlayerState] using hCards))
  | playItem card =>
    cases hPlayer : state.activePlayer <;> simp [step, playTrainer, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      cases hStep
      have hCards : playerCardCount
          { state.playerOne with hand := _, discard := card :: state.playerOne.discard } =
          playerCardCount state.playerOne := by
        simp [playerCardCount]
      simpa using (totalCardCount_setPlayerState state .playerOne _ (by simpa [getPlayerState] using hCards))
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      cases hStep
      have hCards : playerCardCount
          { state.playerTwo with hand := _, discard := card :: state.playerTwo.discard } =
          playerCardCount state.playerTwo := by
        simp [playerCardCount]
      simpa using (totalCardCount_setPlayerState state .playerTwo _ (by simpa [getPlayerState] using hCards))
  | playSupporter card =>
    cases hPlayer : state.activePlayer <;> simp [step, playTrainer, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      cases hStep
      have hCards : playerCardCount
          { state.playerOne with hand := _, discard := card :: state.playerOne.discard } =
          playerCardCount state.playerOne := by
        simp [playerCardCount]
      simpa using (totalCardCount_setPlayerState state .playerOne _ (by simpa [getPlayerState] using hCards))
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      cases hStep
      have hCards : playerCardCount
          { state.playerTwo with hand := _, discard := card :: state.playerTwo.discard } =
          playerCardCount state.playerTwo := by
        simp [playerCardCount]
      simpa using (totalCardCount_setPlayerState state .playerTwo _ (by simpa [getPlayerState] using hCards))
  | playTool card =>
    cases hPlayer : state.activePlayer <;> simp [step, playTrainer, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      cases hStep
      have hCards : playerCardCount
          { state.playerOne with hand := _, discard := card :: state.playerOne.discard } =
          playerCardCount state.playerOne := by
        simp [playerCardCount]
      simpa using (totalCardCount_setPlayerState state .playerOne _ (by simpa [getPlayerState] using hCards))
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      cases hStep
      have hCards : playerCardCount
          { state.playerTwo with hand := _, discard := card :: state.playerTwo.discard } =
          playerCardCount state.playerTwo := by
        simp [playerCardCount]
      simpa using (totalCardCount_setPlayerState state .playerTwo _ (by simpa [getPlayerState] using hCards))
  | playSupporterDraw card count =>
    cases hPlayer : state.activePlayer <;>
      simp [step, playTrainerDraw, drawFromDeck, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      by_cases hCount : count ≤ state.playerOne.deck.length
      · simp [hCount] at hStep
        cases hStep
        have hCards :
            playerCardCount
              { state.playerOne with
                deck := _
                hand := _ ++ _
                discard := card :: state.playerOne.discard } =
            playerCardCount state.playerOne := by
          have hLen : (state.playerOne.deck.drop count).length + count = state.playerOne.deck.length := by
            simpa using (Nat.add_comm (state.playerOne.deck.drop count).length count)
          simp [playerCardCount, bench_card_count, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
            List.length_take, List.length_drop, hCount, hLen]
        simpa using (totalCardCount_setPlayerState state .playerOne _ (by simpa [getPlayerState] using hCards))
      · simp [hCount] at hStep
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      by_cases hCount : count ≤ state.playerTwo.deck.length
      · simp [hCount] at hStep
        cases hStep
        have hCards :
            playerCardCount
              { state.playerTwo with
                deck := _
                hand := _ ++ _
                discard := card :: state.playerTwo.discard } =
            playerCardCount state.playerTwo := by
          have hLen : (state.playerTwo.deck.drop count).length + count = state.playerTwo.deck.length := by
            simpa using (Nat.add_comm (state.playerTwo.deck.drop count).length count)
          simp [playerCardCount, bench_card_count, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
            List.length_take, List.length_drop, hCount, hLen]
        simpa using (totalCardCount_setPlayerState state .playerTwo _ (by simpa [getPlayerState] using hCards))
      · simp [hCount] at hStep
  | playItemHeal card amount =>
    cases hPlayer : state.activePlayer <;>
      simp [step, playTrainerHeal, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      cases hActive : state.playerOne.active <;> simp [hActive] at hStep
      cases hStep
      have hCards : playerCardCount
          { state.playerOne with
            hand := _
            active := some { hActive with damage := _ }
            discard := card :: state.playerOne.discard } =
          playerCardCount state.playerOne := by
        simp [playerCardCount, bench_card_count, hActive]
      simpa using (totalCardCount_setPlayerState state .playerOne _ (by simpa [getPlayerState] using hCards))
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
      cases hStep
      have hCards : playerCardCount
          { state.playerTwo with
            hand := _
            active := some { hActive with damage := _ }
            discard := card :: state.playerTwo.discard } =
          playerCardCount state.playerTwo := by
        simp [playerCardCount, bench_card_count, hActive]
      simpa using (totalCardCount_setPlayerState state .playerTwo _ (by simpa [getPlayerState] using hCards))
  | evolveActive card =>
    cases hPlayer : state.activePlayer <;>
      simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hActive : state.playerOne.active <;> simp [hActive] at hStep
      cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      by_cases hHp : hActive.card.hp ≤ card.hp
      · simp [hHp] at hStep
      cases hStep
      have hCards : playerCardCount
          { state.playerOne with hand := _, active := some { hActive with card := card } } =
          playerCardCount state.playerOne := by
        simp [playerCardCount, bench_card_count, hActive]
      simpa using (totalCardCount_setPlayerState state .playerOne _ (by simpa [getPlayerState] using hCards))
      · simp [hHp] at hStep
    · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
      cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      by_cases hHp : hActive.card.hp ≤ card.hp
      · simp [hHp] at hStep
      cases hStep
      have hCards : playerCardCount
          { state.playerTwo with hand := _, active := some { hActive with card := card } } =
          playerCardCount state.playerTwo := by
        simp [playerCardCount, bench_card_count, hActive]
      simpa using (totalCardCount_setPlayerState state .playerTwo _ (by simpa [getPlayerState] using hCards))
      · simp [hHp] at hStep
  | useAbilityHeal amount =>
    cases hPlayer : state.activePlayer <;>
      simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hActive : state.playerOne.active <;> simp [hActive] at hStep
      cases hStep
      have hCards : playerCardCount
          { state.playerOne with active := some { hActive with damage := _ } } =
          playerCardCount state.playerOne := by
        simp [playerCardCount, bench_card_count, hActive]
      simpa using (totalCardCount_setPlayerState state .playerOne _ (by simpa [getPlayerState] using hCards))
    · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
      cases hStep
      have hCards : playerCardCount
          { state.playerTwo with active := some { hActive with damage := _ } } =
          playerCardCount state.playerTwo := by
        simp [playerCardCount, bench_card_count, hActive]
      simpa using (totalCardCount_setPlayerState state .playerTwo _ (by simpa [getPlayerState] using hCards))
  | useAbilityDraw count =>
    cases hPlayer : state.activePlayer <;>
      simp [step, drawFromDeck, hPlayer, getPlayerState, setPlayerState] at hStep
    · by_cases hCount : count ≤ state.playerOne.deck.length
      · simp [hCount] at hStep
        cases hStep
        have hCards :
            playerCardCount
              { state.playerOne with
                deck := _
                hand := _ ++ _ } =
            playerCardCount state.playerOne := by
          have hLen : (state.playerOne.deck.drop count).length + count = state.playerOne.deck.length := by
            simpa using (Nat.add_comm (state.playerOne.deck.drop count).length count)
          simp [playerCardCount, bench_card_count, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
            List.length_take, List.length_drop, hCount, hLen]
        simpa using (totalCardCount_setPlayerState state .playerOne _ (by simpa [getPlayerState] using hCards))
      · simp [hCount] at hStep
    · by_cases hCount : count ≤ state.playerTwo.deck.length
      · simp [hCount] at hStep
        cases hStep
        have hCards :
            playerCardCount
              { state.playerTwo with
                deck := _
                hand := _ ++ _ } =
            playerCardCount state.playerTwo := by
          have hLen : (state.playerTwo.deck.drop count).length + count = state.playerTwo.deck.length := by
            simpa using (Nat.add_comm (state.playerTwo.deck.drop count).length count)
          simp [playerCardCount, bench_card_count, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
            List.length_take, List.length_drop, hCount, hLen]
        simpa using (totalCardCount_setPlayerState state .playerTwo _ (by simpa [getPlayerState] using hCards))
      · simp [hCount] at hStep
  | attack attackIndex =>
    cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hAtt : state.playerOne.active <;> simp [hAtt] at hStep
      cases hDef : state.playerTwo.active <;> simp [hDef] at hStep
      cases hAttack : listGet? hAtt.card.attacks attackIndex <;> simp [hAttack] at hStep
      cases hCost : hasEnergyCost hAttack hAtt.energy <;> simp [hCost] at hStep
      let damage := calculateDamage hAttack hAtt.card.energyType hDef.card
      let damagedDefender := applyDamage hDef damage
      let effectedDefender := applyAttackEffects damagedDefender hAttack.effects
      by_cases hKo : effectedDefender.damage >= effectedDefender.card.hp
      · simp [hKo] at hStep
        cases hStep
        have hDiscard :
            playerCardCount
                { (takePrize state.playerOne state.playerTwo).2 with
                  active := none, discard := hDef.card :: (takePrize state.playerOne state.playerTwo).2.discard } =
              playerCardCount (takePrize state.playerOne state.playerTwo).2 := by
          have hActive : (takePrize state.playerOne state.playerTwo).2.active = some hDef := by
            simp [takePrize, hDef]
          simpa [hActive] using
            (active_to_discard_preserves_player_cards (takePrize state.playerOne state.playerTwo).2 hDef hActive)
        have hPrize := takePrize_preserves_total_cards state.playerOne state.playerTwo
        have hTotal :
            playerCardCount (takePrize state.playerOne state.playerTwo).1 +
              playerCardCount
                  { (takePrize state.playerOne state.playerTwo).2 with
                    active := none, discard := hDef.card :: (takePrize state.playerOne state.playerTwo).2.discard } =
              playerCardCount state.playerOne + playerCardCount state.playerTwo := by
          simpa [hDiscard] using hPrize
        simp [totalCardCount, hTotal]
      · simp [hKo] at hStep
        cases hStep
        have hCards :
            playerCardCount { state.playerTwo with active := some effectedDefender } =
              playerCardCount state.playerTwo := by
          simp [playerCardCount, bench_card_count, hDef]
        simpa using (totalCardCount_setPlayerState state .playerTwo _ (by simpa [getPlayerState] using hCards))
    · cases hAtt : state.playerTwo.active <;> simp [hAtt] at hStep
      cases hDef : state.playerOne.active <;> simp [hDef] at hStep
      cases hAttack : listGet? hAtt.card.attacks attackIndex <;> simp [hAttack] at hStep
      cases hCost : hasEnergyCost hAttack hAtt.energy <;> simp [hCost] at hStep
      let damage := calculateDamage hAttack hAtt.card.energyType hDef.card
      let damagedDefender := applyDamage hDef damage
      let effectedDefender := applyAttackEffects damagedDefender hAttack.effects
      by_cases hKo : effectedDefender.damage >= effectedDefender.card.hp
      · simp [hKo] at hStep
        cases hStep
        have hDiscard :
            playerCardCount
                { (takePrize state.playerTwo state.playerOne).2 with
                  active := none, discard := hDef.card :: (takePrize state.playerTwo state.playerOne).2.discard } =
              playerCardCount (takePrize state.playerTwo state.playerOne).2 := by
          have hActive : (takePrize state.playerTwo state.playerOne).2.active = some hDef := by
            simp [takePrize, hDef]
          simpa [hActive] using
            (active_to_discard_preserves_player_cards (takePrize state.playerTwo state.playerOne).2 hDef hActive)
        have hPrize := takePrize_preserves_total_cards state.playerTwo state.playerOne
        have hTotal :
            playerCardCount (takePrize state.playerTwo state.playerOne).1 +
              playerCardCount
                  { (takePrize state.playerTwo state.playerOne).2 with
                    active := none, discard := hDef.card :: (takePrize state.playerTwo state.playerOne).2.discard } =
              playerCardCount state.playerTwo + playerCardCount state.playerOne := by
          simpa [hDiscard] using hPrize
        simp [totalCardCount, hTotal]
      · simp [hKo] at hStep
        cases hStep
        have hCards :
            playerCardCount { state.playerOne with active := some effectedDefender } =
              playerCardCount state.playerOne := by
          simp [playerCardCount, bench_card_count, hDef]
        simpa using (totalCardCount_setPlayerState state .playerOne _ (by simpa [getPlayerState] using hCards))
  | retreat =>
    cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hActive : state.playerOne.active <;> simp [hActive] at hStep
      · cases hBench : state.playerOne.bench <;> simp [hBench] at hStep
      · cases hBench : state.playerOne.bench <;> simp [hBench] at hStep
        cases hPay : payRetreatCost hActive <;> simp [hPay] at hStep
        cases hStep
        have hCards :=
          retreat_preserves_player_cards state.playerOne _ _ _ hActive hBench _ hPay
        simpa using (totalCardCount_setPlayerState state .playerOne _ (by simpa [getPlayerState] using hCards))
    · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
      · cases hBench : state.playerTwo.bench <;> simp [hBench] at hStep
      · cases hBench : state.playerTwo.bench <;> simp [hBench] at hStep
        cases hPay : payRetreatCost hActive <;> simp [hPay] at hStep
        cases hStep
        have hCards :=
          retreat_preserves_player_cards state.playerTwo _ _ _ hActive hBench _ hPay
        simpa using (totalCardCount_setPlayerState state .playerTwo _ (by simpa [getPlayerState] using hCards))
  | drawCard =>
    cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hDeck : state.playerOne.deck <;> simp [hDeck] at hStep
      cases hStep
      have hCards := drawCard_preserves_player_cards state.playerOne _ _ hDeck
      simpa using (totalCardCount_setPlayerState state .playerOne _ (by simpa [getPlayerState] using hCards))
    · cases hDeck : state.playerTwo.deck <;> simp [hDeck] at hStep
      cases hStep
      have hCards := drawCard_preserves_player_cards state.playerTwo _ _ hDeck
      simpa using (totalCardCount_setPlayerState state .playerTwo _ (by simpa [getPlayerState] using hCards))

theorem step_preserves_valid (state : GameState) (action : Action) (state' : GameState)
    (hValid : ValidState state) (hStep : step state action = .ok state') :
    ValidState state' := by
  rcases hValid with ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
  cases action with
  | endTurn =>
    simp [step] at hStep
    cases hStep
    exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
  | playPokemonToBench card =>
    cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      by_cases hBench : state.playerOne.bench.length < benchLimit
      · simp [hBench] at hStep
        cases hStep
        have hBenchOne' : (state.playerOne.bench ++ [toPokemonInPlay card]).length ≤ benchLimit := by
          have hBenchSucc : state.playerOne.bench.length + 1 ≤ benchLimit :=
            Nat.succ_le_of_lt hBench
          simpa [List.length_append, List.length_cons, List.length_nil] using hBenchSucc
        exact ⟨hBenchOne', hBenchTwo, hPrizeOne, hPrizeTwo⟩
      · simp [hBench] at hStep
        cases hStep
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      by_cases hBench : state.playerTwo.bench.length < benchLimit
      · simp [hBench] at hStep
        cases hStep
        have hBenchTwo' : (state.playerTwo.bench ++ [toPokemonInPlay card]).length ≤ benchLimit := by
          have hBenchSucc : state.playerTwo.bench.length + 1 ≤ benchLimit :=
            Nat.succ_le_of_lt hBench
          simpa [List.length_append, List.length_cons, List.length_nil] using hBenchSucc
        exact ⟨hBenchOne, hBenchTwo', hPrizeOne, hPrizeTwo⟩
      · simp [hBench] at hStep
        cases hStep
  | playItem card =>
    cases hPlayer : state.activePlayer <;> simp [step, playTrainer, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      cases hStep
      exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      cases hStep
      exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
  | playSupporter card =>
    cases hPlayer : state.activePlayer <;> simp [step, playTrainer, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      cases hStep
      exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      cases hStep
      exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
  | playTool card =>
    cases hPlayer : state.activePlayer <;> simp [step, playTrainer, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      cases hStep
      exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      cases hStep
      exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
  | playSupporterDraw card count =>
    cases hPlayer : state.activePlayer <;>
      simp [step, playTrainerDraw, drawFromDeck, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      by_cases hCount : count ≤ state.playerOne.deck.length
      · simp [hCount] at hStep
        cases hStep
        exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
      · simp [hCount] at hStep
        cases hStep
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      by_cases hCount : count ≤ state.playerTwo.deck.length
      · simp [hCount] at hStep
        cases hStep
        exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
      · simp [hCount] at hStep
        cases hStep
  | playItemHeal card amount =>
    cases hPlayer : state.activePlayer <;>
      simp [step, playTrainerHeal, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      cases hActive : state.playerOne.active <;> simp [hActive] at hStep
      cases hStep
      exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
      cases hStep
      exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
  | evolveActive card =>
    cases hPlayer : state.activePlayer <;>
      simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hActive : state.playerOne.active <;> simp [hActive] at hStep
      cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      by_cases hHp : hActive.card.hp ≤ card.hp
      · simp [hHp] at hStep
      cases hStep
      exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
      · simp [hHp] at hStep
    · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
      cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      by_cases hHp : hActive.card.hp ≤ card.hp
      · simp [hHp] at hStep
      cases hStep
      exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
      · simp [hHp] at hStep
  | useAbilityHeal amount =>
    cases hPlayer : state.activePlayer <;>
      simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hActive : state.playerOne.active <;> simp [hActive] at hStep
      cases hStep
      exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
    · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
      cases hStep
      exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
  | useAbilityDraw count =>
    cases hPlayer : state.activePlayer <;>
      simp [step, drawFromDeck, hPlayer, getPlayerState, setPlayerState] at hStep
    · by_cases hCount : count ≤ state.playerOne.deck.length
      · simp [hCount] at hStep
        cases hStep
        exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
      · simp [hCount] at hStep
        cases hStep
    · by_cases hCount : count ≤ state.playerTwo.deck.length
      · simp [hCount] at hStep
        cases hStep
        exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
      · simp [hCount] at hStep
        cases hStep
  | attachEnergy energyType =>
    cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hActive : state.playerOne.active <;> simp [hActive] at hStep
      cases hStep
      exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
    · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
      cases hStep
      exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
  | attack attackIndex =>
    cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hAtt : state.playerOne.active <;> simp [hAtt] at hStep
      cases hDef : state.playerTwo.active <;> simp [hDef] at hStep
      cases hAttack : listGet? hAtt.card.attacks attackIndex <;> simp [hAttack] at hStep
      cases hCost : hasEnergyCost hAttack hAtt.energy <;> simp [hCost] at hStep
      by_cases hKo : (applyAttackEffects (applyDamage hDef
          (calculateDamage hAttack hAtt.card.energyType hDef.card)) hAttack.effects).damage >=
          (applyAttackEffects (applyDamage hDef
            (calculateDamage hAttack hAtt.card.energyType hDef.card)) hAttack.effects).card.hp
      · simp [hKo] at hStep
        cases hStep
        have hPrizeTwo' : (takePrize state.playerOne state.playerTwo).2.prizes.length ≤ standardPrizeCount :=
          Nat.le_trans (takePrize_prizes_length_le' state.playerOne state.playerTwo) hPrizeTwo
        exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo'⟩
      · simp [hKo] at hStep
        cases hStep
        exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
    · cases hAtt : state.playerTwo.active <;> simp [hAtt] at hStep
      cases hDef : state.playerOne.active <;> simp [hDef] at hStep
      cases hAttack : listGet? hAtt.card.attacks attackIndex <;> simp [hAttack] at hStep
      cases hCost : hasEnergyCost hAttack hAtt.energy <;> simp [hCost] at hStep
      by_cases hKo : (applyAttackEffects (applyDamage hDef
          (calculateDamage hAttack hAtt.card.energyType hDef.card)) hAttack.effects).damage >=
          (applyAttackEffects (applyDamage hDef
            (calculateDamage hAttack hAtt.card.energyType hDef.card)) hAttack.effects).card.hp
      · simp [hKo] at hStep
        cases hStep
        have hPrizeOne' : (takePrize state.playerTwo state.playerOne).2.prizes.length ≤ standardPrizeCount :=
          Nat.le_trans (takePrize_prizes_length_le' state.playerTwo state.playerOne) hPrizeOne
        exact ⟨hBenchOne, hBenchTwo, hPrizeOne', hPrizeTwo⟩
      · simp [hKo] at hStep
        cases hStep
        exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
  | retreat =>
    cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hActive : state.playerOne.active <;> simp [hActive] at hStep
      · cases hBench : state.playerOne.bench <;> simp [hBench] at hStep
      · cases hBench : state.playerOne.bench <;> simp [hBench] at hStep
        cases hPay : payRetreatCost hActive <;> simp [hPay] at hStep
        cases hStep
        exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
    · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
      · cases hBench : state.playerTwo.bench <;> simp [hBench] at hStep
      · cases hBench : state.playerTwo.bench <;> simp [hBench] at hStep
        cases hPay : payRetreatCost hActive <;> simp [hPay] at hStep
        cases hStep
        exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
  | drawCard =>
    cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hDeck : state.playerOne.deck <;> simp [hDeck] at hStep
      cases hStep
      exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
    · cases hDeck : state.playerTwo.deck <;> simp [hDeck] at hStep
      cases hStep
      exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩

theorem step_prizes_nonincreasing (state : GameState) (action : Action) (state' : GameState)
    (hStep : step state action = .ok state') :
    state'.playerOne.prizes.length ≤ state.playerOne.prizes.length ∧
      state'.playerTwo.prizes.length ≤ state.playerTwo.prizes.length := by
  cases action with
  | endTurn =>
    simp [step] at hStep
    cases hStep
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | playPokemonToBench card =>
    cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      by_cases hBench : state.playerOne.bench.length < benchLimit
      · simp [hBench] at hStep
        cases hStep
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      · simp [hBench] at hStep
        cases hStep
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      by_cases hBench : state.playerTwo.bench.length < benchLimit
      · simp [hBench] at hStep
        cases hStep
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      · simp [hBench] at hStep
        cases hStep
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | playItem card =>
    cases hPlayer : state.activePlayer <;> simp [step, playTrainer, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      cases hStep
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      cases hStep
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | playSupporter card =>
    cases hPlayer : state.activePlayer <;> simp [step, playTrainer, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      cases hStep
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      cases hStep
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | playTool card =>
    cases hPlayer : state.activePlayer <;> simp [step, playTrainer, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      cases hStep
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      cases hStep
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | playSupporterDraw card count =>
    cases hPlayer : state.activePlayer <;>
      simp [step, playTrainerDraw, drawFromDeck, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      by_cases hCount : count ≤ state.playerOne.deck.length
      · simp [hCount] at hStep
        cases hStep
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      · simp [hCount] at hStep
        cases hStep
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      by_cases hCount : count ≤ state.playerTwo.deck.length
      · simp [hCount] at hStep
        cases hStep
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      · simp [hCount] at hStep
        cases hStep
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | playItemHeal card amount =>
    cases hPlayer : state.activePlayer <;>
      simp [step, playTrainerHeal, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      cases hActive : state.playerOne.active <;> simp [hActive] at hStep
      cases hStep
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
      cases hStep
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | evolveActive card =>
    cases hPlayer : state.activePlayer <;>
      simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hActive : state.playerOne.active <;> simp [hActive] at hStep
      cases hRemove : removeFirst card state.playerOne.hand <;> simp [hRemove] at hStep
      cases hStep
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
      cases hRemove : removeFirst card state.playerTwo.hand <;> simp [hRemove] at hStep
      cases hStep
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | useAbilityHeal amount =>
    cases hPlayer : state.activePlayer <;>
      simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hActive : state.playerOne.active <;> simp [hActive] at hStep
      cases hStep
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
      cases hStep
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | useAbilityDraw count =>
    cases hPlayer : state.activePlayer <;>
      simp [step, drawFromDeck, hPlayer, getPlayerState, setPlayerState] at hStep
    · by_cases hCount : count ≤ state.playerOne.deck.length
      · simp [hCount] at hStep
        cases hStep
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      · simp [hCount] at hStep
        cases hStep
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · by_cases hCount : count ≤ state.playerTwo.deck.length
      · simp [hCount] at hStep
        cases hStep
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      · simp [hCount] at hStep
        cases hStep
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | attachEnergy energyType =>
    cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hActive : state.playerOne.active <;> simp [hActive] at hStep
      cases hStep
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
      cases hStep
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | attack attackIndex =>
    cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hAtt : state.playerOne.active <;> simp [hAtt] at hStep
      cases hDef : state.playerTwo.active <;> simp [hDef] at hStep
      cases hAttack : listGet? hAtt.card.attacks attackIndex <;> simp [hAttack] at hStep
      cases hCost : hasEnergyCost hAttack hAtt.energy <;> simp [hCost] at hStep
      by_cases hKo : (applyAttackEffects (applyDamage hDef
          (calculateDamage hAttack hAtt.card.energyType hDef.card)) hAttack.effects).damage >=
          (applyAttackEffects (applyDamage hDef
            (calculateDamage hAttack hAtt.card.energyType hDef.card)) hAttack.effects).card.hp
      · simp [hKo] at hStep
        cases hStep
        have hPrize :
            (takePrize state.playerOne state.playerTwo).2.prizes.length ≤ state.playerTwo.prizes.length :=
          takePrize_prizes_length_le' state.playerOne state.playerTwo
        have hPrize' :
            (takePrize state.playerOne state.playerTwo).1.prizes.length ≤ state.playerOne.prizes.length := by
          rfl
        exact ⟨hPrize', hPrize⟩
      · simp [hKo] at hStep
        cases hStep
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · cases hAtt : state.playerTwo.active <;> simp [hAtt] at hStep
      cases hDef : state.playerOne.active <;> simp [hDef] at hStep
      cases hAttack : listGet? hAtt.card.attacks attackIndex <;> simp [hAttack] at hStep
      cases hCost : hasEnergyCost hAttack hAtt.energy <;> simp [hCost] at hStep
      by_cases hKo : (applyAttackEffects (applyDamage hDef
          (calculateDamage hAttack hAtt.card.energyType hDef.card)) hAttack.effects).damage >=
          (applyAttackEffects (applyDamage hDef
            (calculateDamage hAttack hAtt.card.energyType hDef.card)) hAttack.effects).card.hp
      · simp [hKo] at hStep
        cases hStep
        have hPrize :
            (takePrize state.playerTwo state.playerOne).2.prizes.length ≤ state.playerOne.prizes.length :=
          takePrize_prizes_length_le' state.playerTwo state.playerOne
        have hPrize' :
            (takePrize state.playerTwo state.playerOne).1.prizes.length ≤ state.playerTwo.prizes.length := by
          rfl
        exact ⟨hPrize, hPrize'⟩
      · simp [hKo] at hStep
        cases hStep
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | retreat =>
    cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hActive : state.playerOne.active <;> simp [hActive] at hStep
      · cases hBench : state.playerOne.bench <;> simp [hBench] at hStep
      · cases hBench : state.playerOne.bench <;> simp [hBench] at hStep
        cases hPay : payRetreatCost hActive <;> simp [hPay] at hStep
        cases hStep
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
      · cases hBench : state.playerTwo.bench <;> simp [hBench] at hStep
      · cases hBench : state.playerTwo.bench <;> simp [hBench] at hStep
        cases hPay : payRetreatCost hActive <;> simp [hPay] at hStep
        cases hStep
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | drawCard =>
    cases hPlayer : state.activePlayer <;> simp [step, hPlayer, getPlayerState, setPlayerState] at hStep
    · cases hDeck : state.playerOne.deck <;> simp [hDeck] at hStep
      cases hStep
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · cases hDeck : state.playerTwo.deck <;> simp [hDeck] at hStep
      cases hStep
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩

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
    simp [stepMany] at hRun
    cases hRun
    simpa using hWon
  | cons action rest ih =>
    cases hStep : step state action with
    | error err =>
      simp [stepMany, List.foldlM, hStep] at hRun
    | ok next =>
      simp [stepMany, List.foldlM, hStep] at hRun
      have hWon' := step_preserves_hasWon state action next player hStep hWon
      exact ih hRun hWon'

theorem step_total_for_legal (state : GameState) (action : Action) :
    Legal state action → ∃ nextState, step state action = .ok nextState := by
  intro hLegal
  exact hLegal

theorem step_error_implies_not_legal (state : GameState) (action : Action) (err : StepError) :
    step state action = .error err → ¬ Legal state action := by
  intro hError hLegal
  rcases hLegal with ⟨nextState, hStep⟩
  simp [hError] at hStep
  exact hStep

theorem not_legal_implies_error (state : GameState) (action : Action) :
    ¬ Legal state action → ∃ err, step state action = .error err := by
  intro hNotLegal
  cases hStep : step state action with
  | ok next =>
    have hLegal : Legal state action := ⟨next, hStep⟩
    exact (hNotLegal hLegal).elim
  | error err =>
    exact ⟨err, hStep⟩

theorem step_error_iff_not_legal (state : GameState) (action : Action) :
    (∃ err, step state action = .error err) ↔ ¬ Legal state action := by
  constructor
  · intro h
    rcases h with ⟨err, hErr⟩
    exact step_error_implies_not_legal state action err hErr
  · exact not_legal_implies_error state action

theorem step_progress_or_error (state : GameState) (action : Action) :
    (∃ nextState, step state action = .ok nextState) ∨
      (∃ err, step state action = .error err) := by
  cases hStep : step state action with
  | ok next =>
    exact Or.inl ⟨next, hStep⟩
  | error err =>
    exact Or.inr ⟨err, hStep⟩

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

theorem reachable_zones_disjoint (state : GameState) (h : Reachable state) :
    GlobalZonesDisjoint state := by
  simpa using (globalZonesDisjoint_trivial state)

end PokemonLean.Semantics

