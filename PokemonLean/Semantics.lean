import PokemonLean.Basic

namespace PokemonLean.Semantics

open PokemonLean

def benchLimit : Nat := 5

inductive Action
  | playPokemonToBench (card : Card)
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
  | noDefenderPokemon
  | invalidAttackIndex
  | insufficientEnergy
  | noBenchPokemon
  | emptyDeck
  deriving Repr, BEq, DecidableEq

-- Turn structure: at most one energy attachment, and the turn ends with attack or endTurn.
inductive TurnActionsAux : Bool → List Action → Prop
  | endTurn (energyAttached : Bool) : TurnActionsAux energyAttached [.endTurn]
  | attack (energyAttached : Bool) (attackIndex : Nat) : TurnActionsAux energyAttached [.attack attackIndex]
  | playPokemon {energyAttached : Bool} {card : Card} {actions : List Action}
      (h : TurnActionsAux energyAttached actions) :
      TurnActionsAux energyAttached (.playPokemonToBench card :: actions)
  | attachEnergy {energyType : EnergyType} {actions : List Action}
      (h : TurnActionsAux true actions) :
      TurnActionsAux false (.attachEnergy energyType :: actions)
  | retreat {energyAttached : Bool} {actions : List Action}
      (h : TurnActionsAux energyAttached actions) :
      TurnActionsAux energyAttached (.retreat :: actions)
  | drawCard {energyAttached : Bool} {actions : List Action}
      (h : TurnActionsAux energyAttached actions) :
      TurnActionsAux energyAttached (.drawCard :: actions)

def TurnActions (actions : List Action) : Prop :=
  TurnActionsAux false actions

def stepMany (state : GameState) (actions : List Action) : Except StepError GameState :=
  actions.foldlM (fun st action => step st action) state

def attachEnergyCount : List Action → Nat
  | [] => 0
  | .attachEnergy _ :: rest => attachEnergyCount rest + 1
  | _ :: rest => attachEnergyCount rest

def EndsTurn : List Action → Prop
  | [] => False
  | [.endTurn] => True
  | [.attack _] => True
  | _ :: rest => EndsTurn rest

theorem turnActionsAux_attachEnergyCount_zero :
    ∀ {actions : List Action}, TurnActionsAux true actions → attachEnergyCount actions = 0 := by
  intro actions hActions
  induction hActions with
  | endTurn =>
    simp [attachEnergyCount]
  | attack =>
    simp [attachEnergyCount]
  | playPokemon h ih =>
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
  | retreat h ih =>
    simpa [attachEnergyCount] using ih
  | drawCard h ih =>
    simpa [attachEnergyCount] using ih
  | attachEnergy h =>
    have hZero := turnActionsAux_attachEnergyCount_zero (actions := _) h
    simp [attachEnergyCount, hZero]

theorem turnActions_ends_turn (actions : List Action) (h : TurnActions actions) :
    EndsTurn actions := by
  induction h with
  | endTurn =>
    simp [EndsTurn]
  | attack =>
    simp [EndsTurn]
  | playPokemon h ih =>
    simpa [EndsTurn] using ih
  | retreat h ih =>
    simpa [EndsTurn] using ih
  | drawCard h ih =>
    simpa [EndsTurn] using ih
  | attachEnergy h ih =>
    simpa [EndsTurn] using ih

theorem stepMany_activePlayer_turnAux :
    ∀ {energyAttached actions state state'},
      TurnActionsAux energyAttached actions →
      stepMany state actions = .ok state' →
      state'.activePlayer = otherPlayer state.activePlayer := by
  intro energyAttached actions state state' hTurn hRun
  induction hTurn generalizing state state' with
  | endTurn energyAttached =>
    simp [stepMany, List.foldlM] at hRun
    exact step_activePlayer_endTurn _ _ hRun
  | attack energyAttached attackIndex =>
    simp [stepMany, List.foldlM] at hRun
    exact step_activePlayer_attack _ _ _ hRun
  | playPokemon h ih =>
    rename_i card actions
    cases hStep : step state (.playPokemonToBench card) <;>
      simp [stepMany, List.foldlM, hStep] at hRun
    have hActive := step_activePlayer_playPokemonToBench state card _ hStep
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

def Legal (state : GameState) (action : Action) : Prop :=
  ∃ nextState, step state action = .ok nextState

def activePlayerState (state : GameState) : PlayerState :=
  getPlayerState state state.activePlayer

def canPlayPokemonToBench (state : GameState) (card : Card) : Prop :=
  let playerState := activePlayerState state
  ∃ newHand, removeFirst card playerState.hand = some newHand ∧
    playerState.bench.length < benchLimit

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
  cases hPlayer : state.activePlayer <;>
    cases hActive : (getPlayerState state state.activePlayer).active <;>
    cases hBench : (getPlayerState state state.activePlayer).bench <;>
    simp [Legal, canRetreat, activePlayerState, step, hPlayer, getPlayerState, setPlayerState, hActive, hBench]

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
    let newState := { playerState with active := some newActive, bench := rest ++ [active] }
    playerCardCount newState = playerCardCount playerState := by
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
      cases hBench : state.playerOne.bench <;> simp [hBench] at hStep
      cases hStep
      have hCards :=
        retreat_preserves_player_cards state.playerOne _ _ _ hActive hBench
      simpa using (totalCardCount_setPlayerState state .playerOne _ (by simpa [getPlayerState] using hCards))
    · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
      cases hBench : state.playerTwo.bench <;> simp [hBench] at hStep
      cases hStep
      have hCards :=
        retreat_preserves_player_cards state.playerTwo _ _ _ hActive hBench
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
      cases hBench : state.playerOne.bench <;> simp [hBench] at hStep
      cases hStep
      exact ⟨hBenchOne, hBenchTwo, hPrizeOne, hPrizeTwo⟩
    · cases hActive : state.playerTwo.active <;> simp [hActive] at hStep
      cases hBench : state.playerTwo.bench <;> simp [hBench] at hStep
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

