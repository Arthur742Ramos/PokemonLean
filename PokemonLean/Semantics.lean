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

theorem step_deterministic (state : GameState) (action : Action) (s1 s2 : GameState)
    (h1 : step state action = .ok s1) (h2 : step state action = .ok s2) : s1 = s2 := by
  simpa [h1] using h2

theorem legal_progress (state : GameState) (action : Action) (h : Legal state action) :
    ∃ nextState, step state action = .ok nextState := by
  exact h

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
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] <;> omega

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

end PokemonLean.Semantics
