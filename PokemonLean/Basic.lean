inductive EnergyType
  | fire
  | water
  | grass
  | lightning
  | psychic
  | fighting
  | dark
  | metal
  | fairy
  | dragon
  | colorless
  deriving Repr, BEq, DecidableEq

inductive StatusCondition
  | asleep
  | burned
  | confused
  | paralyzed
  | poisoned
  deriving Repr, BEq, DecidableEq

inductive AttackEffect
  | applyStatus (condition : StatusCondition)
  | heal (amount : Nat)
  | drawCards (count : Nat)
  | addDamage (amount : Nat)
  deriving Repr, BEq, DecidableEq

structure Attack where
  name : String
  baseDamage : Nat
  effects : List AttackEffect
  deriving Repr, BEq, DecidableEq

structure Weakness where
  energyType : EnergyType
  multiplier : Nat := 2
  deriving Repr, BEq, DecidableEq

structure Resistance where
  energyType : EnergyType
  amount : Nat := 30
  deriving Repr, BEq, DecidableEq

structure Card where
  name : String
  hp : Nat
  energyType : EnergyType
  attacks : List Attack
  weakness : Option Weakness := none
  resistance : Option Resistance := none
  deriving Repr, BEq, DecidableEq

structure PokemonInPlay where
  card : Card
  damage : Nat
  status : Option StatusCondition
  deriving Repr, BEq, DecidableEq

structure PlayerState where
  deck : List Card
  hand : List Card
  bench : List PokemonInPlay
  active : Option PokemonInPlay
  discard : List Card
  prizes : List Card
  deriving Repr, BEq, DecidableEq

inductive PlayerId
  | playerOne
  | playerTwo
  deriving Repr, BEq, DecidableEq

structure GameState where
  playerOne : PlayerState
  playerTwo : PlayerState
  activePlayer : PlayerId
  deriving Repr, BEq, DecidableEq

inductive Action
  | endTurn
  | playCard (card : Card)
  | attack (attackIndex : Nat)
  deriving Repr, BEq, DecidableEq

-- Actions allowed during a single Turn 1 for player one.
inductive TurnOneActions : List Action -> Prop
  | nil : TurnOneActions []
  | play {card : Card} {actions : List Action} (h : TurnOneActions actions) :
      TurnOneActions (Action.playCard card :: actions)
  | endTurn : TurnOneActions [Action.endTurn]

def otherPlayer : PlayerId -> PlayerId
  | .playerOne => .playerTwo
  | .playerTwo => .playerOne

def getPlayerState (state : GameState) (player : PlayerId) : PlayerState :=
  match player with
  | .playerOne => state.playerOne
  | .playerTwo => state.playerTwo

def setPlayerState (state : GameState) (player : PlayerId) (playerState : PlayerState) : GameState :=
  match player with
  | .playerOne => { state with playerOne := playerState }
  | .playerTwo => { state with playerTwo := playerState }

def removeFirst (card : Card) : List Card -> Option (List Card)
  | [] => none
  | x :: xs =>
    if x == card then
      some xs
    else
      match removeFirst card xs with
      | some rest => some (x :: rest)
      | none => none

def listGet? {α : Type} (xs : List α) (index : Nat) : Option α :=
  match xs, index with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, Nat.succ index => listGet? xs index

def toPokemonInPlay (card : Card) : PokemonInPlay :=
  { card := card, damage := 0, status := none }

def applyDamage (pokemon : PokemonInPlay) (amount : Nat) : PokemonInPlay :=
  { pokemon with damage := pokemon.damage + amount }

def statusFromEffects (effects : List AttackEffect) : Option StatusCondition :=
  effects.foldl
    (fun acc effect =>
      match acc with
      | some _ => acc
      | none =>
        match effect with
        | .applyStatus condition => some condition
        | _ => none)
    none

def applyAttackEffects (pokemon : PokemonInPlay) (effects : List AttackEffect) : PokemonInPlay :=
  match statusFromEffects effects with
  | none => pokemon
  | some condition => { pokemon with status := some condition }

def takePrize (attacker defender : PlayerState) : PlayerState × PlayerState :=
  match defender.prizes with
  | [] => (attacker, defender)
  | prize :: rest =>
    ({ attacker with hand := prize :: attacker.hand }, { defender with prizes := rest })

theorem takePrize_prizes_length_le (attacker defender : PlayerState) :
    defender.prizes.length ≤ (takePrize attacker defender).2.prizes.length + 1 := by
  cases h : defender.prizes with
  | nil => simp [takePrize, h]
  | cons prize rest => simp [takePrize, h]

theorem takePrize_prizes_length_eq (attacker defender : PlayerState) :
    defender.prizes.length = (takePrize attacker defender).2.prizes.length +
      (if defender.prizes.isEmpty then 0 else 1) := by
  cases h : defender.prizes with
  | nil => simp [takePrize, h]
  | cons prize rest => simp [takePrize, h]

theorem takePrize_hand_length_eq (attacker defender : PlayerState) :
    (takePrize attacker defender).1.hand.length = attacker.hand.length +
      (if defender.prizes.isEmpty then 0 else 1) := by
  cases h : defender.prizes with
  | nil => simp [takePrize, h]
  | cons prize rest => simp [takePrize, h]

def damageBonus (effects : List AttackEffect) : Nat :=
  effects.foldl
    (fun acc effect =>
      match effect with
      | .addDamage amount => acc + amount
      | _ => acc)
    0

def applyWeakness (damage : Nat) (attackerType : EnergyType) (weakness : Option Weakness) : Nat :=
  match weakness with
  | some w => if w.energyType == attackerType then damage * w.multiplier else damage
  | none => damage

def applyResistance (damage : Nat) (attackerType : EnergyType) (resistance : Option Resistance) : Nat :=
  match resistance with
  | some r => if r.energyType == attackerType then Nat.sub damage r.amount else damage
  | none => damage

def calculateDamage (attack : Attack) (attackerType : EnergyType) (defender : Card) : Nat :=
  let base := attack.baseDamage + damageBonus attack.effects
  let afterWeakness := applyWeakness base attackerType defender.weakness
  let afterResistance := applyResistance afterWeakness attackerType defender.resistance
  afterResistance

def applyAction (state : GameState) (action : Action) : Option GameState :=
  match action with
  | .endTurn =>
    some { state with activePlayer := otherPlayer state.activePlayer }
  | .playCard card =>
    let player := state.activePlayer
    let playerState := getPlayerState state player
    match removeFirst card playerState.hand with
    | none => none
    | some newHand =>
      let pokemon := toPokemonInPlay card
      let updatedPlayerState :=
        match playerState.active with
        | none => { playerState with hand := newHand, active := some pokemon }
        | some _ => { playerState with hand := newHand, bench := playerState.bench ++ [pokemon] }
      some (setPlayerState state player updatedPlayerState)
  | .attack attackIndex =>
    let attackerPlayer := state.activePlayer
    let defenderPlayer := otherPlayer attackerPlayer
    let attackerState := getPlayerState state attackerPlayer
    let defenderState := getPlayerState state defenderPlayer
    match attackerState.active, defenderState.active with
    | some attacker, some defender =>
      match listGet? attacker.card.attacks attackIndex with
      | none => none
      | some attack =>
        let damage := calculateDamage attack attacker.card.energyType defender.card
        let damagedDefender := applyDamage defender damage
        let effectedDefender := applyAttackEffects damagedDefender attack.effects
        if effectedDefender.damage >= effectedDefender.card.hp then
          let (updatedAttacker, updatedDefender) := takePrize attackerState defenderState
          let newDefenderState :=
            { updatedDefender with active := none, discard := defender.card :: updatedDefender.discard }
          let newState := setPlayerState state attackerPlayer updatedAttacker
          let finalState := setPlayerState newState defenderPlayer newDefenderState
          some { finalState with activePlayer := otherPlayer state.activePlayer }
        else
          let newDefenderState := { defenderState with active := some effectedDefender }
          let newState := setPlayerState state defenderPlayer newDefenderState
          some { newState with activePlayer := otherPlayer state.activePlayer }
    | _, _ => none

-- ============================================================================
-- PHASE 3: FORMAL VERIFICATION & META-SAFETY
-- ============================================================================

-- Count cards in a PokemonInPlay (always 1 card per Pokemon)
def pokemonInPlayCardCount (_pokemon : PokemonInPlay) : Nat := 1

-- Count all cards in a player's zones
def playerCardCount (player : PlayerState) : Nat :=
  player.deck.length +
  player.hand.length +
  (player.bench.map pokemonInPlayCardCount).foldl (· + ·) 0 +
  (match player.active with | some _ => 1 | none => 0) +
  player.discard.length +
  player.prizes.length

-- Total cards in game (both players)
def totalCardCount (state : GameState) : Nat :=
  playerCardCount state.playerOne + playerCardCount state.playerTwo

-- Standard deck size constant
def standardDeckSize : Nat := 60

-- A game state is valid if total cards equals 120 (60 per player)
def validCardCount (state : GameState) : Prop :=
  totalCardCount state = 2 * standardDeckSize

theorem takePrize_preserves_total_cards (attacker defender : PlayerState) :
    playerCardCount (takePrize attacker defender).1 +
      playerCardCount (takePrize attacker defender).2 =
      playerCardCount attacker + playerCardCount defender := by
  cases h : defender.prizes with
  | nil => simp [takePrize, h, playerCardCount]
  | cons prize rest =>
    simp [takePrize, h, playerCardCount, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

-- Win condition: opponent has no prizes left (took all 6)
def hasWon (state : GameState) (player : PlayerId) : Prop :=
  let opponent := otherPlayer player
  let opponentState := getPlayerState state opponent
  opponentState.prizes.length = 0

-- A standard starting state for a player
def standardStartingPlayer (deck : List Card) (hand : List Card) (prizes : List Card) : PlayerState :=
  { deck := deck
  , hand := hand
  , bench := []
  , active := none
  , discard := []
  , prizes := prizes }

-- ============================================================================
-- CONSERVATION OF CARDS THEOREM
-- ============================================================================

-- Helper: endTurn preserves card count
theorem endTurn_preserves_cards (state : GameState) :
    totalCardCount { state with activePlayer := otherPlayer state.activePlayer } = totalCardCount state := by
  rfl

-- Lemma: removeFirst reduces list length by 1
theorem removeFirst_length (card : Card) (xs : List Card) (ys : List Card)
    (h : removeFirst card xs = some ys) : ys.length + 1 = xs.length := by
  induction xs generalizing ys with
  | nil => simp [removeFirst] at h
  | cons x xs ih =>
    simp only [removeFirst] at h
    split at h
    · -- card == x, so ys = xs
      simp at h
      simp [← h]
    · -- card ≠ x, recursive case
      cases hRec : removeFirst card xs with
      | none => simp [hRec] at h
      | some rest =>
        simp [hRec] at h
        subst h
        simp [ih rest hRec]

-- Helper: foldl addition with init n equals n + foldl with init 0
theorem foldl_add_shift (xs : List Nat) (n : Nat) :
    xs.foldl (· + ·) n = n + xs.foldl (· + ·) 0 := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl, Nat.zero_add]
    rw [ih (n + x), ih x]
    exact Nat.add_assoc n x _

-- Helper: bench card count is just the length (since each pokemon counts as 1)
theorem bench_card_count (bench : List PokemonInPlay) :
    (bench.map pokemonInPlayCardCount).foldl (· + ·) 0 = bench.length := by
  induction bench with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map, pokemonInPlayCardCount, List.foldl, List.length_cons]
    rw [foldl_add_shift]
    omega

-- Helper: playing a card preserves total card count (card moves from hand to board)
theorem playCard_preserves_player_cards (playerState : PlayerState) (card : Card) (newHand : List Card)
    (h : removeFirst card playerState.hand = some newHand) :
    let pokemon := toPokemonInPlay card
    let newState := match playerState.active with
      | none => { playerState with hand := newHand, active := some pokemon }
      | some _ => { playerState with hand := newHand, bench := playerState.bench ++ [pokemon] }
    playerCardCount newState = playerCardCount playerState := by
  have hLen : newHand.length + 1 = playerState.hand.length := removeFirst_length card playerState.hand newHand h
  cases hActive : playerState.active with
  | none =>
    simp only [playerCardCount, hActive]
    rw [bench_card_count]
    omega
  | some _ =>
    simp only [playerCardCount, hActive]
    rw [bench_card_count, bench_card_count]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem applyAction_endTurn_preserves_total_cards (state : GameState) (finalState : GameState)
    (h : applyAction state .endTurn = some finalState) :
    totalCardCount finalState = totalCardCount state := by
  simp [applyAction] at h
  cases h
  simpa using (endTurn_preserves_cards state)

theorem applyAction_playCard_preserves_total_cards (state : GameState) (card : Card) (finalState : GameState)
    (h : applyAction state (.playCard card) = some finalState) :
    totalCardCount finalState = totalCardCount state := by
  cases hPlayer : state.activePlayer with
  | playerOne =>
    simp [applyAction, hPlayer, getPlayerState, setPlayerState] at h
    cases hRemove : removeFirst card state.playerOne.hand with
    | none =>
      simp [hRemove] at h
    | some newHand =>
      simp [hRemove] at h
      cases h
      have hCards :
          playerCardCount
              (match state.playerOne.active with
              | none => { state.playerOne with hand := newHand, active := some (toPokemonInPlay card) }
              | some _ => { state.playerOne with hand := newHand, bench := state.playerOne.bench ++ [toPokemonInPlay card] }) =
            playerCardCount state.playerOne := by
        simpa using (playCard_preserves_player_cards state.playerOne card newHand hRemove)
      simp [totalCardCount, hCards]
  | playerTwo =>
    simp [applyAction, hPlayer, getPlayerState, setPlayerState] at h
    cases hRemove : removeFirst card state.playerTwo.hand with
    | none =>
      simp [hRemove] at h
    | some newHand =>
      simp [hRemove] at h
      cases h
      have hCards :
          playerCardCount
              (match state.playerTwo.active with
              | none => { state.playerTwo with hand := newHand, active := some (toPokemonInPlay card) }
              | some _ => { state.playerTwo with hand := newHand, bench := state.playerTwo.bench ++ [toPokemonInPlay card] }) =
            playerCardCount state.playerTwo := by
        simpa using (playCard_preserves_player_cards state.playerTwo card newHand hRemove)
      simp [totalCardCount, hCards]

theorem turn_one_cards_preserved (state : GameState) (actions : List Action)
    (hActions : TurnOneActions actions) :
    ∀ finalState : GameState,
      (actions.foldlM applyAction state = some finalState) →
      totalCardCount finalState = totalCardCount state := by
  induction hActions generalizing state with
  | nil =>
    intro finalState hFold
    simp [List.foldlM] at hFold
    cases hFold
    rfl
  | play hRest ih =>
    rename_i card rest
    intro finalState hFold
    cases hAct : applyAction state (.playCard card) with
    | none =>
      simp [List.foldlM, hAct] at hFold
    | some state' =>
      have hFold' : rest.foldlM applyAction state' = some finalState := by
        simpa [List.foldlM, hAct] using hFold
      have hCardsRest := ih (state := state') (finalState := finalState) hFold'
      have hCardsPlay := applyAction_playCard_preserves_total_cards state card state' hAct
      exact hCardsRest.trans hCardsPlay
  | endTurn =>
    intro finalState hFold
    simp [List.foldlM] at hFold
    exact applyAction_endTurn_preserves_total_cards state finalState hFold

-- ============================================================================
-- T1 (TURN ONE) THEOREM SETUP
-- ============================================================================

-- Standard prize count
def standardPrizeCount : Nat := 6

-- A valid starting game state
structure ValidStartingState (state : GameState) : Prop where
  playerOnePrizes : state.playerOne.prizes.length = standardPrizeCount
  playerTwoPrizes : state.playerTwo.prizes.length = standardPrizeCount
  cardConservation : validCardCount state

theorem turn_one_prizes_preserved (state : GameState) (actions : List Action)
    (hActions : TurnOneActions actions) :
    ∀ finalState : GameState,
      (actions.foldlM applyAction state = some finalState) →
      (getPlayerState finalState .playerTwo).prizes.length =
        (getPlayerState state .playerTwo).prizes.length := by
  -- Turn 1 actions exclude attacks, so player two prizes are unchanged.
  induction hActions generalizing state with
  | nil =>
    intro finalState hFold
    simp [List.foldlM] at hFold
    cases hFold
    rfl
  | play hRest ih =>
    rename_i card rest
    intro finalState hFold
    cases hAct : applyAction state (.playCard card) with
    | none =>
      simp [List.foldlM, hAct] at hFold
    | some state' =>
      have hFold' : rest.foldlM applyAction state' = some finalState := by
        simpa [List.foldlM, hAct] using hFold
      have hEqRest :=
        ih (state := state') (finalState := finalState) hFold'
      have hEqPlay :
          (getPlayerState state' .playerTwo).prizes.length =
            (getPlayerState state .playerTwo).prizes.length := by
        cases hPlayer : state.activePlayer with
        | playerOne =>
          simp [applyAction, getPlayerState, setPlayerState, hPlayer] at hAct
          cases hRemove : removeFirst card state.playerOne.hand with
          | none =>
            simp [hRemove] at hAct
          | some newHand =>
            simp [hRemove] at hAct
            cases hAct
            simp [getPlayerState, setPlayerState]
        | playerTwo =>
          simp [applyAction, getPlayerState, setPlayerState, hPlayer] at hAct
          cases hRemove : removeFirst card state.playerTwo.hand with
          | none =>
            simp [hRemove] at hAct
          | some newHand =>
            simp [hRemove] at hAct
            cases hAct
            cases hActive : state.playerTwo.active <;> simp [getPlayerState, hActive]
      exact hEqRest.trans hEqPlay
  | endTurn =>
    intro finalState hFold
    simp [List.foldlM, applyAction] at hFold
    cases hFold
    rfl
theorem applyAction_attack_prizes_le (state : GameState) (attackIndex : Nat) (finalState : GameState)
    (hFirst : state.activePlayer = .playerOne)
    (h : applyAction state (.attack attackIndex) = some finalState) :
    state.playerTwo.prizes.length ≤ finalState.playerTwo.prizes.length + 1 := by
  cases hAtt : state.playerOne.active with
  | none =>
    simp [applyAction, hFirst, otherPlayer, getPlayerState, hAtt] at h
  | some attacker =>
    cases hDef : state.playerTwo.active with
    | none =>
      simp [applyAction, hFirst, otherPlayer, getPlayerState, hAtt, hDef] at h
    | some defender =>
      cases hAttack : listGet? attacker.card.attacks attackIndex with
      | none =>
        simp [applyAction, hFirst, otherPlayer, getPlayerState, hAtt, hDef, hAttack] at h
      | some attack =>
        let damage := calculateDamage attack attacker.card.energyType defender.card
        let damagedDefender := applyDamage defender damage
        let effectedDefender := applyAttackEffects damagedDefender attack.effects
        by_cases hKo : effectedDefender.damage >= effectedDefender.card.hp
        · simp [applyAction, hFirst, otherPlayer, getPlayerState, hAtt, hDef, hAttack, hKo,
            damage, damagedDefender, effectedDefender] at h
          cases h
          simpa [getPlayerState, setPlayerState] using
            (takePrize_prizes_length_le state.playerOne state.playerTwo)
        · simp [applyAction, hFirst, otherPlayer, getPlayerState, hAtt, hDef, hAttack, hKo,
            damage, damagedDefender, effectedDefender] at h
          cases h
          simpa [getPlayerState, setPlayerState] using
            (Nat.le_succ state.playerTwo.prizes.length)

theorem turn_one_prizes_at_most_one (state : GameState) (actions : List Action)
    (hActions : TurnOneActions actions) :
    ∀ finalState : GameState,
      (actions.foldlM applyAction state = some finalState) →
      (getPlayerState state .playerTwo).prizes.length ≤
        (getPlayerState finalState .playerTwo).prizes.length + 1 := by
  intro finalState hFold
  have hEq := turn_one_prizes_preserved state actions hActions finalState hFold
  simpa [hEq] using (Nat.le_succ (getPlayerState state .playerTwo).prizes.length)

-- The Turn 1 Theorem: No sequence of legal actions on Turn 1 can result in a win
-- This states that from any valid starting state, after one turn, no player has won
theorem no_turn_one_win (state : GameState) (actions : List Action)
    (hStart : ValidStartingState state)
    (hActions : TurnOneActions actions) :
    ∀ finalState : GameState,
      (actions.foldlM applyAction state = some finalState) →
      ¬ hasWon finalState .playerOne := by
  intro finalState hFold hWon
  have hEq := turn_one_prizes_preserved state actions hActions finalState hFold
  have hWon' : (getPlayerState finalState .playerTwo).prizes.length = 0 := by
    simpa [hasWon, otherPlayer, getPlayerState] using hWon
  have hStartPrizes : (getPlayerState state .playerTwo).prizes.length = standardPrizeCount := by
    simpa [getPlayerState] using hStart.playerTwoPrizes
  have hStateZero : (getPlayerState state .playerTwo).prizes.length = 0 := by
    simpa [hEq] using hWon'
  have hStandardZero : standardPrizeCount = 0 := by
    simpa [hStartPrizes] using hStateZero
  simpa [standardPrizeCount] using hStandardZero

-- ============================================================================
-- DAMAGE CALCULATION VERIFICATION
-- ============================================================================

-- Damage is always non-negative (trivially true for Nat)
theorem damage_nonneg (attack : Attack) (attackerType : EnergyType) (defender : Card) :
    0 ≤ calculateDamage attack attackerType defender := by
  exact Nat.zero_le _

-- Weakness at most doubles damage (with default multiplier of 2)
theorem weakness_bounded (damage : Nat) (attackerType : EnergyType) (w : Weakness)
    (hMult : w.multiplier ≥ 1) :
    applyWeakness damage attackerType (some w) ≤ damage * w.multiplier := by
  simp only [applyWeakness]
  split
  · -- Weakness applies
    exact Nat.le_refl _
  · -- Weakness doesn't apply (wrong type), damage ≤ damage * multiplier when multiplier ≥ 1
    exact Nat.le_mul_of_pos_right damage hMult

-- Resistance reduces damage (cannot go negative due to Nat.sub)
theorem resistance_reduces (damage : Nat) (attackerType : EnergyType) (r : Resistance) :
    applyResistance damage attackerType (some r) ≤ damage := by
  simp only [applyResistance]
  split
  · -- Resistance applies
    exact Nat.sub_le damage r.amount
  · -- Resistance doesn't apply
    exact Nat.le_refl _

-- ============================================================================
-- SAMPLE CARDS FOR TESTING
-- ============================================================================

def samplePikachu : Card :=
  { name := "Pikachu"
  , hp := 60
  , energyType := .lightning
  , attacks := [{ name := "Thunder Shock", baseDamage := 20, effects := [.applyStatus .paralyzed] }]
  , weakness := some { energyType := .fighting }
  , resistance := some { energyType := .metal } }

def sampleCharmander : Card :=
  { name := "Charmander"
  , hp := 70
  , energyType := .fire
  , attacks := [{ name := "Ember", baseDamage := 30, effects := [] }]
  , weakness := some { energyType := .water }
  , resistance := none }

-- Helper to safely get first attack
def getFirstAttack (card : Card) : Option Attack :=
  match card.attacks with
  | [] => none
  | a :: _ => some a

-- Example evaluation: Pikachu attacking Charmander
#eval match getFirstAttack samplePikachu with
  | some atk => calculateDamage atk samplePikachu.energyType sampleCharmander
  | none => 0
-- Expected: 20 (no weakness/resistance interaction)

-- Example: Damage with weakness
def sampleSquirtle : Card :=
  { name := "Squirtle"
  , hp := 60
  , energyType := .water
  , attacks := [{ name := "Water Gun", baseDamage := 20, effects := [] }]
  , weakness := some { energyType := .lightning }
  , resistance := none }

#eval match getFirstAttack sampleSquirtle with
  | some atk => calculateDamage atk sampleSquirtle.energyType sampleCharmander
  | none => 0
-- Expected: 40 (water vs fire weakness, 20 * 2)
