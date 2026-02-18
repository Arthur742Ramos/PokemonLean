import PokemonLean.Basic

namespace PokemonLean.BoardState

open PokemonLean

-- ============================================================================
-- CORE CONSTANTS
-- ============================================================================

def defaultBenchLimit : Nat := 5

def skyFieldBenchLimit : Nat := 8

def prizeCardCount : Nat := 6

def totalCardsTarget : Nat := 60

def skyFieldName : String := "Sky Field"

@[simp] theorem defaultBenchLimit_eq : defaultBenchLimit = 5 := rfl
@[simp] theorem skyFieldBenchLimit_eq : skyFieldBenchLimit = 8 := rfl
@[simp] theorem prizeCardCount_eq : prizeCardCount = 6 := rfl
@[simp] theorem totalCardsTarget_eq : totalCardsTarget = 60 := rfl

-- ============================================================================
-- COMPLETE BOARD MODEL
-- ============================================================================

structure BoardPokemon where
  card : Card
  attachedEnergy : List Card := []
  attachedTools : List Card := []
  damageCounters : Nat := 0
  deriving Repr, BEq, DecidableEq

def mkBoardPokemon (card : Card) : BoardPokemon :=
  { card := card }

structure BoardState where
  active : Option BoardPokemon
  bench : List BoardPokemon
  discard : List Card
  deck : List Card
  hand : List Card
  prizes : List Card
  lostZone : List Card
  stadium : Option Card
  activeCondition : Option StatusCondition
  supporterPlayed : Bool := false
  gxUsed : Bool := false
  vstarUsed : Bool := false
  turnCounter : Nat := 0
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- BENCH LIMIT (5 default, 8 with Sky Field)
-- ============================================================================

def isSkyField (stadium : Option Card) : Bool :=
  match stadium with
  | some card => card.name == skyFieldName
  | none => false

def benchLimit (state : BoardState) : Nat :=
  if isSkyField state.stadium then skyFieldBenchLimit else defaultBenchLimit

@[simp] theorem isSkyField_none : isSkyField none = false := rfl

theorem isSkyField_some_eq (card : Card) :
    isSkyField (some card) = (card.name == skyFieldName) := by
  rfl

theorem benchLimit_no_stadium (state : BoardState) (h : state.stadium = none) :
    benchLimit state = defaultBenchLimit := by
  simp [benchLimit, isSkyField, h]

theorem benchLimit_sky_field (state : BoardState) (card : Card)
    (hStadium : state.stadium = some card)
    (hSky : card.name = skyFieldName) :
    benchLimit state = skyFieldBenchLimit := by
  simp [benchLimit, isSkyField, hStadium, hSky]

theorem benchLimit_non_sky_field (state : BoardState) (card : Card)
    (hStadium : state.stadium = some card)
    (hSky : (card.name == skyFieldName) = false) :
    benchLimit state = defaultBenchLimit := by
  simp [benchLimit, isSkyField, hStadium, hSky]

theorem defaultBenchLimit_le_benchLimit (state : BoardState) :
    defaultBenchLimit ≤ benchLimit state := by
  by_cases hSky : isSkyField state.stadium
  · simp [benchLimit, hSky]
  · simp [benchLimit, hSky]

theorem benchLimit_le_skyFieldBenchLimit (state : BoardState) :
    benchLimit state ≤ skyFieldBenchLimit := by
  by_cases hSky : isSkyField state.stadium
  · simp [benchLimit, hSky]
  · simp [benchLimit, hSky]

-- ============================================================================
-- CARD COUNTING
-- ============================================================================

def boardPokemonCardCount (pokemon : BoardPokemon) : Nat :=
  1 + pokemon.attachedEnergy.length + pokemon.attachedTools.length

def activeCardCount : Option BoardPokemon → Nat
  | none => 0
  | some pokemon => boardPokemonCardCount pokemon

def benchCardCount : List BoardPokemon → Nat
  | [] => 0
  | pokemon :: rest => boardPokemonCardCount pokemon + benchCardCount rest

def stadiumCardCount (stadium : Option Card) : Nat :=
  if stadium.isSome then 1 else 0

def totalCardCount (state : BoardState) : Nat :=
  state.deck.length +
  state.hand.length +
  state.prizes.length +
  state.discard.length +
  state.lostZone.length +
  activeCardCount state.active +
  benchCardCount state.bench +
  stadiumCardCount state.stadium

@[simp] theorem boardPokemonCardCount_mk (card : Card) :
    boardPokemonCardCount (mkBoardPokemon card) = 1 := by
  simp [mkBoardPokemon, boardPokemonCardCount]

theorem boardPokemonCardCount_pos (pokemon : BoardPokemon) :
    0 < boardPokemonCardCount pokemon := by
  have hOne : 1 ≤ boardPokemonCardCount pokemon := by
    unfold boardPokemonCardCount
    omega
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one hOne

@[simp] theorem boardPokemonCardCount_attachEnergy (pokemon : BoardPokemon) (energyCard : Card) :
    boardPokemonCardCount { pokemon with attachedEnergy := energyCard :: pokemon.attachedEnergy } =
      boardPokemonCardCount pokemon + 1 := by
  simp [boardPokemonCardCount, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

@[simp] theorem boardPokemonCardCount_attachTool (pokemon : BoardPokemon) (toolCard : Card) :
    boardPokemonCardCount { pokemon with attachedTools := toolCard :: pokemon.attachedTools } =
      boardPokemonCardCount pokemon + 1 := by
  simp [boardPokemonCardCount, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

@[simp] theorem boardPokemonCardCount_damageCounters (pokemon : BoardPokemon) (n : Nat) :
    boardPokemonCardCount { pokemon with damageCounters := n } = boardPokemonCardCount pokemon := by
  simp [boardPokemonCardCount]

@[simp] theorem activeCardCount_none :
    activeCardCount none = 0 := rfl

@[simp] theorem activeCardCount_some (pokemon : BoardPokemon) :
    activeCardCount (some pokemon) = boardPokemonCardCount pokemon := rfl

@[simp] theorem benchCardCount_nil :
    benchCardCount [] = 0 := rfl

@[simp] theorem benchCardCount_cons (pokemon : BoardPokemon) (rest : List BoardPokemon) :
    benchCardCount (pokemon :: rest) = boardPokemonCardCount pokemon + benchCardCount rest := rfl

@[simp] theorem stadiumCardCount_none :
    stadiumCardCount none = 0 := by
  simp [stadiumCardCount]

@[simp] theorem stadiumCardCount_some (card : Card) :
    stadiumCardCount (some card) = 1 := by
  simp [stadiumCardCount]

theorem benchCardCount_append (bench1 bench2 : List BoardPokemon) :
    benchCardCount (bench1 ++ bench2) = benchCardCount bench1 + benchCardCount bench2 := by
  induction bench1 with
  | nil =>
      simp [benchCardCount]
  | cons pokemon rest ih =>
      simp [benchCardCount, ih, Nat.add_assoc]

theorem benchCardCount_append_single (bench : List BoardPokemon) (pokemon : BoardPokemon) :
    benchCardCount (bench ++ [pokemon]) = benchCardCount bench + boardPokemonCardCount pokemon := by
  simpa using benchCardCount_append bench [pokemon]

def activeCards (pokemon : BoardPokemon) : List Card :=
  pokemon.card :: (pokemon.attachedEnergy ++ pokemon.attachedTools)

theorem activeCards_length (pokemon : BoardPokemon) :
    (activeCards pokemon).length = boardPokemonCardCount pokemon := by
  simp [activeCards, boardPokemonCardCount, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

-- ============================================================================
-- BOARD INVARIANTS
-- ============================================================================

def prizesInvariant (state : BoardState) : Prop :=
  state.prizes.length = prizeCardCount

def benchInvariant (state : BoardState) : Prop :=
  state.bench.length ≤ benchLimit state

def totalCardsInvariant (state : BoardState) : Prop :=
  totalCardCount state = totalCardsTarget

def boardInvariant (state : BoardState) : Prop :=
  prizesInvariant state ∧ benchInvariant state ∧ totalCardsInvariant state

theorem prizesInvariant_iff (state : BoardState) :
    prizesInvariant state ↔ state.prizes.length = prizeCardCount := by
  rfl

theorem benchInvariant_iff (state : BoardState) :
    benchInvariant state ↔ state.bench.length ≤ benchLimit state := by
  rfl

theorem totalCardsInvariant_iff (state : BoardState) :
    totalCardsInvariant state ↔ totalCardCount state = totalCardsTarget := by
  rfl

theorem boardInvariant_iff (state : BoardState) :
    boardInvariant state ↔
      prizesInvariant state ∧ benchInvariant state ∧ totalCardsInvariant state := by
  rfl

-- ============================================================================
-- BOARD TRANSITIONS (GAME ACTIONS)
-- ============================================================================

def drawCard (state : BoardState) : Option BoardState :=
  match state.deck with
  | [] => none
  | top :: rest =>
      some { state with deck := rest, hand := top :: state.hand }

def setActiveFromHand (state : BoardState) (card : Card) : Option BoardState :=
  match state.active with
  | some _ => none
  | none =>
      match removeFirst card state.hand with
      | none => none
      | some newHand =>
          some { state with
            hand := newHand
            active := some (mkBoardPokemon card)
            activeCondition := none }

def benchFromHand (state : BoardState) (card : Card) : Option BoardState :=
  if state.bench.length < benchLimit state then
    match removeFirst card state.hand with
    | none => none
    | some newHand =>
        some { state with
          hand := newHand
          bench := state.bench ++ [mkBoardPokemon card] }
  else
    none

def attachEnergyToActive (state : BoardState) (energyCard : Card) : Option BoardState :=
  match state.active with
  | none => none
  | some active =>
      match removeFirst energyCard state.hand with
      | none => none
      | some newHand =>
          some { state with
            hand := newHand
            active := some { active with attachedEnergy := energyCard :: active.attachedEnergy } }

def attachToolToActive (state : BoardState) (toolCard : Card) : Option BoardState :=
  match state.active with
  | none => none
  | some active =>
      match removeFirst toolCard state.hand with
      | none => none
      | some newHand =>
          some { state with
            hand := newHand
            active := some { active with attachedTools := toolCard :: active.attachedTools } }

def stadiumDiscard (state : BoardState) : List Card :=
  match state.stadium with
  | none => state.discard
  | some old => old :: state.discard

def withPlayedStadium (state : BoardState) (stadiumCard : Card) (newHand : List Card) : BoardState :=
  { state with
    hand := newHand
    discard := stadiumDiscard state
    stadium := some stadiumCard }

def playStadiumFromHand (state : BoardState) (stadiumCard : Card) : Option BoardState :=
  match removeFirst stadiumCard state.hand with
  | none => none
  | some newHand =>
      let nextState := withPlayedStadium state stadiumCard newHand
      if nextState.bench.length ≤ benchLimit nextState then
        some nextState
      else
        none

def moveActiveToDiscard (state : BoardState) : Option BoardState :=
  match state.active with
  | none => none
  | some active =>
      some { state with
        active := none
        activeCondition := none
        discard := activeCards active ++ state.discard }

def moveActiveToLostZone (state : BoardState) : Option BoardState :=
  match state.active with
  | none => none
  | some active =>
      some { state with
        active := none
        activeCondition := none
        lostZone := activeCards active ++ state.lostZone }

def placeDamageOnActive (state : BoardState) (counters : Nat) : Option BoardState :=
  match state.active with
  | none => none
  | some active =>
      some { state with active := some { active with damageCounters := active.damageCounters + counters } }

def healActive (state : BoardState) (counters : Nat) : Option BoardState :=
  match state.active with
  | none => none
  | some active =>
      some { state with active := some { active with damageCounters := active.damageCounters - counters } }

def setActiveCondition (state : BoardState) (condition : StatusCondition) : Option BoardState :=
  match state.active with
  | none => none
  | some _ =>
      some { state with activeCondition := some condition }

def clearActiveCondition (state : BoardState) : BoardState :=
  { state with activeCondition := none }

def playSupporter (state : BoardState) : Option BoardState :=
  if state.supporterPlayed then none else some { state with supporterPlayed := true }

def useGX (state : BoardState) : Option BoardState :=
  if state.gxUsed then none else some { state with gxUsed := true }

def useVSTAR (state : BoardState) : Option BoardState :=
  if state.vstarUsed then none else some { state with vstarUsed := true }

def endTurn (state : BoardState) : BoardState :=
  { state with
    supporterPlayed := false
    turnCounter := state.turnCounter + 1 }

inductive BoardAction
  | drawCard
  | setActiveFromHand (card : Card)
  | benchFromHand (card : Card)
  | attachEnergyToActive (card : Card)
  | attachToolToActive (card : Card)
  | playStadiumFromHand (card : Card)
  | moveActiveToDiscard
  | moveActiveToLostZone
  | placeDamageOnActive (counters : Nat)
  | healActive (counters : Nat)
  | setActiveCondition (condition : StatusCondition)
  | clearActiveCondition
  | playSupporter
  | useGX
  | useVSTAR
  | endTurn
  deriving Repr, BEq, DecidableEq

def stepBoard (state : BoardState) (action : BoardAction) : Option BoardState :=
  match action with
  | .drawCard => drawCard state
  | .setActiveFromHand card => setActiveFromHand state card
  | .benchFromHand card => benchFromHand state card
  | .attachEnergyToActive card => attachEnergyToActive state card
  | .attachToolToActive card => attachToolToActive state card
  | .playStadiumFromHand card => playStadiumFromHand state card
  | .moveActiveToDiscard => moveActiveToDiscard state
  | .moveActiveToLostZone => moveActiveToLostZone state
  | .placeDamageOnActive counters => placeDamageOnActive state counters
  | .healActive counters => healActive state counters
  | .setActiveCondition condition => setActiveCondition state condition
  | .clearActiveCondition => some (clearActiveCondition state)
  | .playSupporter => playSupporter state
  | .useGX => useGX state
  | .useVSTAR => useVSTAR state
  | .endTurn => some (endTurn state)

def stepBoardMany : BoardState → List BoardAction → Option BoardState
  | state, [] => some state
  | state, action :: rest =>
      match stepBoard state action with
      | none => none
      | some next => stepBoardMany next rest

-- ============================================================================
-- TRANSITION THEOREMS
-- ============================================================================

theorem drawCard_none_when_deck_empty (state : BoardState)
    (hDeck : state.deck = []) :
    drawCard state = none := by
  simp [drawCard, hDeck]

theorem drawCard_some_hand_length (state next : BoardState)
    (h : drawCard state = some next) :
    next.hand.length = state.hand.length + 1 := by
  cases hDeck : state.deck with
  | nil =>
      simp [drawCard, hDeck] at h
  | cons top rest =>
      simp [drawCard, hDeck] at h
      cases h
      simp

theorem drawCard_some_deck_length (state next : BoardState)
    (h : drawCard state = some next) :
    next.deck.length + 1 = state.deck.length := by
  cases hDeck : state.deck with
  | nil =>
      simp [drawCard, hDeck] at h
  | cons top rest =>
      simp [drawCard, hDeck] at h
      cases h
      simp

theorem drawCard_preserves_totalCards (state next : BoardState)
    (h : drawCard state = some next) :
    totalCardCount next = totalCardCount state := by
  cases hDeck : state.deck with
  | nil =>
      simp [drawCard, hDeck] at h
  | cons top rest =>
      simp [drawCard, hDeck] at h
      cases h
      simpa [hDeck, totalCardCount, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem setActiveFromHand_none_when_active (state : BoardState) (card : Card) (active : BoardPokemon)
    (hActive : state.active = some active) :
    setActiveFromHand state card = none := by
  simp [setActiveFromHand, hActive]

theorem setActiveFromHand_none_when_missing (state : BoardState) (card : Card)
    (hActive : state.active = none) (hRemove : removeFirst card state.hand = none) :
    setActiveFromHand state card = none := by
  simp [setActiveFromHand, hActive, hRemove]

theorem setActiveFromHand_some_active_isSome (state next : BoardState) (card : Card)
    (h : setActiveFromHand state card = some next) :
    next.active.isSome = true := by
  unfold setActiveFromHand at h
  cases hActive : state.active with
  | some active =>
      simp [hActive] at h
  | none =>
      simp [hActive] at h
      cases hRemove : removeFirst card state.hand with
      | none =>
          simp [hRemove] at h
      | some newHand =>
          simp [hRemove] at h
          cases h
          simp

theorem setActiveFromHand_preserves_totalCards (state next : BoardState) (card : Card)
    (h : setActiveFromHand state card = some next) :
    totalCardCount next = totalCardCount state := by
  unfold setActiveFromHand at h
  cases hActive : state.active with
  | some active =>
      simp [hActive] at h
  | none =>
      simp [hActive] at h
      cases hRemove : removeFirst card state.hand with
      | none =>
          simp [hRemove] at h
      | some newHand =>
          simp [hRemove] at h
          cases h
          have hLen : newHand.length + 1 = state.hand.length :=
            removeFirst_length card state.hand newHand hRemove
          have hHand : state.hand.length = newHand.length + 1 := by
            simpa [Nat.add_comm] using hLen.symm
          simp [totalCardCount, hActive, hHand, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem benchFromHand_none_when_full (state : BoardState) (card : Card)
    (hFull : ¬ state.bench.length < benchLimit state) :
    benchFromHand state card = none := by
  simp [benchFromHand, hFull]

theorem benchFromHand_some_bench_length (state next : BoardState) (card : Card)
    (h : benchFromHand state card = some next) :
    next.bench.length = state.bench.length + 1 := by
  unfold benchFromHand at h
  by_cases hBench : state.bench.length < benchLimit state
  · simp [hBench] at h
    cases hRemove : removeFirst card state.hand with
    | none =>
        simp [hRemove] at h
    | some newHand =>
        simp [hRemove] at h
        cases h
        simp
  · simp [hBench] at h

theorem benchFromHand_preserves_totalCards (state next : BoardState) (card : Card)
    (h : benchFromHand state card = some next) :
    totalCardCount next = totalCardCount state := by
  unfold benchFromHand at h
  by_cases hBench : state.bench.length < benchLimit state
  · simp [hBench] at h
    cases hRemove : removeFirst card state.hand with
    | none =>
        simp [hRemove] at h
    | some newHand =>
        simp [hRemove] at h
        cases h
        have hLen : newHand.length + 1 = state.hand.length :=
          removeFirst_length card state.hand newHand hRemove
        have hHand : state.hand.length = newHand.length + 1 := by
          simpa [Nat.add_comm] using hLen.symm
        simp [totalCardCount, benchCardCount_append_single, hHand, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  · simp [hBench] at h

theorem attachEnergyToActive_none_no_active (state : BoardState) (energyCard : Card)
    (hActive : state.active = none) :
    attachEnergyToActive state energyCard = none := by
  simp [attachEnergyToActive, hActive]

theorem attachEnergyToActive_some_hand_length (state next : BoardState) (energyCard : Card)
    (h : attachEnergyToActive state energyCard = some next) :
    next.hand.length + 1 = state.hand.length := by
  unfold attachEnergyToActive at h
  cases hActive : state.active with
  | none =>
      simp [hActive] at h
  | some active =>
      simp [hActive] at h
      cases hRemove : removeFirst energyCard state.hand with
      | none =>
          simp [hRemove] at h
      | some newHand =>
          simp [hRemove] at h
          cases h
          simpa using removeFirst_length energyCard state.hand newHand hRemove

theorem attachEnergyToActive_preserves_totalCards (state next : BoardState) (energyCard : Card)
    (h : attachEnergyToActive state energyCard = some next) :
    totalCardCount next = totalCardCount state := by
  unfold attachEnergyToActive at h
  cases hActive : state.active with
  | none =>
      simp [hActive] at h
  | some active =>
      simp [hActive] at h
      cases hRemove : removeFirst energyCard state.hand with
      | none =>
          simp [hRemove] at h
      | some newHand =>
          simp [hRemove] at h
          cases h
          have hLen : newHand.length + 1 = state.hand.length :=
            removeFirst_length energyCard state.hand newHand hRemove
          have hHand : state.hand.length = newHand.length + 1 := by
            simpa [Nat.add_comm] using hLen.symm
          simp [totalCardCount, hActive, hHand, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem attachToolToActive_none_no_active (state : BoardState) (toolCard : Card)
    (hActive : state.active = none) :
    attachToolToActive state toolCard = none := by
  simp [attachToolToActive, hActive]

theorem attachToolToActive_some_hand_length (state next : BoardState) (toolCard : Card)
    (h : attachToolToActive state toolCard = some next) :
    next.hand.length + 1 = state.hand.length := by
  unfold attachToolToActive at h
  cases hActive : state.active with
  | none =>
      simp [hActive] at h
  | some active =>
      simp [hActive] at h
      cases hRemove : removeFirst toolCard state.hand with
      | none =>
          simp [hRemove] at h
      | some newHand =>
          simp [hRemove] at h
          cases h
          simpa using removeFirst_length toolCard state.hand newHand hRemove

theorem attachToolToActive_preserves_totalCards (state next : BoardState) (toolCard : Card)
    (h : attachToolToActive state toolCard = some next) :
    totalCardCount next = totalCardCount state := by
  unfold attachToolToActive at h
  cases hActive : state.active with
  | none =>
      simp [hActive] at h
  | some active =>
      simp [hActive] at h
      cases hRemove : removeFirst toolCard state.hand with
      | none =>
          simp [hRemove] at h
      | some newHand =>
          simp [hRemove] at h
          cases h
          have hLen : newHand.length + 1 = state.hand.length :=
            removeFirst_length toolCard state.hand newHand hRemove
          have hHand : state.hand.length = newHand.length + 1 := by
            simpa [Nat.add_comm] using hLen.symm
          simp [totalCardCount, hActive, hHand, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

@[simp] theorem withPlayedStadium_stadium (state : BoardState) (stadiumCard : Card) (newHand : List Card) :
    (withPlayedStadium state stadiumCard newHand).stadium = some stadiumCard := by
  rfl

@[simp] theorem withPlayedStadium_hand (state : BoardState) (stadiumCard : Card) (newHand : List Card) :
    (withPlayedStadium state stadiumCard newHand).hand = newHand := by
  rfl

theorem playStadiumFromHand_none_when_missing (state : BoardState) (stadiumCard : Card)
    (hRemove : removeFirst stadiumCard state.hand = none) :
    playStadiumFromHand state stadiumCard = none := by
  simp [playStadiumFromHand, hRemove]

theorem playStadiumFromHand_some_stadium (state next : BoardState) (stadiumCard : Card)
    (h : playStadiumFromHand state stadiumCard = some next) :
    next.stadium = some stadiumCard := by
  unfold playStadiumFromHand at h
  cases hRemove : removeFirst stadiumCard state.hand with
  | none =>
      simp [hRemove] at h
  | some newHand =>
      by_cases hBench :
          (withPlayedStadium state stadiumCard newHand).bench.length ≤
            benchLimit (withPlayedStadium state stadiumCard newHand)
      · simp [hRemove, hBench] at h
        cases h
        simp
      · simp [hRemove, hBench] at h

theorem playStadiumFromHand_preserves_totalCards (state next : BoardState) (stadiumCard : Card)
    (h : playStadiumFromHand state stadiumCard = some next) :
    totalCardCount next = totalCardCount state := by
  unfold playStadiumFromHand at h
  cases hRemove : removeFirst stadiumCard state.hand with
  | none =>
      simp [hRemove] at h
  | some newHand =>
      by_cases hBench :
          (withPlayedStadium state stadiumCard newHand).bench.length ≤
            benchLimit (withPlayedStadium state stadiumCard newHand)
      · simp [hRemove, hBench] at h
        cases h
        have hLen : newHand.length + 1 = state.hand.length :=
          removeFirst_length stadiumCard state.hand newHand hRemove
        have hHand : state.hand.length = newHand.length + 1 := by
          simpa [Nat.add_comm] using hLen.symm
        cases hStadium : state.stadium with
        | none =>
            simp [totalCardCount, withPlayedStadium, stadiumDiscard, hStadium, hHand,
              Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        | some old =>
            simp [totalCardCount, withPlayedStadium, stadiumDiscard, hStadium, hHand,
              Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · simp [hRemove, hBench] at h

theorem moveActiveToDiscard_none (state : BoardState)
    (hActive : state.active = none) :
    moveActiveToDiscard state = none := by
  simp [moveActiveToDiscard, hActive]

theorem moveActiveToDiscard_preserves_totalCards (state next : BoardState)
    (h : moveActiveToDiscard state = some next) :
    totalCardCount next = totalCardCount state := by
  unfold moveActiveToDiscard at h
  cases hActive : state.active with
  | none =>
      simp [hActive] at h
  | some active =>
      simp [hActive] at h
      cases h
      simp [totalCardCount, hActive, activeCards_length, List.length_append,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem moveActiveToLostZone_none (state : BoardState)
    (hActive : state.active = none) :
    moveActiveToLostZone state = none := by
  simp [moveActiveToLostZone, hActive]

theorem moveActiveToLostZone_preserves_totalCards (state next : BoardState)
    (h : moveActiveToLostZone state = some next) :
    totalCardCount next = totalCardCount state := by
  unfold moveActiveToLostZone at h
  cases hActive : state.active with
  | none =>
      simp [hActive] at h
  | some active =>
      simp [hActive] at h
      cases h
      simp [totalCardCount, hActive, activeCards_length, List.length_append,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem placeDamageOnActive_preserves_totalCards (state next : BoardState) (counters : Nat)
    (h : placeDamageOnActive state counters = some next) :
    totalCardCount next = totalCardCount state := by
  unfold placeDamageOnActive at h
  cases hActive : state.active with
  | none =>
      simp [hActive] at h
  | some active =>
      simp [hActive] at h
      cases h
      simp [totalCardCount, hActive]

theorem healActive_preserves_totalCards (state next : BoardState) (counters : Nat)
    (h : healActive state counters = some next) :
    totalCardCount next = totalCardCount state := by
  unfold healActive at h
  cases hActive : state.active with
  | none =>
      simp [hActive] at h
  | some active =>
      simp [hActive] at h
      cases h
      simp [totalCardCount, hActive]

theorem setActiveCondition_preserves_totalCards (state next : BoardState) (condition : StatusCondition)
    (h : setActiveCondition state condition = some next) :
    totalCardCount next = totalCardCount state := by
  unfold setActiveCondition at h
  cases hActive : state.active with
  | none =>
      simp [hActive] at h
  | some active =>
      simp [hActive] at h
      cases h
      simp [totalCardCount, hActive]

theorem clearActiveCondition_preserves_totalCards (state : BoardState) :
    totalCardCount (clearActiveCondition state) = totalCardCount state := by
  simp [clearActiveCondition, totalCardCount]

theorem playSupporter_first (state : BoardState)
    (h : state.supporterPlayed = false) :
    playSupporter state = some { state with supporterPlayed := true } := by
  simp [playSupporter, h]

theorem playSupporter_twice_none (state : BoardState)
    (h : state.supporterPlayed = true) :
    playSupporter state = none := by
  simp [playSupporter, h]

theorem playSupporter_preserves_totalCards (state next : BoardState)
    (h : playSupporter state = some next) :
    totalCardCount next = totalCardCount state := by
  unfold playSupporter at h
  by_cases hPlayed : state.supporterPlayed
  · simp [hPlayed] at h
  · simp [hPlayed] at h
    cases h
    simp [totalCardCount]

theorem useGX_sets_flag (state next : BoardState)
    (h : useGX state = some next) :
    next.gxUsed = true := by
  unfold useGX at h
  by_cases hUsed : state.gxUsed
  · simp [hUsed] at h
  · simp [hUsed] at h
    cases h
    simp

theorem useGX_twice_none (state : BoardState)
    (h : state.gxUsed = true) :
    useGX state = none := by
  simp [useGX, h]

theorem useGX_preserves_totalCards (state next : BoardState)
    (h : useGX state = some next) :
    totalCardCount next = totalCardCount state := by
  unfold useGX at h
  by_cases hUsed : state.gxUsed
  · simp [hUsed] at h
  · simp [hUsed] at h
    cases h
    simp [totalCardCount]

theorem useVSTAR_sets_flag (state next : BoardState)
    (h : useVSTAR state = some next) :
    next.vstarUsed = true := by
  unfold useVSTAR at h
  by_cases hUsed : state.vstarUsed
  · simp [hUsed] at h
  · simp [hUsed] at h
    cases h
    simp

theorem useVSTAR_twice_none (state : BoardState)
    (h : state.vstarUsed = true) :
    useVSTAR state = none := by
  simp [useVSTAR, h]

theorem useVSTAR_preserves_totalCards (state next : BoardState)
    (h : useVSTAR state = some next) :
    totalCardCount next = totalCardCount state := by
  unfold useVSTAR at h
  by_cases hUsed : state.vstarUsed
  · simp [hUsed] at h
  · simp [hUsed] at h
    cases h
    simp [totalCardCount]

theorem endTurn_increments_counter (state : BoardState) :
    (endTurn state).turnCounter = state.turnCounter + 1 := by
  simp [endTurn]

theorem endTurn_resets_supporter (state : BoardState) :
    (endTurn state).supporterPlayed = false := by
  simp [endTurn]

theorem endTurn_preserves_totalCards (state : BoardState) :
    totalCardCount (endTurn state) = totalCardCount state := by
  simp [endTurn, totalCardCount]

@[simp] theorem stepBoard_drawCard_eq (state : BoardState) :
    stepBoard state .drawCard = drawCard state := rfl

@[simp] theorem stepBoard_endTurn_eq (state : BoardState) :
    stepBoard state .endTurn = some (endTurn state) := rfl

@[simp] theorem stepBoardMany_nil (state : BoardState) :
    stepBoardMany state [] = some state := rfl

@[simp] theorem stepBoardMany_cons (state : BoardState) (action : BoardAction) (rest : List BoardAction) :
    stepBoardMany state (action :: rest) =
      match stepBoard state action with
      | none => none
      | some next => stepBoardMany next rest := rfl

theorem stepBoard_preserves_totalCards (state next : BoardState) (action : BoardAction)
    (h : stepBoard state action = some next) :
    totalCardCount next = totalCardCount state := by
  cases action with
  | drawCard =>
      exact drawCard_preserves_totalCards state next h
  | setActiveFromHand card =>
      exact setActiveFromHand_preserves_totalCards state next card h
  | benchFromHand card =>
      exact benchFromHand_preserves_totalCards state next card h
  | attachEnergyToActive card =>
      exact attachEnergyToActive_preserves_totalCards state next card h
  | attachToolToActive card =>
      exact attachToolToActive_preserves_totalCards state next card h
  | playStadiumFromHand card =>
      exact playStadiumFromHand_preserves_totalCards state next card h
  | moveActiveToDiscard =>
      exact moveActiveToDiscard_preserves_totalCards state next h
  | moveActiveToLostZone =>
      exact moveActiveToLostZone_preserves_totalCards state next h
  | placeDamageOnActive counters =>
      exact placeDamageOnActive_preserves_totalCards state next counters h
  | healActive counters =>
      exact healActive_preserves_totalCards state next counters h
  | setActiveCondition condition =>
      exact setActiveCondition_preserves_totalCards state next condition h
  | clearActiveCondition =>
      simp [stepBoard, clearActiveCondition] at h
      cases h
      exact clearActiveCondition_preserves_totalCards state
  | playSupporter =>
      exact playSupporter_preserves_totalCards state next h
  | useGX =>
      exact useGX_preserves_totalCards state next h
  | useVSTAR =>
      exact useVSTAR_preserves_totalCards state next h
  | endTurn =>
      simp [stepBoard] at h
      cases h
      simpa using endTurn_preserves_totalCards state

theorem stepBoard_preserves_totalInvariant (state next : BoardState) (action : BoardAction)
    (hInv : totalCardsInvariant state)
    (hStep : stepBoard state action = some next) :
    totalCardsInvariant next := by
  unfold totalCardsInvariant at hInv ⊢
  calc
    totalCardCount next = totalCardCount state := stepBoard_preserves_totalCards state next action hStep
    _ = totalCardsTarget := hInv

end PokemonLean.BoardState
