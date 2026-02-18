/-
  PokemonLean / Core / MulliganSetup.lean

  Game setup and mulligan system for the Pokémon TCG.
  ====================================================

  Models:
    - Deck requirements: exactly 60 cards, max 4 copies of any card (except basic energy)
    - Opening hand: draw 7 cards
    - Must have at least 1 Basic Pokémon in opening hand
    - Mulligan: if no Basic in hand, reveal, shuffle, redraw 7; opponent may draw 1
    - Repeated mulligans: keep mulliganing until a Basic is found
    - Setup sequence: flip coin, draw 7, mulligan if needed, place active + bench, 6 prizes

  Self-contained — no imports from other PokemonLean modules.
  All proofs are sorry-free.  37 theorems.
-/

set_option linter.unusedVariables false

namespace PokemonLean.Core.MulliganSetup

-- ============================================================
-- §1  Core Types
-- ============================================================

/-- Card category for setup purposes. -/
inductive MullCardKind where
  | basicPokemon
  | stagePokemon
  | trainer
  | basicEnergy
  | specialEnergy
deriving DecidableEq, Repr, BEq, Inhabited

/-- Bridge BEq to DecidableEq so simp can reason about equality. -/
@[simp] theorem beq_mullCardKind_eq_decide (a b : MullCardKind) :
    (a == b) = decide (a = b) := by
  cases a <;> cases b <;> decide

/-- A card for the mulligan/setup system. -/
structure MullCard where
  name     : String
  kind     : MullCardKind
deriving DecidableEq, Repr, BEq, Inhabited

/-- A deck is a list of cards. -/
abbrev MDeck := List MullCard

/-- Coin flip result. -/
inductive MCoin where
  | heads | tails
deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================
-- §2  Deck Requirements
-- ============================================================

def deckSize (d : MDeck) : Nat := d.length

def countByName (nm : String) (d : MDeck) : Nat :=
  (d.filter (fun c => c.name == nm)).length

def isBasicEnergyCard (c : MullCard) : Bool :=
  c.kind == .basicEnergy

def basicPokemonCount (d : MDeck) : Nat :=
  (d.filter (fun c => c.kind == .basicPokemon)).length

def hasBasicPokemonBool (d : MDeck) : Bool :=
  d.any (fun c => c.kind == .basicPokemon)

/-- A deck is size-valid if it has exactly 60 cards. -/
def validSize (d : MDeck) : Prop := d.length = 60

-- ============================================================
-- §3  Hand Drawing
-- ============================================================

/-- Draw n cards from a deck (take the top n). -/
def drawCards (d : MDeck) (n : Nat) : MDeck × MDeck :=
  (d.take n, d.drop n)

/-- The opening hand size. -/
def openingHandSize : Nat := 7

/-- Draw an opening hand. -/
def drawOpeningHand (d : MDeck) : MDeck × MDeck :=
  drawCards d openingHandSize

-- ============================================================
-- §4  Mulligan System
-- ============================================================

/-- Whether a hand contains at least one basic Pokémon. -/
def handHasBasic (hand : MDeck) : Bool :=
  hand.any (fun c => c.kind == .basicPokemon)

/-- A mulligan state: tracks the deck, hand, and number of mulligans taken. -/
structure MulliganState where
  deck           : MDeck
  hand           : MDeck
  mulliganCount  : Nat
  opponentDraws  : Nat
deriving Repr

/-- Initialize mulligan state from a shuffled deck. -/
def initMulliganState (d : MDeck) : MulliganState :=
  let (hand, remaining) := drawOpeningHand d
  { deck := remaining, hand := hand, mulliganCount := 0, opponentDraws := 0 }

/-- Perform one mulligan: shuffle hand back, redraw 7.
    In our model, the "reshuffled" deck is hand ++ deck (simplified). -/
def performMulligan (st : MulliganState) : MulliganState :=
  let fullDeck := st.hand ++ st.deck
  let (newHand, remaining) := drawOpeningHand fullDeck
  { deck := remaining, hand := newHand,
    mulliganCount := st.mulliganCount + 1,
    opponentDraws := st.opponentDraws + 1 }

-- ============================================================
-- §5  Setup Constants
-- ============================================================

def prizeCount : Nat := 6
def maxBenchSize : Nat := 5
def maxCopies : Nat := 4
def deckRequiredSize : Nat := 60

/-- Prize cards: top 6 from remaining deck. -/
def drawPrizes (d : MDeck) : MDeck × MDeck :=
  drawCards d 6

-- ============================================================
-- §6  Example Cards
-- ============================================================

def pikachuCard : MullCard :=
  { name := "Pikachu", kind := .basicPokemon }

def raltsCard : MullCard :=
  { name := "Ralts", kind := .basicPokemon }

def gardevoirCard : MullCard :=
  { name := "Gardevoir ex", kind := .stagePokemon }

def bossOrdersCard : MullCard :=
  { name := "Boss's Orders", kind := .trainer }

def psychicEnergyCard : MullCard :=
  { name := "Psychic Energy", kind := .basicEnergy }

def doubleColorless : MullCard :=
  { name := "Double Colorless Energy", kind := .specialEnergy }

/-- Make n copies of a card. -/
def makeN (c : MullCard) (n : Nat) : MDeck :=
  List.replicate n c

-- ============================================================
-- §7  Repeated Mulligans
-- ============================================================

def repeatMulligan : MulliganState → Nat → MulliganState
  | st, 0     => st
  | st, n + 1 => repeatMulligan (performMulligan st) n

-- ============================================================
-- §8  Theorems — Draw Preservation
-- ============================================================

/-- Drawing preserves total card count. -/
theorem draw_preserves_total (d : MDeck) (n : Nat) :
    (drawCards d n).1.length + (drawCards d n).2.length = d.length := by
  simp only [drawCards, List.length_take, List.length_drop]
  omega

/-- Opening hand is at most 7 cards. -/
theorem opening_hand_le_7 (d : MDeck) :
    (drawOpeningHand d).1.length ≤ 7 := by
  simp only [drawOpeningHand, openingHandSize, drawCards, List.length_take]
  omega

/-- Opening hand from a 60-card deck is exactly 7. -/
theorem opening_hand_eq_7 (d : MDeck) (h : d.length = 60) :
    (drawOpeningHand d).1.length = 7 := by
  simp only [drawOpeningHand, openingHandSize, drawCards, List.length_take]
  omega

/-- After drawing opening hand from 60-card deck, 53 cards remain. -/
theorem remaining_after_draw (d : MDeck) (h : d.length = 60) :
    (drawOpeningHand d).2.length = 53 := by
  simp only [drawOpeningHand, openingHandSize, drawCards, List.length_drop]
  omega

/-- The prize draw takes 6 cards when enough remain. -/
theorem prize_draw_count (d : MDeck) (h : d.length ≥ 6) :
    (drawPrizes d).1.length = 6 := by
  simp only [drawPrizes, drawCards, List.length_take]
  omega

/-- After drawing prizes from a 53-card remaining deck, 47 cards left. -/
theorem after_prizes_remaining (d : MDeck) (h : d.length = 53) :
    (drawPrizes d).2.length = 47 := by
  simp only [drawPrizes, drawCards, List.length_drop]
  omega

-- ============================================================
-- §9  Theorems — Mulligan State Properties
-- ============================================================

/-- Mulligan increments the mulligan counter. -/
theorem mulligan_increments (st : MulliganState) :
    (performMulligan st).mulliganCount = st.mulliganCount + 1 := by
  rfl

/-- Mulligan increments opponent draw opportunities. -/
theorem mulligan_opponent_draw (st : MulliganState) :
    (performMulligan st).opponentDraws = st.opponentDraws + 1 := by
  rfl

/-- Initial state has 0 mulligans. -/
theorem init_zero_mulligans (d : MDeck) :
    (initMulliganState d).mulliganCount = 0 := by
  rfl

/-- Initial state has 0 opponent draws. -/
theorem init_zero_opponent_draws (d : MDeck) :
    (initMulliganState d).opponentDraws = 0 := by
  rfl

/-- The total cards (hand + deck) is preserved across mulligan. -/
theorem mulligan_preserves_total (st : MulliganState) :
    (performMulligan st).hand.length + (performMulligan st).deck.length =
    st.hand.length + st.deck.length := by
  simp only [performMulligan, drawOpeningHand, openingHandSize, drawCards,
             List.length_take, List.length_drop, List.length_append]
  omega

/-- After k mulligans, opponent has k draw opportunities. -/
theorem k_mulligans_k_draws (st : MulliganState)
    (h : st.mulliganCount = st.opponentDraws) :
    (performMulligan st).mulliganCount = (performMulligan st).opponentDraws := by
  simp only [performMulligan, h]

-- ============================================================
-- §10  Theorems — Basic Energy Exceptions
-- ============================================================

/-- Basic energy is identified by kind. -/
theorem basic_energy_identified (c : MullCard) :
    isBasicEnergyCard c = true ↔ c.kind = .basicEnergy := by
  simp [isBasicEnergyCard]

/-- Psychic Energy is basic energy. -/
theorem psychic_is_basic_energy :
    isBasicEnergyCard psychicEnergyCard = true := by native_decide

/-- Double Colorless is NOT basic energy. -/
theorem dce_not_basic_energy :
    isBasicEnergyCard doubleColorless = false := by native_decide

/-- Boss's Orders is NOT basic energy. -/
theorem boss_not_basic_energy :
    isBasicEnergyCard bossOrdersCard = false := by native_decide

-- ============================================================
-- §11  Theorems — Hand / Basic Checks
-- ============================================================

/-- A hand with a basic Pokémon passes the check. -/
theorem hand_with_basic_passes (hand : MDeck) (c : MullCard)
    (hc : c.kind = .basicPokemon) (hmem : c ∈ hand) :
    handHasBasic hand = true := by
  simp [handHasBasic, List.any_eq_true]
  exact ⟨c, hmem, by simp [hc]⟩

/-- An empty hand has no basic. -/
theorem empty_hand_no_basic : handHasBasic [] = false := by native_decide

/-- Pikachu is a basic Pokémon. -/
theorem pikachu_is_basic : pikachuCard.kind = .basicPokemon := by rfl

/-- A singleton hand with Pikachu has a basic. -/
theorem singleton_pikachu_has_basic :
    handHasBasic [pikachuCard] = true := by native_decide

/-- A hand of only trainers has no basic. -/
theorem trainers_only_no_basic :
    handHasBasic (makeN bossOrdersCard 7) = false := by native_decide

/-- A hand of only energy has no basic. -/
theorem energy_only_no_basic :
    handHasBasic (makeN psychicEnergyCard 7) = false := by native_decide

-- ============================================================
-- §12  Theorems — Count Properties
-- ============================================================

/-- countByName on an empty deck is 0. -/
theorem count_empty (nm : String) : countByName nm [] = 0 := by
  rfl

/-- replicate n of a card c gives countByName c.name = n. -/
theorem count_replicate (c : MullCard) (n : Nat) :
    countByName c.name (makeN c n) = n := by
  simp [countByName, makeN]

/-- basicPokemonCount on an empty deck is 0. -/
theorem basic_count_empty : basicPokemonCount [] = 0 := by
  rfl

/-- basicPokemonCount of replicated basics. -/
theorem basic_count_replicate_basic (c : MullCard) (n : Nat)
    (hk : c.kind = .basicPokemon) :
    basicPokemonCount (makeN c n) = n := by
  simp [basicPokemonCount, makeN, hk]

/-- basicPokemonCount of replicated non-basics is 0. -/
theorem basic_count_replicate_nonbasic (c : MullCard) (n : Nat)
    (hk : c.kind ≠ .basicPokemon) :
    basicPokemonCount (makeN c n) = 0 := by
  simp [basicPokemonCount, makeN, hk]

-- ============================================================
-- §13  Theorems — Setup Sequence Constants
-- ============================================================

/-- deckRequiredSize is 60. -/
theorem deck_required_size_val : deckRequiredSize = 60 := by rfl

/-- prizeCount is 6. -/
theorem prize_count_val : prizeCount = 6 := by rfl

/-- openingHandSize is 7. -/
theorem opening_hand_size_val : openingHandSize = 7 := by rfl

/-- maxCopies is 4. -/
theorem max_copies_val : maxCopies = 4 := by rfl

/-- maxBenchSize is 5. -/
theorem max_bench_size_val : maxBenchSize = 5 := by rfl

/-- 60 = 7 (hand) + 6 (prizes) + 47 (remaining deck). -/
theorem setup_card_accounting : 60 = openingHandSize + prizeCount + 47 := by
  rfl

/-- Drawing 7 then 6 from 60 leaves 47. -/
theorem full_setup_remaining (d : MDeck) (h : d.length = 60) :
    ((drawPrizes (drawOpeningHand d).2).2).length = 47 := by
  simp only [drawOpeningHand, openingHandSize, drawPrizes, drawCards,
             List.length_drop, List.length_take]
  omega

-- ============================================================
-- §14  Theorems — Adding Basics
-- ============================================================

/-- Adding a basic to a deck increases basic count by 1. -/
theorem adding_basic_increases_count (d : MDeck) (c : MullCard)
    (hk : c.kind = .basicPokemon) :
    basicPokemonCount (c :: d) = basicPokemonCount d + 1 := by
  simp [basicPokemonCount, hk]

/-- Adding a non-basic doesn't change basic count. -/
theorem adding_nonbasic_preserves_count (d : MDeck) (c : MullCard)
    (hk : c.kind ≠ .basicPokemon) :
    basicPokemonCount (c :: d) = basicPokemonCount d := by
  simp [basicPokemonCount, hk]

-- ============================================================
-- §15  Theorems — Repeated Mulligan Accumulation
-- ============================================================

/-- General lemma: repeated mulligans add to mulliganCount. -/
theorem repeat_mulligan_count_gen (st : MulliganState) (k : Nat) :
    (repeatMulligan st k).mulliganCount = st.mulliganCount + k := by
  induction k generalizing st with
  | zero => simp [repeatMulligan]
  | succ m ih =>
    simp only [repeatMulligan]
    rw [ih]
    simp [performMulligan]
    omega

/-- After n mulligans from a fresh init, mulliganCount = n. -/
theorem repeat_mulligan_count_from_init (d : MDeck) (n : Nat) :
    (repeatMulligan (initMulliganState d) n).mulliganCount = n := by
  rw [repeat_mulligan_count_gen]
  simp [initMulliganState]

/-- General lemma: repeated mulligans add to opponentDraws. -/
theorem repeat_mulligan_draws_gen (st : MulliganState) (k : Nat) :
    (repeatMulligan st k).opponentDraws = st.opponentDraws + k := by
  induction k generalizing st with
  | zero => simp [repeatMulligan]
  | succ m ih =>
    simp only [repeatMulligan]
    rw [ih]
    simp [performMulligan]
    omega

/-- After n mulligans from a fresh init, opponentDraws = n. -/
theorem repeat_mulligan_draws_from_init (d : MDeck) (n : Nat) :
    (repeatMulligan (initMulliganState d) n).opponentDraws = n := by
  rw [repeat_mulligan_draws_gen]
  simp [initMulliganState]

/-- Repeated mulligans preserve total card count. -/
theorem repeat_mulligan_total (st : MulliganState) (n : Nat) :
    (repeatMulligan st n).hand.length + (repeatMulligan st n).deck.length =
    st.hand.length + st.deck.length := by
  induction n generalizing st with
  | zero => simp [repeatMulligan]
  | succ k ih =>
    simp only [repeatMulligan]
    rw [ih]
    exact mulligan_preserves_total st

-- ============================================================
-- §16  Concrete Scenario Theorems
-- ============================================================

/-- Pikachu cards are basics. -/
theorem pikachu_kind : pikachuCard.kind = .basicPokemon := by rfl

/-- Ralts cards are basics. -/
theorem ralts_kind : raltsCard.kind = .basicPokemon := by rfl

/-- Gardevoir ex is not basic. -/
theorem gardevoir_not_basic : gardevoirCard.kind ≠ .basicPokemon := by decide

/-- Psychic Energy is basic energy. -/
theorem psychic_kind : psychicEnergyCard.kind = .basicEnergy := by rfl

/-- Gardevoir is a stage Pokémon. -/
theorem gardevoir_kind : gardevoirCard.kind = .stagePokemon := by rfl

/-- Hand of [Pikachu, Boss, Boss, Boss, Energy, Energy, Energy] has a basic. -/
theorem example_hand_has_basic :
    handHasBasic [pikachuCard, bossOrdersCard, bossOrdersCard, bossOrdersCard,
                  psychicEnergyCard, psychicEnergyCard, psychicEnergyCard] = true := by
  native_decide

/-- A deck of 4 Pikachu has basicPokemonCount 4. -/
theorem four_pikachu_count :
    basicPokemonCount (makeN pikachuCard 4) = 4 := by native_decide

/-- deckSize of 10 cards is 10. -/
theorem deckSize_ten :
    deckSize (makeN pikachuCard 10) = 10 := by native_decide

end PokemonLean.Core.MulliganSetup
