-- Mulligan Rules: Opening Hand, Basic Pokémon Checks, Reshuffle Logic
-- PokemonLean: 7-card draw, mulligan loop, hypergeometric probability bounds

import PokemonLean.Basic

namespace PokemonLean.Mulligan

-- ============================================================================
-- BASIC POKÉMON PREDICATES
-- ============================================================================

/-- A card is a basic Pokémon if it is not a trainer (i.e., it has attacks). -/
def isBasicPokemon (card : Card) : Bool :=
  !isTrainer card


theorem isBasicPokemon_of_attacks_nonempty (card : Card) (a : Attack) (as : List Attack)
    (h : card.attacks = a :: as) :
    isBasicPokemon card = true := by
  simp [isBasicPokemon, isTrainer, h, List.isEmpty]

theorem not_isBasicPokemon_of_attacks_empty (card : Card)
    (h : card.attacks = []) :
    isBasicPokemon card = false := by
  simp [isBasicPokemon, isTrainer, h, List.isEmpty]

/-- Count the number of basic Pokémon in a list of cards. -/
def basicCount (cards : List Card) : Nat :=
  cards.countP (fun c => isBasicPokemon c)

@[simp] theorem basicCount_nil : basicCount [] = 0 := rfl

theorem basicCount_cons (c : Card) (cs : List Card) :
    basicCount (c :: cs) = basicCount cs + (if isBasicPokemon c then 1 else 0) := by
  simp [basicCount, List.countP_cons]

theorem basicCount_cons_basic (c : Card) (cs : List Card) (h : isBasicPokemon c = true) :
    basicCount (c :: cs) = basicCount cs + 1 := by
  simp [basicCount_cons, h]

theorem basicCount_cons_nonbasic (c : Card) (cs : List Card) (h : isBasicPokemon c = false) :
    basicCount (c :: cs) = basicCount cs := by
  simp [basicCount_cons, h]

theorem basicCount_le_length (cards : List Card) : basicCount cards ≤ cards.length := by
  simp [basicCount]
  induction cards with
  | nil => simp
  | cons hd tl ih => simp [List.countP_cons]; split <;> omega
theorem basicCount_append (xs ys : List Card) :
    basicCount (xs ++ ys) = basicCount xs + basicCount ys := by
  simp [basicCount, List.countP_append]

/-- A hand has at least one basic Pokémon. -/
def hasBasic (hand : List Card) : Prop :=
  basicCount hand > 0

theorem hasBasic_iff_exists (hand : List Card) :
    hasBasic hand ↔ ∃ c, c ∈ hand ∧ isBasicPokemon c = true := by
  constructor
  · intro h
    induction hand with
    | nil => simp [hasBasic, basicCount] at h
    | cons x xs ih =>
      rw [hasBasic, basicCount_cons] at h
      by_cases hx : isBasicPokemon x
      · exact ⟨x, List.Mem.head xs, hx⟩
      · simp [hx] at h
        obtain ⟨c, hc, hp⟩ := ih h
        exact ⟨c, List.Mem.tail x hc, hp⟩
  · intro ⟨c, hc, hp⟩
    induction hand with
    | nil => cases hc
    | cons x xs ih =>
      rw [hasBasic, basicCount_cons]
      cases hc with
      | head => simp [hp]
      | tail _ hc =>
        have : hasBasic xs := ih hc
        rw [hasBasic] at this
        by_cases hx : isBasicPokemon x <;> simp [hx] <;> omega

theorem hasBasic_cons_basic (c : Card) (cs : List Card) (h : isBasicPokemon c = true) :
    hasBasic (c :: cs) := by
  rw [hasBasic_iff_exists]
  exact ⟨c, List.Mem.head cs, h⟩

theorem hasBasic_cons_of_tail (c : Card) (cs : List Card) (h : hasBasic cs) :
    hasBasic (c :: cs) := by
  rw [hasBasic, basicCount_cons]
  rw [hasBasic] at h
  by_cases hc : isBasicPokemon c <;> simp [hc] <;> omega

theorem not_hasBasic_nil : ¬hasBasic [] := by
  simp [hasBasic]

theorem not_hasBasic_iff (hand : List Card) :
    ¬hasBasic hand ↔ basicCount hand = 0 := by
  unfold hasBasic; omega

-- ============================================================================
-- INITIAL HAND SIZE
-- ============================================================================

/-- Standard initial hand size in Pokémon TCG. -/
def initialHandSize : Nat := 7

/-- Standard deck size. -/
def mulliganDeckSize : Nat := 60

-- ============================================================================
-- MULLIGAN STATE
-- ============================================================================

/-- State during the mulligan phase before the game begins. -/
structure MulliganState where
  /-- The full deck (shuffled). -/
  deck : List Card
  /-- The current hand (first 7 cards). -/
  hand : List Card
  /-- Number of mulligans taken so far. -/
  mulligans : Nat
  /-- Extra cards the opponent has drawn (one per mulligan). -/
  opponentExtras : Nat
  deriving Repr, BEq, DecidableEq

/-- Initial mulligan state from a shuffled deck. -/
def initMulligan (deck : List Card) : MulliganState :=
  { deck := deck
  , hand := deck.take initialHandSize
  , mulligans := 0
  , opponentExtras := 0 }


theorem initMulligan_hand_length (deck : List Card) (h : initialHandSize ≤ deck.length) :
    (initMulligan deck).hand.length = initialHandSize := by
  simp [initMulligan, List.length_take, Nat.min_eq_left h]

-- ============================================================================
-- MULLIGAN DECISION
-- ============================================================================

/-- Whether a mulligan is needed (no basic Pokémon in hand). -/
def needsMulligan (ms : MulliganState) : Bool :=
  basicCount ms.hand == 0

theorem needsMulligan_iff (ms : MulliganState) :
    needsMulligan ms = true ↔ ¬hasBasic ms.hand := by
  constructor
  · intro h; simp [needsMulligan] at h; rw [not_hasBasic_iff]; exact h
  · intro h; rw [not_hasBasic_iff] at h; simp [needsMulligan, h]

theorem needsMulligan_false_iff (ms : MulliganState) :
    needsMulligan ms = false ↔ hasBasic ms.hand := by
  unfold needsMulligan hasBasic
  constructor
  · intro h; simp at h; omega
  · intro h; simp; omega

/-- Perform one mulligan: reshuffle deck, redraw hand, increment counters. -/
def doMulligan (ms : MulliganState) (reshuffled : List Card) : MulliganState :=
  { deck := reshuffled
  , hand := reshuffled.take initialHandSize
  , mulligans := ms.mulligans + 1
  , opponentExtras := ms.opponentExtras + 1 }


theorem doMulligan_opponentExtras_eq_mulligans (ms : MulliganState)
    (reshuffled : List Card) (h : ms.opponentExtras = ms.mulligans) :
    (doMulligan ms reshuffled).opponentExtras = (doMulligan ms reshuffled).mulligans := by
  simp [doMulligan, h]


theorem doMulligan_hand_length (ms : MulliganState) (reshuffled : List Card)
    (h : initialHandSize ≤ reshuffled.length) :
    (doMulligan ms reshuffled).hand.length = initialHandSize := by
  simp [doMulligan, List.length_take, Nat.min_eq_left h]

-- ============================================================================
-- OPPONENT EXTRA CARDS TRACKING
-- ============================================================================


/-- After any number of mulligans, opponentExtras always equals mulligans. -/
theorem opponentExtras_eq_mulligans (ms : MulliganState)
    (h : ms.opponentExtras = ms.mulligans)
    (reshuffleds : List (List Card)) :
    let final := reshuffleds.foldl (fun acc r => doMulligan acc r) ms
    final.opponentExtras = final.mulligans := by
  induction reshuffleds generalizing ms with
  | nil => simpa using h
  | cons r rs ih =>
    simp [List.foldl]
    exact ih (doMulligan ms r) (doMulligan_opponentExtras_eq_mulligans ms r h)

-- ============================================================================
-- MULLIGAN COUNT TRACKING
-- ============================================================================

theorem mulligans_monotone (ms : MulliganState) (reshuffled : List Card) :
    ms.mulligans < (doMulligan ms reshuffled).mulligans := by
  simp [doMulligan]

theorem mulligans_after_n (ms : MulliganState) (reshuffleds : List (List Card)) :
    let final := reshuffleds.foldl (fun acc r => doMulligan acc r) ms
    final.mulligans = ms.mulligans + reshuffleds.length := by
  induction reshuffleds generalizing ms with
  | nil => simp
  | cons r rs ih =>
    simp [List.foldl]
    rw [ih (doMulligan ms r)]
    simp [doMulligan]; omega

-- ============================================================================
-- HAND BASIC COUNT PROPERTIES
-- ============================================================================

/-- A hand drawn from a deck can't have more basics than the deck. -/
theorem hand_basicCount_le_deck (deck : List Card) :
    basicCount (deck.take initialHandSize) ≤ basicCount deck := by
  have : basicCount (deck.take initialHandSize) + basicCount (deck.drop initialHandSize)
      = basicCount deck := by
    simp only [basicCount, ← List.countP_append, List.take_append_drop]
  omega

theorem hand_basicCount_le_handSize (deck : List Card) :
    basicCount (deck.take initialHandSize) ≤ initialHandSize := by
  have h1 := basicCount_le_length (deck.take initialHandSize)
  have h2 := List.length_take_le initialHandSize deck
  omega

-- ============================================================================
-- MULLIGAN LOOP TERMINATION
-- ============================================================================

/-- A deck is valid for play if it has the right size and at least one basic. -/
structure ValidDeck (deck : List Card) : Prop where
  hasSize : deck.length = mulliganDeckSize
  hasBasics : basicCount deck > 0

/-- Split property: basics are in the hand or the rest of the deck. -/
theorem deck_basics_preserved_by_take_drop (deck : List Card) :
    basicCount (deck.take initialHandSize) + basicCount (deck.drop initialHandSize) =
      basicCount deck := by
  simp only [basicCount, ← List.countP_append, List.take_append_drop]

/-- If the deck has basics, they must be in the hand portion or the remaining portion. -/
theorem basics_in_full_deck_means_basics_somewhere (deck : List Card)
    (h : basicCount deck > 0) :
    basicCount (deck.take initialHandSize) > 0 ∨
    basicCount (deck.drop initialHandSize) > 0 := by
  have := deck_basics_preserved_by_take_drop deck
  omega

-- ============================================================================
-- HYPERGEOMETRIC PROBABILITY BOUNDS (NATURAL NUMBER ARITHMETIC)
-- ============================================================================

/-- Binomial coefficient (choose n k). -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _+1 => 0
  | n+1, k+1 => choose n k + choose n (k+1)

@[simp] theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by
  cases n <;> simp [choose]

@[simp] theorem choose_zero_succ (k : Nat) : choose 0 (k + 1) = 0 := by
  simp [choose]

theorem choose_succ_succ (n k : Nat) :
    choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := by
  simp [choose]

/-- choose n k = 0 when k > n. -/
theorem choose_eq_zero_of_gt : ∀ (n k : Nat), n < k → choose n k = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk; cases k with
    | zero => omega
    | succ k => simp [choose]
  | succ n ih =>
    intro k hk; cases k with
    | zero => omega
    | succ k =>
      simp [choose]
      exact ⟨ih k (by omega), ih (k + 1) (by omega)⟩

theorem choose_self (n : Nat) : choose n n = 1 := by
  induction n with
  | zero => simp [choose]
  | succ n ih =>
    simp [choose, ih]
    exact choose_eq_zero_of_gt n (n + 1) (by omega)

theorem choose_one (n : Nat) : choose n 1 = n := by
  induction n with
  | zero => simp [choose]
  | succ n ih => simp [choose]; omega

theorem choose_pos_of_le : ∀ (n k : Nat), k ≤ n → choose n k > 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    have : k = 0 := Nat.eq_zero_of_le_zero hk
    subst this; simp [choose]
  | succ n ih =>
    intro k hk; cases k with
    | zero => simp [choose]
    | succ k =>
      simp [choose]
      exact Nat.lt_of_lt_of_le (ih k (by omega)) (Nat.le_add_right _ _)

/-- The number of ways to draw a hand with zero basics. -/
def waysNoBasic (totalCards basics handSize : Nat) : Nat :=
  choose (totalCards - basics) handSize

/-- Total ways to draw a hand of size h from N cards. -/
def waysTotal (totalCards handSize : Nat) : Nat :=
  choose totalCards handSize

theorem waysNoBasic_eq_waysTotal_when_no_basics (totalCards handSize : Nat) :
    waysNoBasic totalCards 0 handSize = waysTotal totalCards handSize := by
  simp [waysNoBasic, waysTotal]

/-- If the entire deck is basics, no-basic draw is impossible (for handSize > 0). -/
theorem no_mulligan_all_basics (totalCards handSize : Nat) (hPos : handSize > 0) :
    waysNoBasic totalCards totalCards handSize = 0 := by
  simp [waysNoBasic, Nat.sub_self]
  exact choose_eq_zero_of_gt 0 handSize hPos

/-- waysTotal is positive when handSize ≤ totalCards. -/
theorem waysTotal_pos (totalCards handSize : Nat) (h : handSize ≤ totalCards) :
    waysTotal totalCards handSize > 0 := by
  exact choose_pos_of_le totalCards handSize h

-- ============================================================================
-- ADDITIONAL THEOREMS
-- ============================================================================

theorem basicCount_singleton_basic (c : Card) (h : isBasicPokemon c = true) :
    basicCount [c] = 1 := by
  rw [basicCount_cons_basic c [] h]; simp

theorem basicCount_singleton_nonbasic (c : Card) (h : isBasicPokemon c = false) :
    basicCount [c] = 0 := by
  rw [basicCount_cons_nonbasic c [] h]; simp

theorem hasBasic_of_basicCount_pos (hand : List Card) (h : basicCount hand > 0) :
    hasBasic hand := h

theorem not_hasBasic_of_basicCount_zero (hand : List Card) (h : basicCount hand = 0) :
    ¬hasBasic hand := by
  rw [not_hasBasic_iff]; exact h

/-- A hand drawn from a deck can't have more basics than the deck (general). -/
theorem drawn_basics_le_deck_basics (deck : List Card) (n : Nat) :
    basicCount (deck.take n) ≤ basicCount deck := by
  have : basicCount (deck.take n) + basicCount (deck.drop n) = basicCount deck := by
    simp only [basicCount, ← List.countP_append, List.take_append_drop]
  omega

/-- After a mulligan, the mulligan count is positive. -/
theorem mulligan_count_pos_after_mulligan (ms : MulliganState) (reshuffled : List Card) :
    (doMulligan ms reshuffled).mulligans > 0 := by
  simp [doMulligan]

/-- The initial state never needs a mulligan if the first 7 cards contain a basic. -/
theorem no_mulligan_if_hand_has_basic (deck : List Card)
    (h : hasBasic (deck.take initialHandSize)) :
    needsMulligan (initMulligan deck) = false := by
  rw [needsMulligan_false_iff]
  show hasBasic (initMulligan deck).hand
  simp only [initMulligan]
  exact h

/-- A mulligan is needed iff the hand has no basics. -/
theorem mulligan_needed_iff_no_basic (ms : MulliganState) :
    needsMulligan ms = true ↔ basicCount ms.hand = 0 := by
  rw [needsMulligan_iff, not_hasBasic_iff]

/-- If the deck has basics and the hand has all cards, hand has basics. -/
theorem hasBasic_of_take_all (deck : List Card)
    (h : basicCount deck > 0) (hLen : deck.length ≤ initialHandSize) :
    hasBasic (deck.take initialHandSize) := by
  rw [List.take_of_length_le hLen]; exact h

/-- Guaranteed mulligan when deck has no basics. -/
theorem guaranteed_mulligan_no_basics (deck : List Card)
    (h : basicCount deck = 0) :
    needsMulligan (initMulligan deck) = true := by
  rw [mulligan_needed_iff_no_basic]
  simp [initMulligan]
  have := drawn_basics_le_deck_basics deck initialHandSize
  omega

end PokemonLean.Mulligan
