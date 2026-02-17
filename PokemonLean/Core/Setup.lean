/-
  PokemonLean / Core / Setup.lean

  Pokémon TCG game setup procedure formalised in Lean 4.
  Self-contained: defines deck, hand, mulligan loop, bench placement,
  prize setup, coin flip for first player, and first-turn restriction.

  Setup procedure:
    1. Each player shuffles a 60-card deck
    2. Draw 7 cards for opening hand
    3. Check for Basic Pokémon — if none, mulligan (shuffle, redraw,
       opponent may draw 1)
    4. Place 1 Basic face-down as active
    5. Place up to 5 Basics face-down on bench
    6. Set aside top 6 cards as prizes (face-down)
    7. Flip coin for who goes first
    8. First player can't attack on their first turn

  All proofs are sorry-free.  31 theorems.
-/

namespace PokemonLean.Core.Setup

-- ============================================================
-- §1  Core Types
-- ============================================================

/-- Card classification for setup purposes. -/
inductive CardKind where
  | basicPokemon   -- can be placed as active or bench
  | otherPokemon   -- stage 1, stage 2, etc.
  | trainer
  | energy
  deriving DecidableEq, Repr

/-- A card with an id and kind. -/
structure Card where
  id   : Nat
  kind : CardKind
  deriving DecidableEq, Repr

/-- Coin flip result. -/
inductive Coin where
  | heads | tails
  deriving DecidableEq, Repr

/-- Whether a card is a Basic Pokémon. -/
def Card.isBasic (c : Card) : Bool :=
  c.kind == .basicPokemon

-- ============================================================
-- §2  Deck Definition
-- ============================================================

/-- Standard deck size. -/
def deckSize : Nat := 60

/-- Opening hand size. -/
def handSize : Nat := 7

/-- Prize count. -/
def prizeCount : Nat := 6

/-- Max bench size. -/
def maxBench : Nat := 5

/-- A deck is a list of exactly 60 cards. -/
structure Deck where
  cards : List Card
  size_ok : cards.length = deckSize
  deriving Repr

-- ============================================================
-- §3  Drawing Cards
-- ============================================================

/-- Draw n cards from the top of a list. Returns (drawn, remaining). -/
def drawCards (cards : List Card) (n : Nat) : List Card × List Card :=
  (cards.take n, cards.drop n)

/-- Draw an opening hand of 7 cards. -/
def drawOpeningHand (cards : List Card) : List Card × List Card :=
  drawCards cards handSize

/-- Count the number of Basics in a hand. -/
def countBasics (hand : List Card) : Nat :=
  (hand.filter Card.isBasic).length

/-- Whether a hand contains at least one Basic. -/
def hasBasic (hand : List Card) : Bool :=
  countBasics hand > 0

-- ============================================================
-- §4  Mulligan
-- ============================================================

/-- Mulligan result: the hand after mulligan and how many mulligans occurred. -/
structure MulliganResult where
  hand           : List Card
  remainingDeck  : List Card
  mulliganCount  : Nat
  deriving Repr

/-- Iterative mulligan: given a sequence of deck orderings (one per shuffle),
    keep redrawing until we get a Basic. Bounded by fuel. -/
def mulliganLoop (fuel : Nat) (deckOrders : List (List Card))
    (count : Nat) : MulliganResult :=
  match fuel with
  | 0 =>
    match deckOrders with
    | order :: _ =>
      ⟨(drawOpeningHand order).1, (drawOpeningHand order).2, count⟩
    | [] => ⟨[], [], count⟩
  | fuel' + 1 =>
    match deckOrders with
    | order :: rest =>
      if hasBasic (drawOpeningHand order).1 then
        ⟨(drawOpeningHand order).1, (drawOpeningHand order).2, count⟩
      else
        mulliganLoop fuel' rest (count + 1)
    | [] => ⟨[], [], count⟩

-- ============================================================
-- §5  Bench Placement
-- ============================================================

/-- Extract Basic Pokémon from hand. Returns (basics, nonBasics). -/
def partitionBasics (hand : List Card) : List Card × List Card :=
  (hand.filter Card.isBasic, hand.filter (fun c => !c.isBasic))

/-- Choose active and bench from basics.
    First basic becomes active, up to 5 more go to bench.
    Returns (active, bench, remainingHand). -/
def placeBasics (hand : List Card) (benchCount : Nat) :
    Option Card × List Card × List Card :=
  let (basics, nonBasics) := partitionBasics hand
  match basics with
  | [] => (none, [], hand)
  | active :: rest =>
    let benchCards := rest.take (min benchCount maxBench)
    let unusedBasics := rest.drop (min benchCount maxBench)
    (some active, benchCards, unusedBasics ++ nonBasics)

-- ============================================================
-- §6  Prize Setup
-- ============================================================

/-- Set aside top 6 cards from deck as prizes. -/
def setPrizes (deck : List Card) : List Card × List Card :=
  drawCards deck prizeCount

-- ============================================================
-- §7  Player Setup State
-- ============================================================

/-- Complete setup state for one player. -/
structure PlayerSetup where
  active         : Option Card
  bench          : List Card
  hand           : List Card
  deck           : List Card
  prizes         : List Card
  mulliganCount  : Nat
  deriving Repr

/-- Total cards across all zones for a player. -/
def PlayerSetup.totalCards (ps : PlayerSetup) : Nat :=
  (if ps.active.isSome then 1 else 0) +
  ps.bench.length + ps.hand.length + ps.deck.length + ps.prizes.length

-- ============================================================
-- §8  First Player / Turn Order
-- ============================================================

/-- Which player goes first. -/
inductive FirstPlayer where
  | player1
  | player2
  deriving DecidableEq, Repr

/-- Determine first player from coin flip. -/
def determineFirstPlayer (flip : Coin) : FirstPlayer :=
  match flip with
  | .heads => .player1
  | .tails => .player2

/-- First-turn restriction: the player going first cannot attack on turn 1. -/
structure TurnRestriction where
  isFirstPlayer : Bool
  turnNumber    : Nat
  deriving DecidableEq, Repr

/-- Whether attack is allowed given restrictions. -/
def TurnRestriction.canAttack (tr : TurnRestriction) : Bool :=
  !(tr.isFirstPlayer && tr.turnNumber == 1)

-- ============================================================
-- §9  Full Setup Execution
-- ============================================================

/-- Execute full setup for one player given their deck order
    and number of basics to bench. -/
def executeSetup (deckOrder : List Card) (benchCount : Nat)
    (_ : deckOrder.length = deckSize) : PlayerSetup :=
  let (hand, afterHand) := drawOpeningHand deckOrder
  let (active, bench, remainingHand) := placeBasics hand benchCount
  let (prizes, finalDeck) := setPrizes afterHand
  { active := active
    bench := bench
    hand := remainingHand
    deck := finalDeck
    prizes := prizes
    mulliganCount := 0 }

-- ============================================================
-- §10  Game Setup State (Both Players)
-- ============================================================

/-- Full game setup state. -/
structure GameSetup where
  player1     : PlayerSetup
  player2     : PlayerSetup
  firstPlayer : FirstPlayer
  deriving Repr

-- ============================================================
-- §11  Helper Lemmas
-- ============================================================

private theorem filter_complement_length (l : List Card) (f : Card → Bool) :
    (l.filter f).length + (l.filter (fun c => !f c)).length = l.length := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter_cons]
    split <;> simp_all <;> omega

-- ============================================================
-- §12  Theorems — Deck and Hand Sizes
-- ============================================================

/-- Theorem 1: Drawing 7 from a 60-card deck gives a hand of 7. -/
theorem opening_hand_size (d : Deck) :
    (drawOpeningHand d.cards).1.length = handSize := by
  simp [drawOpeningHand, drawCards, List.length_take, d.size_ok, handSize, deckSize]

/-- Theorem 2: After drawing 7, 53 cards remain. -/
theorem remaining_after_draw (d : Deck) :
    (drawOpeningHand d.cards).2.length = 53 := by
  simp [drawOpeningHand, drawCards, List.length_drop, d.size_ok, handSize, deckSize]

/-- Theorem 3: Drawing preserves total count. -/
theorem draw_preserves_count (d : Deck) :
    (drawOpeningHand d.cards).1.length + (drawOpeningHand d.cards).2.length = deckSize := by
  simp [drawOpeningHand, drawCards, List.length_take, List.length_drop, d.size_ok, deckSize,
        handSize]

/-- Theorem 4: Prize setup takes exactly 6 cards when deck is large enough. -/
theorem prize_count_exact (deck : List Card) (h : deck.length ≥ prizeCount) :
    (setPrizes deck).1.length = prizeCount := by
  have : prizeCount = 6 := rfl
  rw [this] at h ⊢
  simp [setPrizes, drawCards, List.length_take]
  omega

/-- Theorem 5: Prize setup preserves total. -/
theorem prize_preserves_total (deck : List Card) :
    (setPrizes deck).1.length + (setPrizes deck).2.length = deck.length := by
  simp [setPrizes, drawCards, List.length_take, List.length_drop]
  omega

-- ============================================================
-- §13  Theorems — Mulligan
-- ============================================================

/-- Theorem 6: If the initial hand has a Basic, no mulligan occurs. -/
theorem no_mulligan_if_basic (order : List Card) (rest : List (List Card))
    (h_basic : hasBasic (drawOpeningHand order).1 = true) :
    (mulliganLoop 100 (order :: rest) 0).mulliganCount = 0 := by
  simp [mulliganLoop, h_basic]

/-- Theorem 7: Mulligan increments count. -/
theorem mulligan_increments (fuel : Nat) (order : List Card) (rest : List (List Card))
    (n : Nat) (h_no_basic : hasBasic (drawOpeningHand order).1 = false) :
    (mulliganLoop (fuel + 1) (order :: rest) n).mulliganCount =
    (mulliganLoop fuel rest (n + 1)).mulliganCount := by
  simp [mulliganLoop, h_no_basic]

/-- Theorem 8: countBasics of empty hand is 0. -/
theorem no_basics_empty : countBasics [] = 0 := by rfl

/-- Theorem 9: A hand with only non-basics has countBasics = 0. -/
theorem non_basics_count_zero (hand : List Card)
    (h : ∀ c ∈ hand, c.isBasic = false) :
    countBasics hand = 0 := by
  simp [countBasics, List.filter_eq_nil_iff]
  intro a ha
  simp [h a ha]

/-- Theorem 10: hasBasic is equivalent to countBasics > 0. -/
theorem has_basic_iff (hand : List Card) :
    hasBasic hand = true ↔ countBasics hand > 0 := by
  simp [hasBasic]

-- ============================================================
-- §14  Theorems — Bench Placement
-- ============================================================

/-- Theorem 11: Bench size is at most maxBench (5). -/
theorem bench_at_most_five (hand : List Card) (n : Nat) :
    (placeBasics hand n).2.1.length ≤ maxBench := by
  simp [placeBasics, partitionBasics]
  cases h : List.filter Card.isBasic hand with
  | nil => simp
  | cons hd tl => simp [List.length_take]; omega

/-- Theorem 12: If hand has no basics, active is none. -/
theorem no_basics_no_active (hand : List Card) (n : Nat)
    (h : hand.filter Card.isBasic = []) :
    (placeBasics hand n).1 = none := by
  simp [placeBasics, partitionBasics, h]

/-- Theorem 13: If hand has at least one basic, active is some. -/
theorem basic_gives_active (hand : List Card) (n : Nat)
    (h : ∃ c, c ∈ hand ∧ c.isBasic = true) :
    (placeBasics hand n).1.isSome = true := by
  simp [placeBasics, partitionBasics]
  obtain ⟨c, hc_mem, hc_basic⟩ := h
  have hc_filter : c ∈ hand.filter Card.isBasic := by
    rw [List.mem_filter]
    exact ⟨hc_mem, hc_basic⟩
  cases hfilt : List.filter Card.isBasic hand with
  | nil => simp [hfilt] at hc_filter
  | cons hd tl => simp

-- ============================================================
-- §15  Theorems — First Player
-- ============================================================

/-- Theorem 14: Heads means player 1 goes first. -/
theorem heads_player1 : determineFirstPlayer .heads = .player1 := by rfl

/-- Theorem 15: Tails means player 2 goes first. -/
theorem tails_player2 : determineFirstPlayer .tails = .player2 := by rfl

/-- Theorem 16: First player can't attack on turn 1. -/
theorem first_player_no_attack_turn1 :
    TurnRestriction.canAttack ⟨true, 1⟩ = false := by rfl

/-- Theorem 17: First player CAN attack on turn 2+. -/
theorem first_player_attacks_turn2 :
    TurnRestriction.canAttack ⟨true, 2⟩ = true := by rfl

/-- Theorem 18: Second player CAN attack on turn 1. -/
theorem second_player_attacks_turn1 :
    TurnRestriction.canAttack ⟨false, 1⟩ = true := by rfl

/-- Theorem 19: Non-first-player can always attack. -/
theorem non_first_always_attacks (n : Nat) :
    TurnRestriction.canAttack ⟨false, n⟩ = true := by
  simp [TurnRestriction.canAttack]

-- ============================================================
-- §16  Theorems — Setup Invariants
-- ============================================================

/-- Theorem 20: After setup with deck of 60, prizes have 6 cards. -/
theorem setup_prizes_six (deckOrder : List Card) (benchCount : Nat)
    (h : deckOrder.length = deckSize) :
    (executeSetup deckOrder benchCount h).prizes.length = prizeCount := by
  have hp : prizeCount = 6 := rfl
  have hd : deckSize = 60 := rfl
  have hh : handSize = 7 := rfl
  rw [hp]
  simp [executeSetup, setPrizes, drawCards, drawOpeningHand,
        List.length_take, List.length_drop, h, hd, hh]
  omega

/-- Theorem 21: Standard constants are correct. -/
theorem deck_is_60 : deckSize = 60 := by rfl
theorem hand_is_7 : handSize = 7 := by rfl
theorem prizes_is_6 : prizeCount = 6 := by rfl
theorem bench_is_5 : maxBench = 5 := by rfl

/-- Theorem 22: Coin flip is binary — exactly two outcomes. -/
theorem coin_binary (c : Coin) : c = .heads ∨ c = .tails := by
  cases c <;> simp

/-- Theorem 23: determineFirstPlayer is surjective. -/
theorem first_player_surjective (fp : FirstPlayer) :
    ∃ c : Coin, determineFirstPlayer c = fp := by
  cases fp
  · exact ⟨.heads, rfl⟩
  · exact ⟨.tails, rfl⟩

/-- Theorem 24: After drawing 7 from 60, remaining deck ≥ prizeCount. -/
theorem enough_for_prizes (d : Deck) :
    (drawOpeningHand d.cards).2.length ≥ prizeCount := by
  have : prizeCount = 6 := rfl
  rw [this]
  simp [drawOpeningHand, drawCards, List.length_drop, d.size_ok, handSize, deckSize]

/-- Theorem 25: Partitioning hand preserves length. -/
theorem partition_preserves_length (hand : List Card) :
    (partitionBasics hand).1.length + (partitionBasics hand).2.length = hand.length := by
  exact filter_complement_length hand Card.isBasic

/-- Theorem 26: countBasics ≤ hand length. -/
theorem basics_le_hand (hand : List Card) :
    countBasics hand ≤ hand.length := by
  simp [countBasics]
  exact List.length_filter_le _ _

/-- Theorem 27: A singleton basic hand has exactly 1 basic. -/
theorem singleton_basic_count (c : Card) (h : c.isBasic = true) :
    countBasics [c] = 1 := by
  simp [countBasics, h]

/-- Theorem 28: An all-basic hand of length n has n basics. -/
theorem all_basics_count (hand : List Card)
    (h : ∀ c ∈ hand, c.isBasic = true) :
    countBasics hand = hand.length := by
  simp only [countBasics, List.filter_eq_self.mpr h]

/-- Theorem 29: First player restriction is only for turn 1. -/
theorem restriction_only_turn1 (n : Nat) (h : n ≠ 1) :
    TurnRestriction.canAttack ⟨true, n⟩ = true := by
  simp [TurnRestriction.canAttack]
  omega

/-- Theorem 30: Mulligan count from mulliganLoop is at least the initial count. -/
theorem mulligan_count_ge_initial (fuel : Nat) (orders : List (List Card)) (n : Nat) :
    (mulliganLoop fuel orders n).mulliganCount ≥ n := by
  induction fuel generalizing orders n with
  | zero =>
    cases orders with
    | nil => simp [mulliganLoop]
    | cons order rest => simp [mulliganLoop]
  | succ k ih =>
    cases orders with
    | nil => simp [mulliganLoop]
    | cons order rest =>
      simp only [mulliganLoop]
      split
      · simp
      · exact Nat.le_trans (Nat.le_succ n) (ih rest (n + 1))

/-- Theorem 31: drawCards with n=0 returns empty drawn list. -/
theorem draw_zero (l : List Card) : (drawCards l 0).1 = [] := by
  simp [drawCards]

end PokemonLean.Core.Setup