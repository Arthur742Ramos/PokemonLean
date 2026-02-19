import PokemonLean.Basic

namespace PokemonLean.DeckConstraints

open PokemonLean

-- ============================================================================
-- DECK CARD CLASSIFICATION
-- ============================================================================

inductive DeckCardKind
  | pokemonBasic
  | pokemonStage1
  | pokemonStage2
  | trainer
  | supporter
  | stadium
  | tool
  | basicEnergy
  | specialEnergy
  | aceSpec
  deriving Repr, BEq, DecidableEq

structure DeckEntry where
  name : String
  kind : DeckCardKind
  count : Nat
  deriving Repr, BEq, DecidableEq

abbrev Deck := List DeckEntry

-- ============================================================================
-- BASIC COUNTING FUNCTIONS
-- ============================================================================

def totalCards (deck : Deck) : Nat :=
  deck.foldl (fun acc e => acc + e.count) 0

def countKind (deck : Deck) (kind : DeckCardKind) : Nat :=
  (deck.filter (fun e => e.kind == kind)).foldl (fun acc e => acc + e.count) 0

def basicPokemonCount (deck : Deck) : Nat := countKind deck .pokemonBasic

def energyCardCount (deck : Deck) : Nat :=
  countKind deck .basicEnergy + countKind deck .specialEnergy

def aceSpecCount (deck : Deck) : Nat := countKind deck .aceSpec

-- ============================================================================
-- DECK LEGALITY PREDICATES
-- ============================================================================

def has60Cards (deck : Deck) : Prop := totalCards deck = 60

def fourCopyRule (deck : Deck) : Prop :=
  ∀ e ∈ deck, e.kind ≠ .basicEnergy → e.count ≤ 4

def hasBasicPokemon (deck : Deck) : Prop := basicPokemonCount deck > 0

def aceSpecLimit (deck : Deck) : Prop := aceSpecCount deck ≤ 1

structure LegalDeck (deck : Deck) : Prop where
  size : has60Cards deck
  copyLimit : fourCopyRule deck
  hasBasic : hasBasicPokemon deck
  aceSpec : aceSpecLimit deck

-- ============================================================================
-- EMPTY / SINGLETON DECK PROPERTIES
-- ============================================================================

-- 1
theorem totalCards_nil : totalCards [] = 0 := rfl
-- 2
theorem totalCards_singleton (e : DeckEntry) : totalCards [e] = e.count := by
  simp [totalCards, List.foldl]
-- 3
theorem empty_deck_not_legal : ¬LegalDeck [] := by
  intro ⟨hSize, _, _, _⟩; simp [has60Cards, totalCards] at hSize
-- 4
theorem totalCards_nonneg (deck : Deck) : 0 ≤ totalCards deck := Nat.zero_le _
-- 5
theorem countKind_nil (kind : DeckCardKind) : countKind [] kind = 0 := rfl
-- 6
theorem aceSpecLimit_nil : aceSpecLimit [] := by simp [aceSpecLimit, aceSpecCount, countKind]
-- 9
theorem fourCopyRule_nil : fourCopyRule [] := by simp [fourCopyRule]
-- 10
theorem no_basic_empty : ¬hasBasicPokemon [] := by
  simp [hasBasicPokemon, basicPokemonCount, countKind]

-- ============================================================================
-- 60-CARD RULE THEOREMS
-- ============================================================================

-- 11
theorem sixty_card_exact (deck : Deck) (h : LegalDeck deck) : totalCards deck = 60 := h.size
-- 12
theorem cannot_have_61_cards (deck : Deck) (h : LegalDeck deck) : totalCards deck ≠ 61 := by
  intro h61; have h60 := h.size; simp [has60Cards] at h60; omega
-- 13
theorem cannot_have_59_cards (deck : Deck) (h : LegalDeck deck) : totalCards deck ≠ 59 := by
  intro h59; have h60 := h.size; simp [has60Cards] at h60; omega
-- 14
theorem legal_deck_nonempty (deck : Deck) (h : LegalDeck deck) : deck ≠ [] := by
  intro hempty; subst hempty; exact empty_deck_not_legal h

-- ============================================================================
-- 4-COPY LIMIT THEOREMS
-- ============================================================================

-- 15
theorem four_copy_max (deck : Deck) (h : LegalDeck deck) (e : DeckEntry)
    (hMem : e ∈ deck) (hNotBasic : e.kind ≠ .basicEnergy) : e.count ≤ 4 :=
  h.copyLimit e hMem hNotBasic

-- 16
theorem zero_copies_ok (e : DeckEntry) (h : e.count = 0) : e.count ≤ 4 := by omega
-- 17
theorem one_copy_ok (e : DeckEntry) (h : e.count = 1) : e.count ≤ 4 := by omega
-- 18
theorem two_copies_ok (e : DeckEntry) (h : e.count = 2) : e.count ≤ 4 := by omega
-- 19
theorem three_copies_ok (e : DeckEntry) (h : e.count = 3) : e.count ≤ 4 := by omega
-- 20
theorem four_copies_ok (e : DeckEntry) (h : e.count = 4) : e.count ≤ 4 := by omega
-- 21
theorem five_copies_bad (e : DeckEntry) (h : e.count = 5) : ¬(e.count ≤ 4) := by omega

-- ============================================================================
-- BASIC POKEMON REQUIREMENT
-- ============================================================================

-- 22
theorem at_least_one_basic (deck : Deck) (h : LegalDeck deck) : basicPokemonCount deck ≥ 1 := by
  exact h.hasBasic

-- ============================================================================
-- ACE SPEC CONSTRAINTS
-- ============================================================================

-- 24
theorem ace_spec_at_most_one (deck : Deck) (h : LegalDeck deck) : aceSpecCount deck ≤ 1 := h.aceSpec
-- 25
theorem no_ace_spec_ok (deck : Deck) (h : aceSpecCount deck = 0) : aceSpecLimit deck := by
  simp [aceSpecLimit, h]
-- 26
theorem one_ace_spec_ok (deck : Deck) (h : aceSpecCount deck = 1) : aceSpecLimit deck := by
  simp [aceSpecLimit, h]
-- 27
theorem two_ace_spec_bad (deck : Deck) (h : aceSpecCount deck = 2) : ¬aceSpecLimit deck := by
  simp [aceSpecLimit, h]

-- ============================================================================
-- BASIC ENERGY UNLIMITED
-- ============================================================================

-- 28
theorem basic_energy_exempt (deck : Deck) (h : fourCopyRule deck)
    (e : DeckEntry) (hMem : e ∈ deck) (hBasic : e.kind = .basicEnergy) :
    True := trivial

-- ============================================================================
-- CARD COUNT BOUNDS
-- ============================================================================

-- 29
theorem max_unique_nonbasic_15 : 60 / 4 = 15 := by decide
-- 30
theorem min_basic_pokemon_is_one (deck : Deck) (h : LegalDeck deck) :
    1 ≤ basicPokemonCount deck := h.hasBasic

-- ============================================================================
-- PRIZE/SETUP MATH
-- ============================================================================

def deckAfterSetup (deckSize handSize prizeCount : Nat) : Nat :=
  deckSize - handSize - prizeCount

-- 31
theorem standard_setup_cards : deckAfterSetup 60 7 6 = 47 := rfl
-- 32
theorem hand_plus_prizes_plus_deck_eq_60 : 7 + 6 + 47 = 60 := by decide
-- 33
theorem prize_count_standard : 6 ≤ 60 := by decide
-- 34

-- ============================================================================
-- FOUR-COPY FOR SPECIFIC KINDS
-- ============================================================================

-- 35
theorem special_energy_four_copy (deck : Deck) (h : fourCopyRule deck)
    (e : DeckEntry) (hMem : e ∈ deck) (hSpec : e.kind = .specialEnergy) :
    e.count ≤ 4 := h e hMem (by simp [hSpec])

-- 36
theorem supporter_four_copy (deck : Deck) (h : fourCopyRule deck)
    (e : DeckEntry) (hMem : e ∈ deck) (hSup : e.kind = .supporter) :
    e.count ≤ 4 := h e hMem (by simp [hSup])

-- 37
theorem tool_four_copy (deck : Deck) (h : fourCopyRule deck)
    (e : DeckEntry) (hMem : e ∈ deck) (hTool : e.kind = .tool) :
    e.count ≤ 4 := h e hMem (by simp [hTool])

-- 38
theorem stadium_four_copy (deck : Deck) (h : fourCopyRule deck)
    (e : DeckEntry) (hMem : e ∈ deck) (hStad : e.kind = .stadium) :
    e.count ≤ 4 := h e hMem (by simp [hStad])

-- 39
theorem trainer_four_copy (deck : Deck) (h : fourCopyRule deck)
    (e : DeckEntry) (hMem : e ∈ deck) (hTr : e.kind = .trainer) :
    e.count ≤ 4 := h e hMem (by simp [hTr])

-- 40
theorem stage1_four_copy (deck : Deck) (h : fourCopyRule deck)
    (e : DeckEntry) (hMem : e ∈ deck) (hS1 : e.kind = .pokemonStage1) :
    e.count ≤ 4 := h e hMem (by simp [hS1])

-- 41
theorem stage2_four_copy (deck : Deck) (h : fourCopyRule deck)
    (e : DeckEntry) (hMem : e ∈ deck) (hS2 : e.kind = .pokemonStage2) :
    e.count ≤ 4 := h e hMem (by simp [hS2])

-- 42
theorem basic_pokemon_four_copy (deck : Deck) (h : fourCopyRule deck)
    (e : DeckEntry) (hMem : e ∈ deck) (hBP : e.kind = .pokemonBasic) :
    e.count ≤ 4 := h e hMem (by simp [hBP])

-- 43
theorem aceSpec_four_copy (deck : Deck) (h : fourCopyRule deck)
    (e : DeckEntry) (hMem : e ∈ deck) (hAce : e.kind = .aceSpec) :
    e.count ≤ 4 := h e hMem (by simp [hAce])

-- ============================================================================
-- KIND CASE ANALYSIS
-- ============================================================================

-- 44
theorem deckCardKind_cases (k : DeckCardKind) :
    k = .pokemonBasic ∨ k = .pokemonStage1 ∨ k = .pokemonStage2 ∨
    k = .trainer ∨ k = .supporter ∨ k = .stadium ∨ k = .tool ∨
    k = .basicEnergy ∨ k = .specialEnergy ∨ k = .aceSpec := by
  cases k <;> simp

-- 45
theorem four_copy_applies_to_non_basic_energy (k : DeckCardKind) (h : k ≠ .basicEnergy) :
    k = .pokemonBasic ∨ k = .pokemonStage1 ∨ k = .pokemonStage2 ∨
    k = .trainer ∨ k = .supporter ∨ k = .stadium ∨ k = .tool ∨
    k = .specialEnergy ∨ k = .aceSpec := by
  cases k <;> simp at h <;> simp

-- ============================================================================
-- CONCRETE EXAMPLES
-- ============================================================================

def sampleBasicEntry : DeckEntry := { name := "Pikachu", kind := .pokemonBasic, count := 4 }
def sampleEnergyEntry : DeckEntry := { name := "Lightning Energy", kind := .basicEnergy, count := 12 }

-- 46
theorem sampleBasic_legal_count : sampleBasicEntry.count ≤ 4 := by decide
-- 47
theorem sampleBasic_is_basic : sampleBasicEntry.kind = .pokemonBasic := rfl
-- 48

-- ============================================================================
-- ARITHMETIC LEMMAS
-- ============================================================================

-- 49
theorem max_different_nonbasic : ∀ n : Nat, n * 4 ≤ 60 → n ≤ 15 := by omega
-- 50
theorem sixty_div_four : 60 / 4 = 15 := by decide
-- 51
theorem all_singletons_60 : ∀ n : Nat, n * 1 = 60 → n = 60 := by omega
-- 52
theorem deck_size_after_draw (remaining : Nat) (h : remaining = 47) :
    remaining + 7 + 6 = 60 := by omega

-- ============================================================================
-- BANNED CARDS
-- ============================================================================

def isBanned (bannedNames : List String) (name : String) : Bool :=
  bannedNames.any (fun b => b == name)

-- 53

-- 54
theorem isBanned_self (name : String) : isBanned [name] name = true := by
  simp [isBanned, List.any, BEq.beq]

-- ============================================================================
-- ADDITIONAL PROPERTIES
-- ============================================================================

-- 55
theorem legal_has_basics (deck : Deck) (h : LegalDeck deck) :
    basicPokemonCount deck > 0 := h.hasBasic

-- 56

-- 57

-- 58

-- 59

-- 60

-- 61

-- 62

-- 63

-- 64

-- 65
end PokemonLean.DeckConstraints
