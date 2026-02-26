import PokemonLean.Core.Types
import Std.Tactic

namespace PokemonLean.DeckLegality

open PokemonLean.Core.Types

def isBasicPokemon (c : Card) : Bool :=
  c.kind == CardKind.pokemon && c.stage == some Stage.basic

def bannedCardNames : List String :=
  ["Lysandre's Trump Card", "Forest of Giant Plants", "Chip-Chip Ice Axe"]

def isBannedName (name : String) : Bool :=
  bannedCardNames.any (fun banned => banned == name)

def isBannedCard (c : Card) : Bool :=
  isBannedName c.name

def countByName (deck : List Card) (name : String) : Nat :=
  deck.countP (fun c => c.name == name)

def DeckLegal (deck : List Card) : Prop :=
  deck.length = 60 ∧
  (∀ c ∈ deck, c.isBasicEnergy = false → countByName deck c.name ≤ 4) ∧
  (∃ c ∈ deck, isBasicPokemon c = true) ∧
  (∀ c ∈ deck, isBannedCard c = false)

def checkDeckLegal (deck : List Card) : Bool :=
  (deck.length == 60) &&
    ((deck.all (fun c => c.isBasicEnergy || decide (countByName deck c.name ≤ 4))) &&
      ((deck.any isBasicPokemon) &&
        (deck.all (fun c => !isBannedCard c))))

theorem checkDeckLegal_sound (deck : List Card) :
    checkDeckLegal deck = true → DeckLegal deck := by
  intro h
  unfold checkDeckLegal at h
  have hLenAndRest :
      (deck.length == 60) = true ∧
        (deck.all (fun c => c.isBasicEnergy || decide (countByName deck c.name ≤ 4)) &&
          (deck.any isBasicPokemon && deck.all (fun c => !isBannedCard c))) = true := by
    exact Eq.mp (Bool.and_eq_true _ _) h
  have hLenBool := hLenAndRest.1
  have hRest := hLenAndRest.2
  have hCopyAndRest :
      deck.all (fun c => c.isBasicEnergy || decide (countByName deck c.name ≤ 4)) = true ∧
        (deck.any isBasicPokemon && deck.all (fun c => !isBannedCard c)) = true := by
    exact Eq.mp (Bool.and_eq_true _ _) hRest
  have hCopyBool := hCopyAndRest.1
  have hRest2 := hCopyAndRest.2
  have hBasicAndBanned :
      deck.any isBasicPokemon = true ∧
        deck.all (fun c => !isBannedCard c) = true := by
    exact Eq.mp (Bool.and_eq_true _ _) hRest2
  have hAnyBool := hBasicAndBanned.1
  have hBanBool := hBasicAndBanned.2

  have hLen : deck.length = 60 := (beq_iff_eq).1 hLenBool
  have hCopyRule : ∀ c ∈ deck, c.isBasicEnergy = false → countByName deck c.name ≤ 4 := by
    intro c hMem hNonBasic
    have hCard :
        (c.isBasicEnergy || decide (countByName deck c.name ≤ 4)) = true :=
      (List.all_eq_true).1 hCopyBool c hMem
    have hCountBool : decide (countByName deck c.name ≤ 4) = true := by
      simpa [hNonBasic] using hCard
    exact of_decide_eq_true hCountBool
  have hBasic : ∃ c ∈ deck, isBasicPokemon c = true := (List.any_eq_true).1 hAnyBool
  have hNoBanned : ∀ c ∈ deck, isBannedCard c = false := by
    intro c hMem
    have hCard : (!isBannedCard c) = true := (List.all_eq_true).1 hBanBool c hMem
    simpa using hCard
  exact ⟨hLen, hCopyRule, hBasic, hNoBanned⟩

theorem checkDeckLegal_complete (deck : List Card) :
    DeckLegal deck → checkDeckLegal deck = true := by
  intro hLegal
  rcases hLegal with ⟨hLen, hCopyRule, hBasic, hNoBanned⟩
  unfold checkDeckLegal
  have hLenBool : (deck.length == 60) = true := (beq_iff_eq).2 hLen
  have hCopyBool :
      deck.all (fun c => c.isBasicEnergy || decide (countByName deck c.name ≤ 4)) = true := by
    apply (List.all_eq_true).2
    intro c hMem
    by_cases hBasicEnergy : c.isBasicEnergy = true
    · simp [hBasicEnergy]
    · have hNonBasic : c.isBasicEnergy = false := by
        cases hCard : c.isBasicEnergy <;> simp [hCard] at hBasicEnergy ⊢
      have hCount : countByName deck c.name ≤ 4 := hCopyRule c hMem hNonBasic
      have hCountBool : decide (countByName deck c.name ≤ 4) = true := decide_eq_true hCount
      simp [hNonBasic, hCountBool]
  have hAnyBool : deck.any isBasicPokemon = true := (List.any_eq_true).2 hBasic
  have hBanBool : deck.all (fun c => !isBannedCard c) = true := by
    apply (List.all_eq_true).2
    intro c hMem
    have hNotBanned : isBannedCard c = false := hNoBanned c hMem
    simp [hNotBanned]
  have hRest2 :
      (deck.any isBasicPokemon && deck.all (fun c => !isBannedCard c)) = true := by
    exact Eq.mpr (Bool.and_eq_true _ _) ⟨hAnyBool, hBanBool⟩
  have hRest :
      (deck.all (fun c => c.isBasicEnergy || decide (countByName deck c.name ≤ 4)) &&
        (deck.any isBasicPokemon && deck.all (fun c => !isBannedCard c))) = true := by
    exact Eq.mpr (Bool.and_eq_true _ _) ⟨hCopyBool, hRest2⟩
  exact Eq.mpr (Bool.and_eq_true _ _) ⟨hLenBool, hRest⟩

theorem checkDeckLegal_iff (deck : List Card) :
    checkDeckLegal deck = true ↔ DeckLegal deck := by
  constructor
  · exact checkDeckLegal_sound deck
  · exact checkDeckLegal_complete deck

instance : DecidablePred DeckLegal := by
  intro deck
  by_cases h : checkDeckLegal deck = true
  · exact isTrue (checkDeckLegal_sound deck h)
  · exact isFalse (fun hLegal => h (checkDeckLegal_complete deck hLegal))

theorem deck_length_59_illegal (deck : List Card) (hLen : deck.length = 59) :
    ¬ DeckLegal deck := by
  intro hLegal
  have h60 : deck.length = 60 := hLegal.1
  omega

theorem deck_length_61_illegal (deck : List Card) (hLen : deck.length = 61) :
    ¬ DeckLegal deck := by
  intro hLegal
  have h60 : deck.length = 60 := hLegal.1
  omega

theorem no_basic_pokemon_illegal (deck : List Card)
    (hNoBasic : ∀ c ∈ deck, isBasicPokemon c = false) :
    ¬ DeckLegal deck := by
  intro hLegal
  rcases hLegal with ⟨_, _, hBasic, _⟩
  rcases hBasic with ⟨c, hMem, hIsBasic⟩
  have hNotBasic : isBasicPokemon c = false := hNoBasic c hMem
  simp [hNotBasic] at hIsBasic

theorem basicEnergy_exempt_from_four_copy_rule (deck : List Card) (c : Card)
    (hBasic : c.isBasicEnergy = true) :
    (c.isBasicEnergy = false → countByName deck c.name ≤ 4) ∧
      (c.isBasicEnergy || decide (countByName deck c.name ≤ 4)) = true := by
  constructor
  · intro hNonBasic
    simp [hBasic] at hNonBasic
  · simp [hBasic]

end PokemonLean.DeckLegality
