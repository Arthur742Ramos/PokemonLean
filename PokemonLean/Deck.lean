import PokemonLean.Basic

namespace List
variable {α : Type _}

def countp (l : List α) (p : α → Prop) [DecidablePred p] : Nat :=
  l.countP (fun a => decide (p a))

@[simp] theorem countp_nil (p : α → Prop) [DecidablePred p] : ([] : List α).countp p = 0 := by
  simp [countp]
@[simp] theorem countp_cons (a : α) (l : List α) (p : α → Prop) [DecidablePred p] :
    (a :: l).countp p = (if p a then 1 else 0) + l.countp p := by
  by_cases h : p a <;> simp [countp, h, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem countp_le_length (l : List α) (p : α → Prop) [DecidablePred p] : l.countp p ≤ l.length := by
  simp [countp]
  induction l with
  | nil => simp
  | cons hd tl ih => simp [List.countP_cons]; split <;> omega
theorem countp_pos {l : List α} {p : α → Prop} [DecidablePred p] :
    0 < l.countp p ↔ ∃ a ∈ l, p a := by
  induction l with
  | nil =>
      simp [countp]
  | cons a l ih =>
      by_cases h : p a
      · constructor
        · intro _
          exact ⟨a, by simp, h⟩
        · intro _
          simp [countp_cons, h]
          omega
      · constructor
        · intro hpos
          have htail : 0 < l.countp p := by
            simpa [countp_cons, h] using hpos
          rcases ih.1 htail with ⟨b, hbmem, hpb⟩
          exact ⟨b, by simp [hbmem], hpb⟩
        · rintro ⟨b, hbmem, hpb⟩
          have hbTail : b ∈ l := by
            simp [List.mem_cons] at hbmem
            rcases hbmem with rfl | hbmem
            · exact (h hpb).elim
            · exact hbmem
          have htail : 0 < l.countp p := ih.2 ⟨b, hbTail, hpb⟩
          simpa [countp_cons, h] using htail

theorem Perm.countp_eq {l₁ l₂ : List α} (h : l₁.Perm l₂) (p : α → Prop) [DecidablePred p] :
    l₁.countp p = l₂.countp p := by
  simpa [countp] using h.countP_eq (p := fun a => decide (p a))

end List

namespace PokemonLean

/-- Count how many cards in `deck` have a given `name`. -/
def countByName (deck : List Card) (name : String) : Nat :=
  deck.countp (fun c => c.name = name)


/-- A simple notion of how many Pokemon cards (non-trainers) are present in a deck.

Note: in this simplified formalization, `isTrainer` is defined by `card.attacks.isEmpty`.
-/
def pokemonCount (deck : List Card) : Nat :=
  deck.countp (fun c => ¬ isTrainer c)


/-- A deck has at least one Pokemon card. -/
def hasPokemon (deck : List Card) : Prop := pokemonCount deck > 0

theorem hasPokemon_of_exists (deck : List Card) (c : Card) (hc : c ∈ deck) (hPok : ¬ isTrainer c) :
    hasPokemon deck := by
  unfold hasPokemon pokemonCount
  -- Count is positive if there is a witness satisfying the predicate.
  have : 0 < deck.countp (fun x => ¬ isTrainer x) := by
    exact List.countp_pos.2 ⟨c, hc, hPok⟩
  simpa using this

/-- Deck-building rules parameterized by a per-name maximum. -/
structure DeckRules where
  deckSize : Nat := standardDeckSize
  maxCopies : String → Nat := fun _ => 4
  requirePokemon : Bool := true

/-- A deck is valid with respect to rules if:

* it has the required size,
* it has at least one Pokemon card when required,
* for every name, the number of copies does not exceed the allowed maximum.

This is intentionally conservative: constraints like "unlimited basic energy" can be encoded
by choosing `maxCopies` appropriately.
-/
def deckValid (rules : DeckRules) (deck : List Card) : Prop :=
  deck.length = rules.deckSize ∧
  (if rules.requirePokemon then hasPokemon deck else True) ∧
  ∀ name : String, countByName deck name ≤ rules.maxCopies name

theorem deckValid_length (rules : DeckRules) (deck : List Card) (h : deckValid rules deck) :
    deck.length = rules.deckSize := h.1

theorem deckValid_countByName_le (rules : DeckRules) (deck : List Card) (name : String)
    (h : deckValid rules deck) :
    countByName deck name ≤ rules.maxCopies name :=
  h.2.2 name

theorem deckValid_hasPokemon (rules : DeckRules) (deck : List Card)
    (h : deckValid rules deck) (hReq : rules.requirePokemon = true) :
    hasPokemon deck := by
  have : (if rules.requirePokemon then hasPokemon deck else True) := h.2.1
  simpa [hReq] using this

/-- Default rules: 60 cards, max 4 per name, require at least one Pokemon. -/
def defaultDeckRules : DeckRules :=
  { deckSize := standardDeckSize
    maxCopies := fun _ => 4
    requirePokemon := true }

theorem deckValid_default_iff (deck : List Card) :
    deckValid defaultDeckRules deck ↔
      deck.length = standardDeckSize ∧ hasPokemon deck ∧ ∀ name, countByName deck name ≤ 4 := by
  simp [deckValid, defaultDeckRules]

/-- `countByName` is invariant under permutation of the deck. -/
theorem countByName_eq_of_perm {deck₁ deck₂ : List Card} (h : deck₁.Perm deck₂) (name : String) :
    countByName deck₁ name = countByName deck₂ name := by
  simpa [countByName] using (h.countp_eq (p := fun c : Card => c.name = name))

/-- `pokemonCount` is invariant under permutation of the deck. -/
theorem pokemonCount_eq_of_perm {deck₁ deck₂ : List Card} (h : deck₁.Perm deck₂) :
    pokemonCount deck₁ = pokemonCount deck₂ := by
  simpa [pokemonCount] using (h.countp_eq (p := fun c : Card => ¬ isTrainer c))

/-- Deck validity is invariant under permutation. -/
theorem deckValid_of_perm {rules : DeckRules} {deck₁ deck₂ : List Card}
    (hperm : deck₁.Perm deck₂) (h : deckValid rules deck₁) : deckValid rules deck₂ := by
  rcases h with ⟨hLen, hPok, hCounts⟩
  refine ⟨?_, ?_, ?_⟩
  · -- length is invariant under permutation
    have hl : deck₁.length = deck₂.length := hperm.length_eq
    calc
      deck₂.length = deck₁.length := by simpa using hl.symm
      _ = rules.deckSize := hLen
  · -- the "has a Pokemon" side condition is also permutation-invariant
    cases hReq : rules.requirePokemon with
    | false =>
        -- requirement disabled
        simpa [hReq] using hPok
    | true =>
        have hpok1 : hasPokemon deck₁ := by
          simpa [hReq] using hPok
        unfold hasPokemon at hpok1 ⊢
        have hpc : pokemonCount deck₂ = pokemonCount deck₁ := by
          simpa using (pokemonCount_eq_of_perm hperm).symm
        simpa [hpc] using hpok1
  · -- per-name copy bounds are permutation-invariant
    intro name
    have hEq : countByName deck₂ name = countByName deck₁ name := by
      simpa using (countByName_eq_of_perm hperm name).symm
    simpa [hEq] using (hCounts name)

/-- If a name is not present in the deck, then its count is 0. -/
theorem countByName_eq_zero_of_forall_ne (deck : List Card) (name : String)
    (h : ∀ c ∈ deck, c.name ≠ name) : countByName deck name = 0 := by
  induction deck with
  | nil => simp [countByName, List.countp]
  | cons c cs ih =>
    rw [countByName_cons]
    have hne := h c (List.Mem.head _)
    simp [hne]
    exact ih (fun c hc => h c (List.mem_cons_of_mem _ hc))

/-- Adding a card cannot decrease the count of any name. -/
theorem countByName_cons_ge (c : Card) (deck : List Card) (name : String) :
    countByName deck name ≤ countByName (c :: deck) name := by
  simp [countByName_cons]

/-- Adding a card increases the count of its own name by exactly 1. -/
theorem countByName_cons_self (c : Card) (deck : List Card) :
    countByName (c :: deck) c.name = countByName deck c.name + 1 := by
  -- the head contributes 1 for its own name
  simp [countByName_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- If a deck satisfies a max-copies rule, then adding a card of an already-saturated name breaks validity.

This lemma is useful for reasoning about deck-building constraints. -/
theorem deckValid_breaks_on_overflow (rules : DeckRules) (deck : List Card) (c : Card)
    (h : deckValid rules deck)
    (hSat : countByName deck c.name = rules.maxCopies c.name) :
    ¬ deckValid rules (c :: deck) := by
  intro h'
  have hBound := deckValid_countByName_le rules (c :: deck) c.name h'
  -- But the new count is old + 1.
  have hCount : countByName (c :: deck) c.name = rules.maxCopies c.name + 1 := by
    simp [countByName_cons_self, hSat, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  -- Contradiction: max+1 ≤ max.
  have hLe : rules.maxCopies c.name + 1 ≤ rules.maxCopies c.name := by
    simpa [hCount] using hBound
  have hContra : Nat.succ (rules.maxCopies c.name) ≤ rules.maxCopies c.name := by
    simpa [Nat.succ_eq_add_one] using hLe
  exact (Nat.not_succ_le_self (rules.maxCopies c.name)) hContra

end PokemonLean
