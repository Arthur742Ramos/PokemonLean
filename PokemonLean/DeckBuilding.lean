import PokemonLean.Basic
import PokemonLean.Core.Types
import PokemonLean.Archetypes

namespace PokemonLean.DeckBuilding

/-- High-level deck-building categories. -/
inductive CardCategory
  | pokemon
  | trainer
  | energy
  deriving Repr, BEq, DecidableEq

/-- Deck-facing card metadata used for deck-construction legality checks. -/
structure DeckCard where
  card : Card
  category : CardCategory
  isBasicPokemon : Bool := false
  isBasicEnergy : Bool := false
  isAceSpec : Bool := false
  isPrismStar : Bool := false
  isDrawSupporter : Bool := false
  isPokemonSearch : Bool := false
  deriving Repr, BEq, DecidableEq

/-- Count copies by card name. -/
def countByName (deck : List DeckCard) (name : String) : Nat :=
  deck.countP (fun c => c.card.name == name)

@[simp] theorem countByName_nil (name : String) : countByName [] name = 0 := by
  simp [countByName]

@[simp] theorem countByName_cons (c : DeckCard) (deck : List DeckCard) (name : String) :
    countByName (c :: deck) name = (if c.card.name == name then 1 else 0) + countByName deck name := by
  simp [countByName, List.countP_cons, Nat.add_comm]

theorem countByName_le_length (deck : List DeckCard) (name : String) :
    countByName deck name ≤ deck.length := by
  simpa [countByName] using
    (List.countP_le_length (p := fun c : DeckCard => c.card.name == name) (l := deck))

/-- Number of Pokemon cards. -/
def pokemonCount (deck : List DeckCard) : Nat :=
  deck.countP (fun c => c.category == .pokemon)

@[simp] theorem pokemonCount_nil : pokemonCount [] = 0 := by
  simp [pokemonCount]

@[simp] theorem pokemonCount_cons (c : DeckCard) (deck : List DeckCard) :
    pokemonCount (c :: deck) = (if c.category == .pokemon then 1 else 0) + pokemonCount deck := by
  simp [pokemonCount, List.countP_cons, Nat.add_comm]

theorem pokemonCount_le_length (deck : List DeckCard) : pokemonCount deck ≤ deck.length := by
  simpa [pokemonCount] using
    (List.countP_le_length (p := fun c : DeckCard => c.category == .pokemon) (l := deck))

/-- Number of Trainer cards. -/
def trainerCount (deck : List DeckCard) : Nat :=
  deck.countP (fun c => c.category == .trainer)

@[simp] theorem trainerCount_nil : trainerCount [] = 0 := by
  simp [trainerCount]

@[simp] theorem trainerCount_cons (c : DeckCard) (deck : List DeckCard) :
    trainerCount (c :: deck) = (if c.category == .trainer then 1 else 0) + trainerCount deck := by
  simp [trainerCount, List.countP_cons, Nat.add_comm]

theorem trainerCount_le_length (deck : List DeckCard) : trainerCount deck ≤ deck.length := by
  simpa [trainerCount] using
    (List.countP_le_length (p := fun c : DeckCard => c.category == .trainer) (l := deck))

/-- Number of Energy cards. -/
def energyCount (deck : List DeckCard) : Nat :=
  deck.countP (fun c => c.category == .energy)

@[simp] theorem energyCount_nil : energyCount [] = 0 := by
  simp [energyCount]

@[simp] theorem energyCount_cons (c : DeckCard) (deck : List DeckCard) :
    energyCount (c :: deck) = (if c.category == .energy then 1 else 0) + energyCount deck := by
  simp [energyCount, List.countP_cons, Nat.add_comm]

theorem energyCount_le_length (deck : List DeckCard) : energyCount deck ≤ deck.length := by
  simpa [energyCount] using
    (List.countP_le_length (p := fun c : DeckCard => c.category == .energy) (l := deck))

/-- Number of basic Pokemon cards. -/
def basicPokemonCount (deck : List DeckCard) : Nat :=
  deck.countP (fun c => c.category == .pokemon && c.isBasicPokemon)

@[simp] theorem basicPokemonCount_nil : basicPokemonCount [] = 0 := by
  simp [basicPokemonCount]

@[simp] theorem basicPokemonCount_cons (c : DeckCard) (deck : List DeckCard) :
    basicPokemonCount (c :: deck) =
      (if c.category == .pokemon && c.isBasicPokemon then 1 else 0) + basicPokemonCount deck := by
  simp [basicPokemonCount, List.countP_cons, Nat.add_comm]

theorem basicPokemonCount_le_length (deck : List DeckCard) :
    basicPokemonCount deck ≤ deck.length := by
  simpa [basicPokemonCount] using
    (List.countP_le_length (p := fun c : DeckCard => c.category == .pokemon && c.isBasicPokemon)
      (l := deck))

/-- Number of draw-supporter cards. -/
def drawSupporterCount (deck : List DeckCard) : Nat :=
  deck.countP (fun c => c.isDrawSupporter)

@[simp] theorem drawSupporterCount_nil : drawSupporterCount [] = 0 := by
  simp [drawSupporterCount]

@[simp] theorem drawSupporterCount_cons (c : DeckCard) (deck : List DeckCard) :
    drawSupporterCount (c :: deck) =
      (if c.isDrawSupporter then 1 else 0) + drawSupporterCount deck := by
  simp [drawSupporterCount, List.countP_cons, Nat.add_comm]

theorem drawSupporterCount_le_length (deck : List DeckCard) :
    drawSupporterCount deck ≤ deck.length := by
  simpa [drawSupporterCount] using
    (List.countP_le_length (p := fun c : DeckCard => c.isDrawSupporter) (l := deck))

/-- Number of Pokemon-search cards. -/
def pokemonSearchCount (deck : List DeckCard) : Nat :=
  deck.countP (fun c => c.isPokemonSearch)

@[simp] theorem pokemonSearchCount_nil : pokemonSearchCount [] = 0 := by
  simp [pokemonSearchCount]

@[simp] theorem pokemonSearchCount_cons (c : DeckCard) (deck : List DeckCard) :
    pokemonSearchCount (c :: deck) =
      (if c.isPokemonSearch then 1 else 0) + pokemonSearchCount deck := by
  simp [pokemonSearchCount, List.countP_cons, Nat.add_comm]

theorem pokemonSearchCount_le_length (deck : List DeckCard) :
    pokemonSearchCount deck ≤ deck.length := by
  simpa [pokemonSearchCount] using
    (List.countP_le_length (p := fun c : DeckCard => c.isPokemonSearch) (l := deck))

/-- Number of ACE SPEC cards. -/
def aceSpecCount (deck : List DeckCard) : Nat :=
  deck.countP (fun c => c.isAceSpec)

@[simp] theorem aceSpecCount_nil : aceSpecCount [] = 0 := by
  simp [aceSpecCount]

@[simp] theorem aceSpecCount_cons (c : DeckCard) (deck : List DeckCard) :
    aceSpecCount (c :: deck) = (if c.isAceSpec then 1 else 0) + aceSpecCount deck := by
  simp [aceSpecCount, List.countP_cons, Nat.add_comm]

theorem aceSpecCount_le_length (deck : List DeckCard) : aceSpecCount deck ≤ deck.length := by
  simpa [aceSpecCount] using
    (List.countP_le_length (p := fun c : DeckCard => c.isAceSpec) (l := deck))

/-- Prism Star copies by card name. -/
def prismStarCountByName (deck : List DeckCard) (name : String) : Nat :=
  deck.countP (fun c => c.isPrismStar && c.card.name == name)

@[simp] theorem prismStarCountByName_nil (name : String) :
    prismStarCountByName [] name = 0 := by
  simp [prismStarCountByName]

@[simp] theorem prismStarCountByName_cons (c : DeckCard) (deck : List DeckCard) (name : String) :
    prismStarCountByName (c :: deck) name =
      (if c.isPrismStar && c.card.name == name then 1 else 0) + prismStarCountByName deck name := by
  simp [prismStarCountByName, List.countP_cons, Nat.add_comm]

theorem prismStarCountByName_le_length (deck : List DeckCard) (name : String) :
    prismStarCountByName deck name ≤ deck.length := by
  simpa [prismStarCountByName] using
    (List.countP_le_length (p := fun c : DeckCard => c.isPrismStar && c.card.name == name) (l := deck))

/-- Rule: a deck must contain exactly 60 cards. -/
def hasSixtyCards (deck : List DeckCard) : Prop :=
  deck.length = standardDeckSize

theorem hasSixtyCards_iff (deck : List DeckCard) :
    hasSixtyCards deck ↔ deck.length = standardDeckSize := Iff.rfl

theorem hasSixtyCards_of_length_eq (deck : List DeckCard)
    (h : deck.length = standardDeckSize) : hasSixtyCards deck := h

theorem length_eq_standardDeckSize_of_hasSixtyCards (deck : List DeckCard)
    (h : hasSixtyCards deck) : deck.length = standardDeckSize := h

/-- Name-based copy limit with a basic-energy exception. -/
def copyLimitFor (c : DeckCard) : Nat :=
  if c.category = .energy ∧ c.isBasicEnergy = true then standardDeckSize else 4

theorem copyLimitFor_basicEnergy (c : DeckCard)
    (h : c.category = .energy ∧ c.isBasicEnergy = true) :
    copyLimitFor c = standardDeckSize := by
  simp [copyLimitFor, h]

theorem copyLimitFor_nonbasic (c : DeckCard)
    (h : ¬ (c.category = .energy ∧ c.isBasicEnergy = true)) :
    copyLimitFor c = 4 := by
  simp [copyLimitFor, h]

/-- Rule: at most four copies per name, except basic energy cards. -/
def legalCopies (deck : List DeckCard) : Prop :=
  ∀ c ∈ deck, countByName deck c.card.name ≤ copyLimitFor c

theorem legalCopies_nil : legalCopies [] := by
  intro c hMem
  cases hMem

theorem legalCopies_nonbasic_bound (deck : List DeckCard) (c : DeckCard)
    (hLegal : legalCopies deck) (hMem : c ∈ deck)
    (hNon : ¬ (c.category = .energy ∧ c.isBasicEnergy = true)) :
    countByName deck c.card.name ≤ 4 := by
  have hBound := hLegal c hMem
  simpa [copyLimitFor, hNon] using hBound

theorem legalCopies_basicEnergy_bound (deck : List DeckCard) (c : DeckCard)
    (hLegal : legalCopies deck) (hMem : c ∈ deck)
    (hBasic : c.category = .energy ∧ c.isBasicEnergy = true) :
    countByName deck c.card.name ≤ standardDeckSize := by
  have hBound := hLegal c hMem
  simpa [copyLimitFor, hBasic] using hBound

/-- Rule: at least one basic Pokemon must be present. -/
def hasBasicPokemon (deck : List DeckCard) : Prop :=
  0 < basicPokemonCount deck

theorem hasBasicPokemon_iff (deck : List DeckCard) :
    hasBasicPokemon deck ↔ 0 < basicPokemonCount deck := Iff.rfl

theorem hasBasicPokemon_of_gt (deck : List DeckCard)
    (h : 0 < basicPokemonCount deck) : hasBasicPokemon deck := h

theorem hasBasicPokemon_cons_basic (c : DeckCard) (deck : List DeckCard)
    (hCat : c.category = .pokemon) (hBasic : c.isBasicPokemon = true) :
    hasBasicPokemon (c :: deck) := by
  unfold hasBasicPokemon
  have hCat' : (c.category == .pokemon) = true := by
    rw [hCat]
    decide
  have hHead : (if c.category == .pokemon && c.isBasicPokemon then 1 else 0) = 1 := by
    simp [hCat', hBasic]
  rw [basicPokemonCount_cons, hHead]
  simpa [Nat.add_comm] using Nat.succ_pos (basicPokemonCount deck)

/-- Rule: at most one ACE SPEC card in the deck. -/
def aceSpecLegal (deck : List DeckCard) : Prop :=
  aceSpecCount deck ≤ 1

theorem aceSpecLegal_iff (deck : List DeckCard) :
    aceSpecLegal deck ↔ aceSpecCount deck ≤ 1 := Iff.rfl

theorem aceSpecLegal_nil : aceSpecLegal [] := by
  simp [aceSpecLegal, aceSpecCount]

theorem aceSpecLegal_singleton (c : DeckCard) : aceSpecLegal [c] := by
  cases hAce : c.isAceSpec <;> simp [aceSpecLegal, aceSpecCount, hAce]

/-- Rule: each Prism Star card name appears at most once. -/
def prismStarLegal (deck : List DeckCard) : Prop :=
  ∀ name : String, prismStarCountByName deck name ≤ 1

theorem prismStarLegal_iff (deck : List DeckCard) :
    prismStarLegal deck ↔ ∀ name : String, prismStarCountByName deck name ≤ 1 := Iff.rfl

theorem prismStarLegal_nil : prismStarLegal [] := by
  intro name
  simp [prismStarCountByName]

theorem prismStarLegal_singleton (c : DeckCard) : prismStarLegal [c] := by
  intro name
  cases hPrism : c.isPrismStar <;> cases hName : (c.card.name == name) <;>
    simp [prismStarCountByName, hPrism, hName]

/-- Consistency metrics used for quick deck checks. -/
structure ConsistencyMetrics where
  drawSupporters : Nat
  pokemonSearch : Nat
  deriving Repr, BEq, DecidableEq

/-- Aggregate consistency metrics from a deck list. -/
def consistencyMetrics (deck : List DeckCard) : ConsistencyMetrics :=
  { drawSupporters := drawSupporterCount deck
    pokemonSearch := pokemonSearchCount deck }

@[simp] theorem consistencyMetrics_drawSupporters (deck : List DeckCard) :
    (consistencyMetrics deck).drawSupporters = drawSupporterCount deck := rfl

@[simp] theorem consistencyMetrics_pokemonSearch (deck : List DeckCard) :
    (consistencyMetrics deck).pokemonSearch = pokemonSearchCount deck := rfl

/-- Reuse the shared archetype type. -/
abbrev Archetype := PokemonLean.Archetypes.Archetype

/-- Classify a profile from draw-supporter and Pokemon-search counts. -/
def classifyArchetype (drawSupporters pokemonSearch : Nat) : Archetype :=
  if 12 ≤ drawSupporters ∧ 8 ≤ pokemonSearch then
    .combo
  else if 10 ≤ drawSupporters then
    .control
  else
    .aggro

theorem classifyArchetype_combo (drawSupporters pokemonSearch : Nat)
    (hDraw : 12 ≤ drawSupporters) (hSearch : 8 ≤ pokemonSearch) :
    classifyArchetype drawSupporters pokemonSearch = .combo := by
  simp [classifyArchetype, hDraw, hSearch]

theorem classifyArchetype_control (drawSupporters pokemonSearch : Nat)
    (hCombo : ¬ (12 ≤ drawSupporters ∧ 8 ≤ pokemonSearch))
    (hDraw : 10 ≤ drawSupporters) :
    classifyArchetype drawSupporters pokemonSearch = .control := by
  simp [classifyArchetype, hCombo, hDraw]

theorem classifyArchetype_aggro (drawSupporters pokemonSearch : Nat)
    (hDraw : drawSupporters < 10) :
    classifyArchetype drawSupporters pokemonSearch = .aggro := by
  have hNotControl : ¬ 10 ≤ drawSupporters := Nat.not_le_of_gt hDraw
  have hNotCombo : ¬ (12 ≤ drawSupporters ∧ 8 ≤ pokemonSearch) := by
    intro hCombo
    exact hNotControl (Nat.le_trans (by decide : 10 ≤ 12) hCombo.1)
  simp [classifyArchetype, hNotCombo, hNotControl]

/-- Deck-level archetype classification. -/
def classifyDeck (deck : List DeckCard) : Archetype :=
  classifyArchetype (drawSupporterCount deck) (pokemonSearchCount deck)

theorem classifyDeck_eq (deck : List DeckCard) :
    classifyDeck deck = classifyArchetype (drawSupporterCount deck) (pokemonSearchCount deck) := rfl

theorem classifyDeck_combo (deck : List DeckCard)
    (hDraw : 12 ≤ drawSupporterCount deck) (hSearch : 8 ≤ pokemonSearchCount deck) :
    classifyDeck deck = .combo := by
  simp [classifyDeck, classifyArchetype, hDraw, hSearch]

theorem classifyDeck_control (deck : List DeckCard)
    (hCombo : ¬ (12 ≤ drawSupporterCount deck ∧ 8 ≤ pokemonSearchCount deck))
    (hDraw : 10 ≤ drawSupporterCount deck) :
    classifyDeck deck = .control := by
  simp [classifyDeck, classifyArchetype, hCombo, hDraw]

theorem classifyDeck_aggro (deck : List DeckCard)
    (hDraw : drawSupporterCount deck < 10) :
    classifyDeck deck = .aggro := by
  exact classifyArchetype_aggro (drawSupporterCount deck) (pokemonSearchCount deck) hDraw

/-- Full deck-building legality predicate. -/
def legalDeck (deck : List DeckCard) : Prop :=
  hasSixtyCards deck ∧
  legalCopies deck ∧
  hasBasicPokemon deck ∧
  aceSpecLegal deck ∧
  prismStarLegal deck

theorem legalDeck_iff (deck : List DeckCard) :
    legalDeck deck ↔
      hasSixtyCards deck ∧
      legalCopies deck ∧
      hasBasicPokemon deck ∧
      aceSpecLegal deck ∧
      prismStarLegal deck := Iff.rfl

theorem legalDeck_hasSixtyCards (deck : List DeckCard) :
    legalDeck deck → hasSixtyCards deck := by
  intro h
  exact h.1

theorem legalDeck_legalCopies (deck : List DeckCard) :
    legalDeck deck → legalCopies deck := by
  intro h
  exact h.2.1

theorem legalDeck_hasBasicPokemon (deck : List DeckCard) :
    legalDeck deck → hasBasicPokemon deck := by
  intro h
  exact h.2.2.1

theorem legalDeck_aceSpecLegal (deck : List DeckCard) :
    legalDeck deck → aceSpecLegal deck := by
  intro h
  exact h.2.2.2.1

theorem legalDeck_prismStarLegal (deck : List DeckCard) :
    legalDeck deck → prismStarLegal deck := by
  intro h
  exact h.2.2.2.2

theorem legalDeck_of_components (deck : List DeckCard)
    (hSize : hasSixtyCards deck)
    (hCopies : legalCopies deck)
    (hBasic : hasBasicPokemon deck)
    (hAce : aceSpecLegal deck)
    (hPrism : prismStarLegal deck) :
    legalDeck deck := by
  exact ⟨hSize, hCopies, hBasic, hAce, hPrism⟩

end PokemonLean.DeckBuilding
