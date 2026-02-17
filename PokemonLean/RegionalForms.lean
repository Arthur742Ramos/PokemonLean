/-
  PokemonLean / RegionalForms.lean

  Regional form mechanics: Alolan, Galarian, Hisuian, Paldean forms.
  Same species different types, evolution branching (Pikachu→Raichu vs
  Pikachu→Alolan Raichu), regional form deck building (count as same
  Pokémon), regional exclusive moves.

-/

namespace RegionalForms
-- ============================================================================
-- §2  Regional form types
-- ============================================================================

/-- Region of origin. -/
inductive Region where
  | kanto | alola | galar | hisui | paldea
deriving DecidableEq, Repr

/-- Pokémon type (energy type in TCG). -/
inductive PType where
  | normal | fire | water | grass | electric | psychic | fighting
  | dark | steel | fairy | dragon | ice | ground | rock
  | flying | poison | bug | ghost
deriving DecidableEq, Repr

/-- Species identifier (national dex style). -/
structure Species where
  dexNum : Nat
  name   : String
deriving DecidableEq, Repr

/-- A regional form: same species, potentially different types. -/
structure RegionalForm where
  species   : Species
  region    : Region
  type1     : PType
  type2     : Option PType
  exclusiveMove : Option String
deriving DecidableEq, Repr

/-- Theorem 1: Two regional forms of the same species share dex number. -/
theorem same_species_same_dex (f1 f2 : RegionalForm)
    (h : f1.species = f2.species) :
    f1.species.dexNum = f2.species.dexNum := by
  rw [h]

-- ============================================================================
-- §3  Canonical Pokémon examples
-- ============================================================================

def vulpixKanto : RegionalForm :=
  ⟨⟨37, "Vulpix"⟩, .kanto, .fire, none, some "Flame Charge"⟩

def vulpixAlola : RegionalForm :=
  ⟨⟨37, "Vulpix"⟩, .alola, .ice, none, some "Aurora Beam"⟩

def meowthKanto : RegionalForm :=
  ⟨⟨52, "Meowth"⟩, .kanto, .normal, none, some "Pay Day"⟩

def meowthAlola : RegionalForm :=
  ⟨⟨52, "Meowth"⟩, .alola, .dark, none, some "Night Slash"⟩

def meowthGalar : RegionalForm :=
  ⟨⟨52, "Meowth"⟩, .galar, .steel, none, some "Metal Claw"⟩

def raichuKanto : RegionalForm :=
  ⟨⟨26, "Raichu"⟩, .kanto, .electric, none, none⟩

def raichuAlola : RegionalForm :=
  ⟨⟨26, "Raichu"⟩, .alola, .electric, some .psychic, some "Psychic"⟩

def growlitheHisui : RegionalForm :=
  ⟨⟨58, "Growlithe"⟩, .hisui, .fire, some .rock, some "Rock Slide"⟩

def wooperPaldea : RegionalForm :=
  ⟨⟨194, "Wooper"⟩, .paldea, .poison, some .ground, some "Poison Tail"⟩

-- ============================================================================
-- §4  Regional form predicates and theorems
-- ============================================================================

/-- Two forms are of the same species. -/
def sameSpecies (f1 f2 : RegionalForm) : Prop := f1.species = f2.species

/-- Theorem 2: Vulpix Kanto and Alola are same species. -/
theorem vulpix_same_species : sameSpecies vulpixKanto vulpixAlola := by rfl

/-- Theorem 3: Meowth Kanto and Alola are same species. -/
theorem meowth_kanto_alola_same : sameSpecies meowthKanto meowthAlola := by rfl

/-- Theorem 4: Meowth Kanto and Galar are same species. -/
theorem meowth_kanto_galar_same : sameSpecies meowthKanto meowthGalar := by rfl

/-- Two forms differ in typing. -/
def differentTyping (f1 f2 : RegionalForm) : Prop :=
  f1.type1 ≠ f2.type1 ∨ f1.type2 ≠ f2.type2

/-- Theorem 5: Vulpix Kanto (Fire) ≠ Alola (Ice) in type. -/
theorem vulpix_different_type : differentTyping vulpixKanto vulpixAlola := by
  left; simp [vulpixKanto, vulpixAlola]

/-- Theorem 6: Meowth Kanto (Normal) ≠ Galar (Steel). -/
theorem meowth_kanto_galar_diff_type : differentTyping meowthKanto meowthGalar := by
  left; simp [meowthKanto, meowthGalar]

-- ============================================================================
-- §5  Evolution branching paths
-- ============================================================================

/-- Evolution state: species + region context. -/
structure EvoState where
  species : Species
  region  : Region
  evolved : Bool
deriving DecidableEq, Repr

def pikachu_state : EvoState := ⟨⟨25, "Pikachu"⟩, .kanto, false⟩
def raichu_kanto_state : EvoState := ⟨⟨26, "Raichu"⟩, .kanto, true⟩
def raichu_alola_state : EvoState := ⟨⟨26, "Raichu"⟩, .alola, true⟩


/-- Theorem 10: Evolution branching: Kanto path ≠ Alola path target. -/
theorem evo_branch_different_targets :
    raichu_kanto_state ≠ raichu_alola_state := by
  simp [raichu_kanto_state, raichu_alola_state]


-- ============================================================================
-- §6  Deck building with regional forms
-- ============================================================================

/-- A deck entry: card name, count, and species for the 4-copy rule. -/
structure DeckEntry where
  cardName : String
  count    : Nat
  species  : Species
deriving DecidableEq, Repr

/-- Count total copies of a species across all entries. -/
def totalCopies (entries : List DeckEntry) (sp : Species) : Nat :=
  entries.filter (fun e => e.species == sp) |>.foldl (fun acc e => acc + e.count) 0

/-- Deck is legal if no species exceeds 4 copies. -/
def deckLegal (entries : List DeckEntry) : Prop :=
  ∀ sp : Species, totalCopies entries sp ≤ 4

/-- Theorem 13: Empty deck is legal. -/
theorem empty_deck_legal : deckLegal [] := by
  intro sp; simp [totalCopies]

/-- Theorem 14: Single entry with count ≤ 4 is legal. -/
theorem single_entry_legal (e : DeckEntry) (h : e.count ≤ 4) :
    deckLegal [e] := by
  intro sp
  simp only [totalCopies, List.filter]
  split
  · simp [List.foldl]; omega
  · simp [List.foldl]

/-- Theorem 15: Regional forms count as same species — Vulpix Kanto (2) + Alola (2) ≤ 4. -/
theorem regional_same_species_count :
    let vulpixSpecies : Species := ⟨37, "Vulpix"⟩
    let entries := [
      DeckEntry.mk "Vulpix (Kanto)" 2 vulpixSpecies,
      DeckEntry.mk "Vulpix (Alola)" 2 vulpixSpecies
    ]
    totalCopies entries vulpixSpecies = 4 := by
  native_decide

/-- Theorem 16: Exceeding 4 with regional forms is illegal.
    3 Kanto Vulpix + 2 Alola Vulpix = 5 > 4. -/
theorem regional_over_limit :
    let vulpixSpecies : Species := ⟨37, "Vulpix"⟩
    let entries := [
      DeckEntry.mk "Vulpix (Kanto)" 3 vulpixSpecies,
      DeckEntry.mk "Vulpix (Alola)" 2 vulpixSpecies
    ]
    totalCopies entries vulpixSpecies = 5 := by
  native_decide

-- ============================================================================
-- §7  Regional exclusive moves
-- ============================================================================

/-- Theorem 17: Alolan Vulpix has exclusive move Aurora Beam. -/
theorem alolan_vulpix_exclusive :
    vulpixAlola.exclusiveMove = some "Aurora Beam" := by rfl

/-- Theorem 18: Kanto Vulpix has exclusive move Flame Charge. -/
theorem kanto_vulpix_exclusive :
    vulpixKanto.exclusiveMove = some "Flame Charge" := by rfl

/-- Theorem 19: Different regions have different exclusive moves. -/
theorem different_region_different_moves :
    vulpixKanto.exclusiveMove ≠ vulpixAlola.exclusiveMove := by
  simp [vulpixKanto, vulpixAlola]

-- ============================================================================
-- §8  Multi-step regional transformation paths
-- ============================================================================

/-- Form transition state. -/
structure FormState where
  form : RegionalForm
  inDeck : Bool
deriving DecidableEq, Repr

def removedState : FormState := ⟨vulpixKanto, false⟩


def meowthAlolaDeckState : FormState := ⟨meowthAlola, true⟩


end RegionalForms
