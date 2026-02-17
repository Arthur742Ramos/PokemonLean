/-
  PokemonLean / RegionalForms.lean

  Regional form mechanics: Alolan, Galarian, Hisuian, Paldean forms.
  Same species different types, evolution branching (Pikachu→Raichu vs
  Pikachu→Alolan Raichu), regional form deck building (count as same
  Pokémon), regional exclusive moves.

  Multi-step trans/symm/congrArg computational path chains.
  All proofs sorry-free.  20+ theorems.
-/

namespace RegionalForms

-- ============================================================================
-- §1  Core Step / Path machinery
-- ============================================================================

inductive Step (α : Type) : α → α → Type where
  | mk : (name : String) → (a b : α) → Step α a b

inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

def Path.trans : Path α a b → Path α b c → Path α a c
  | .nil _, q => q
  | .cons s p, q => .cons s (p.trans q)

def Path.length : Path α a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

def Step.symm : Step α a b → Step α b a
  | .mk name a b => .mk (name ++ "⁻¹") b a

def Path.symm : Path α a b → Path α b a
  | .nil a => .nil a
  | .cons s rest => rest.symm.trans (.cons s.symm (.nil _))

def Path.single (s : Step α a b) : Path α a b :=
  .cons s (.nil b)

def Path.congrArg (f : α → β) (lbl : String)
    : Path α a b → Path β (f a) (f b)
  | .nil _ => .nil _
  | .cons _ p => .cons (.mk lbl _ _) (p.congrArg f lbl)

theorem Path.trans_nil (p : Path α a b) : p.trans (.nil b) = p := by
  induction p with
  | nil _ => rfl
  | cons s _ ih => simp [Path.trans, ih]

theorem Path.trans_assoc (p : Path α a b) (q : Path α b c) (r : Path α c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => rfl
  | cons s _ ih => simp [Path.trans, ih]

theorem Path.length_trans (p : Path α a b) (q : Path α b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [Path.trans, Path.length]
  | cons _ _ ih => simp [Path.trans, Path.length, ih]; omega

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

/-- Theorem 7: Pikachu → Kanto Raichu is a single-step path. -/
def evo_path_kanto : Path EvoState pikachu_state raichu_kanto_state :=
  Path.single (Step.mk "evolve-thunder-stone-kanto" _ _)

/-- Theorem 8: Pikachu → Alolan Raichu is a single-step path. -/
def evo_path_alola : Path EvoState pikachu_state raichu_alola_state :=
  Path.single (Step.mk "evolve-thunder-stone-alola" _ _)

/-- Theorem 9: Both evolution paths have length 1. -/
theorem evo_branch_same_length :
    evo_path_kanto.length = evo_path_alola.length := by rfl

/-- Theorem 10: Evolution branching: Kanto path ≠ Alola path target. -/
theorem evo_branch_different_targets :
    raichu_kanto_state ≠ raichu_alola_state := by
  simp [raichu_kanto_state, raichu_alola_state]

/-- Theorem 11: Symm of Kanto evolution undoes evolution. -/
theorem evo_kanto_symm_length :
    evo_path_kanto.symm.length = 1 := by rfl

/-- Theorem 12: congrArg extracts species path from evolution path. -/
theorem evo_congrArg_species :
    (evo_path_kanto.congrArg (fun s => s.species.dexNum) "dex").length = 1 := by rfl

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

/-- Theorem 20: Path from Kanto to Alola form (conceptual region migration). -/
def kanto_to_alola_path :
    Path FormState
      ⟨vulpixKanto, true⟩
      ⟨vulpixAlola, true⟩ :=
  Path.cons (Step.mk "remove-kanto-form" ⟨vulpixKanto, true⟩ removedState)
    (Path.single (Step.mk "add-alola-form" removedState ⟨vulpixAlola, true⟩))

/-- Theorem 21: Region migration path has length 2. -/
theorem region_migration_length :
    kanto_to_alola_path.length = 2 := by rfl

/-- Theorem 22: Symm of migration path has length 2. -/
theorem region_migration_symm_length :
    kanto_to_alola_path.symm.length = 2 := by rfl

/-- Theorem 23: congrArg on form type through migration. -/
theorem migration_congrArg_type :
    (kanto_to_alola_path.congrArg (fun s => s.form.type1) "type").length = 2 := by rfl

def meowthAlolaDeckState : FormState := ⟨meowthAlola, true⟩

/-- Theorem 24: Three-region Meowth path (Kanto → Alola → Galar). -/
def meowth_three_regions :
    Path FormState
      ⟨meowthKanto, true⟩
      ⟨meowthGalar, true⟩ :=
  Path.cons (Step.mk "swap-kanto-alola" ⟨meowthKanto, true⟩ meowthAlolaDeckState)
    (Path.single (Step.mk "swap-alola-galar" meowthAlolaDeckState ⟨meowthGalar, true⟩))

/-- Theorem 25: Three-region meowth path has length 2. -/
theorem meowth_three_regions_length :
    meowth_three_regions.length = 2 := by rfl

/-- Theorem 26: Trans of two single-step paths = 2-step path length. -/
theorem trans_two_single_steps :
    let p1 := Path.single (Step.mk "step1" (⟨meowthKanto, true⟩ : FormState) ⟨meowthAlola, true⟩)
    let p2 := Path.single (Step.mk "step2" (⟨meowthAlola, true⟩ : FormState) ⟨meowthGalar, true⟩)
    (p1.trans p2).length = 2 := by rfl

end RegionalForms
