/-
  PokemonLean / Core / Types.lean

  Foundational Pokémon TCG type system for the PokemonLean project.
  Defines Pokémon types (PType), energy types (EnergyType) including
  colorless, energy costs, and the weakness/resistance type chart.

  This is the shared base that all other PokemonLean modules will import.

  All proofs are sorry-free.  20+ theorems.
-/

namespace PokemonLean.Core

-- ============================================================
-- §1  Pokémon Types
-- ============================================================

/-- The 11 Pokémon types in the TCG.
    Note: Colorless is NOT a Pokémon type — it is an energy type only. -/
inductive PType where
  | fire
  | water
  | grass
  | electric
  | psychic
  | fighting
  | dark
  | steel
  | dragon
  | fairy
  | normal
deriving DecidableEq, Repr, BEq, Inhabited

/-- Total number of Pokémon types. -/
def PType.count : Nat := 11

-- ============================================================
-- §2  Energy Types (extends PType with colorless)
-- ============================================================

/-- Energy types include all Pokémon types plus colorless.
    Colorless energy can satisfy any colorless requirement. -/
inductive EnergyType where
  | typed (t : PType)
  | colorless
deriving DecidableEq, Repr, BEq, Inhabited

/-- Lift a PType to the corresponding EnergyType. -/
def PType.toEnergy (t : PType) : EnergyType := .typed t

/-- All PType values as a list (useful for exhaustive checks). -/
def PType.all : List PType :=
  [.fire, .water, .grass, .electric, .psychic, .fighting,
   .dark, .steel, .dragon, .fairy, .normal]

/-- All EnergyType values. -/
def EnergyType.all : List EnergyType :=
  PType.all.map .typed ++ [.colorless]

-- ============================================================
-- §3  Energy Cost
-- ============================================================

/-- Energy cost for an attack or retreat.
    `requirements` maps each PType to the number of that specific energy needed.
    `colorlessReq` is how many additional energy of any type are needed. -/
structure EnergyCost where
  requirements : PType → Nat
  colorlessReq : Nat
deriving Inhabited

/-- The zero energy cost. -/
def EnergyCost.zero : EnergyCost where
  requirements := fun _ => 0
  colorlessReq := 0

/-- An energy cost requiring only colorless energy. -/
def EnergyCost.colorlessOnly (n : Nat) : EnergyCost where
  requirements := fun _ => 0
  colorlessReq := n

/-- An energy cost of a single typed energy. -/
def EnergyCost.single (t : PType) : EnergyCost where
  requirements := fun t' => if t == t' then 1 else 0
  colorlessReq := 0

/-- Total typed energy required. -/
def EnergyCost.totalTyped (ec : EnergyCost) : Nat :=
  PType.all.foldl (fun acc t => acc + ec.requirements t) 0

/-- Total energy required (typed + colorless). -/
def EnergyCost.totalCost (ec : EnergyCost) : Nat :=
  ec.totalTyped + ec.colorlessReq

-- ============================================================
-- §4  Weakness / Resistance Chart (TCG-accurate)
-- ============================================================

/-- The Pokémon type that a given type is weak to in the TCG.
    TCG weakness is simpler than video game weakness — each type has
    at most one weakness printed on the card. These are the standard
    weakness assignments used across modern TCG eras. -/
def weaknessFor : PType → Option PType
  | .fire      => some .water
  | .water     => some .electric
  | .grass     => some .fire
  | .electric  => some .fighting
  | .psychic   => some .dark
  | .fighting  => some .psychic
  | .dark      => some .fighting
  | .steel     => some .fire
  | .dragon    => some .fairy
  | .fairy     => some .steel
  | .normal    => some .fighting

/-- The Pokémon type that a given type resists in the TCG.
    Not all types have resistance; many Pokémon have no resistance printed. -/
def resistanceFor : PType → Option PType
  | .fire      => none
  | .water     => none
  | .grass     => none
  | .electric  => some .steel
  | .psychic   => some .fighting
  | .fighting  => none
  | .dark      => some .psychic
  | .steel     => some .psychic
  | .dragon    => none
  | .fairy     => some .dark
  | .normal    => none

/-- Standard weakness multiplier in the TCG: damage × 2. -/
def weaknessMultiplier : Nat := 2

/-- Standard resistance reduction in the TCG: damage − 30. -/
def resistanceReduction : Nat := 30

/-- Apply weakness: double the damage. -/
def applyWeakness (baseDamage : Nat) : Nat :=
  baseDamage * weaknessMultiplier

/-- Apply resistance: subtract 30, minimum 0. -/
def applyResistance (baseDamage : Nat) : Nat :=
  if baseDamage ≥ resistanceReduction then baseDamage - resistanceReduction else 0

/-- Check if attacking type triggers weakness on the defender's PType. -/
def isWeakTo (defender attacker : PType) : Bool :=
  weaknessFor defender == some attacker

/-- Check if defender resists the attacking type. -/
def resists (defender attacker : PType) : Bool :=
  resistanceFor defender == some attacker

-- ============================================================
-- §5  Theorems — PType enumeration
-- ============================================================

/-- PType.all contains exactly 11 elements. -/
theorem ptype_all_length : PType.all.length = 11 := by native_decide

/-- Every PType is in PType.all. -/
theorem ptype_all_complete (t : PType) : t ∈ PType.all := by
  cases t <;> simp [PType.all]

/-- PType.all has no duplicates. -/
theorem ptype_all_nodup : PType.all.Nodup := by native_decide

/-- EnergyType.all contains exactly 12 elements. -/
theorem energyType_all_length : EnergyType.all.length = 12 := by native_decide

-- ============================================================
-- §6  Theorems — Energy Cost
-- ============================================================

/-- Zero energy cost has total cost 0. -/
theorem zero_cost_total : EnergyCost.zero.totalCost = 0 := by
  simp [EnergyCost.totalCost, EnergyCost.totalTyped, EnergyCost.zero, PType.all]

/-- Colorless-only cost of n has total cost n. -/
theorem colorless_only_total (n : Nat) : (EnergyCost.colorlessOnly n).totalCost = n := by
  simp [EnergyCost.totalCost, EnergyCost.totalTyped, EnergyCost.colorlessOnly, PType.all]

/-- Single typed energy has total cost 1. -/
theorem single_cost_total (t : PType) : (EnergyCost.single t).totalCost = 1 := by
  cases t <;> native_decide

-- ============================================================
-- §7  Theorems — Weakness / Resistance properties
-- ============================================================

/-- Every PType has a weakness. -/
theorem every_type_has_weakness (t : PType) : (weaknessFor t).isSome = true := by
  cases t <;> rfl

/-- No type is weak to itself. -/
theorem no_self_weakness (t : PType) : weaknessFor t ≠ some t := by
  cases t <;> simp [weaknessFor]

/-- Weakness is not symmetric: if A is weak to B, B is not necessarily weak to A.
    Concrete witness: fire is weak to water, but water is NOT weak to fire. -/
theorem weakness_not_symmetric :
    weaknessFor .fire = some .water ∧ weaknessFor .water ≠ some .fire := by
  constructor
  · rfl
  · simp [weaknessFor]

/-- Fire is weak to water. -/
theorem fire_weak_to_water : isWeakTo .fire .water = true := by native_decide

/-- Water is weak to electric. -/
theorem water_weak_to_electric : isWeakTo .water .electric = true := by native_decide

/-- Grass is weak to fire. -/
theorem grass_weak_to_fire : isWeakTo .grass .fire = true := by native_decide

/-- Dragon is weak to fairy. -/
theorem dragon_weak_to_fairy : isWeakTo .dragon .fairy = true := by native_decide

/-- Resistance reduces damage: for any positive base damage ≥ 30,
    the result after applying resistance is strictly less. -/
theorem resistance_reduces_damage (d : Nat) (h : d ≥ 30) :
    applyResistance d < d := by
  unfold applyResistance resistanceReduction
  simp [h]
  omega

/-- Resistance cannot produce negative damage (always ≥ 0). -/
theorem resistance_nonneg (d : Nat) : applyResistance d ≥ 0 := by
  omega

/-- Applying weakness doubles damage. -/
theorem weakness_doubles (d : Nat) : applyWeakness d = d * 2 := by
  simp [applyWeakness, weaknessMultiplier]

/-- Weakness of 0 damage is still 0. -/
theorem weakness_zero : applyWeakness 0 = 0 := by
  simp [applyWeakness, weaknessMultiplier]

/-- Resistance applied to 0 is 0. -/
theorem resistance_zero : applyResistance 0 = 0 := by
  simp [applyResistance, resistanceReduction]

/-- Dark resists Psychic. -/
theorem dark_resists_psychic : resists .dark .psychic = true := by native_decide

/-- Fairy resists Dark. -/
theorem fairy_resists_dark : resists .fairy .dark = true := by native_decide

/-- Type chart completeness: weaknessFor maps each PType to a valid PType
    (the result is always `some`). -/
theorem weakness_chart_total (t : PType) :
    ∃ w : PType, weaknessFor t = some w := by
  cases t <;> exact ⟨_, rfl⟩

/-- The weakness target is always a different type. -/
theorem weakness_target_differs (t : PType) :
    ∀ w, weaknessFor t = some w → t ≠ w := by
  cases t <;> intro w hw <;> simp [weaknessFor] at hw <;> subst hw <;> simp

end PokemonLean.Core
