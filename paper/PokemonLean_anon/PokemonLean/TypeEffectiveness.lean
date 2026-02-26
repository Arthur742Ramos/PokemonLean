/-
  PokemonLean / TypeEffectiveness.lean

  Formalizes the Pokémon TCG type effectiveness (weakness/resistance) system
  and proves strategic results about coverage, triangles, and damage calculation.

  PType constructor mapping to TCG names:
    electric = Lightning, dark = Darkness, steel = Metal, normal = Colorless

  Weakness chart (modern TCG, multiple eras combined for completeness):
    Grass    weak to Fire
    Fire     weak to Water
    Water    weak to Grass, Electric (both appear on TCG Water cards)
    Electric weak to Fighting
    Psychic  weak to Dark (Darkness)
    Fighting weak to Psychic
    Dark     weak to Grass
    Steel    weak to Fire
    Dragon   weak to Fairy (XY-era TCG)
    Fairy    weak to Steel (Metal)
    Normal   weak to Fighting (standard Colorless weakness)

  Resistance chart (TCG standard, −30 damage):
    Fire     resists Steel (Metal)
    Grass    resists Water
    Steel    resists Psychic
    Dark     resists Psychic
    Fairy    resists Dark (Darkness)
    Fighting resists Dark (Darkness)
-/

import PokemonLean.Core.Types

open PokemonLean.Core.Types

namespace PokemonLean.TypeEffectiveness

/-! ## Weakness -/

/-- TCG weakness chart. `weakness defender attacker` is true when
    a Pokémon of type `defender` is weak to attacks of type `attacker`. -/
def weakness : PType → PType → Bool
  | .grass,    .fire     => true
  | .fire,     .water    => true
  | .water,    .grass    => true
  | .water,    .electric => true
  | .electric, .fighting => true
  | .psychic,  .dark     => true
  | .fighting, .psychic  => true
  | .dark,     .grass    => true
  | .steel,    .fire     => true
  | .dragon,   .fairy    => true
  | .fairy,    .steel    => true
  | .normal,   .fighting => true
  | _,         _         => false

/-! ## Resistance -/

/-- TCG resistance chart. `resistance defender attacker` is true when
    a Pokémon of type `defender` resists attacks of type `attacker` (−30). -/
def resistance : PType → PType → Bool
  | .fire,     .steel   => true
  | .grass,    .water   => true
  | .steel,    .psychic => true
  | .dark,     .psychic => true
  | .fairy,    .dark    => true
  | .fighting, .dark    => true
  | _,         _        => false

/-! ## Damage calculation -/

/-- Apply weakness: doubles damage if the defender is weak to the attacker's type. -/
def applyWeakness (baseDamage : Nat) (attackerType defenderType : PType) : Nat :=
  if weakness defenderType attackerType then baseDamage * 2
  else baseDamage

/-- Apply resistance: subtracts 30 if the defender resists the attacker's type.
    Damage cannot go below 0 (Nat subtraction). -/
def applyResistance (baseDamage : Nat) (attackerType defenderType : PType) : Nat :=
  if resistance defenderType attackerType then baseDamage - 30
  else baseDamage

/-- Effective damage: apply weakness first, then resistance (standard TCG order). -/
def effectiveDamage (baseDamage : Nat) (attackerType defenderType : PType) : Nat :=
  let afterWeak := applyWeakness baseDamage attackerType defenderType
  applyResistance afterWeak attackerType defenderType

/-! ## Theorems -/

/-- (7) WEAKNESS_DOUBLES: if the defender is weak to the attacker and does not resist,
    effective damage = 2 × base. -/
theorem WEAKNESS_DOUBLES (base : Nat) (atk def_ : PType)
    (hw : weakness def_ atk = true) (hr : resistance def_ atk = false) :
    effectiveDamage base atk def_ = base * 2 := by
  simp [effectiveDamage, applyWeakness, applyResistance, hw, hr]

/-- (8) RESISTANCE_SUBTRACTS: if the defender resists and is not weak,
    effective damage = base − 30. -/
theorem RESISTANCE_SUBTRACTS (base : Nat) (atk def_ : PType)
    (hnw : weakness def_ atk = false) (hr : resistance def_ atk = true) :
    effectiveDamage base atk def_ = base - 30 := by
  simp [effectiveDamage, applyWeakness, applyResistance, hnw, hr]

/-- (9) WEAKNESS_BEATS_RESISTANCE: if both weakness and resistance apply,
    damage = 2 × base − 30 (weakness applied first, then resistance). -/
theorem WEAKNESS_BEATS_RESISTANCE (base : Nat) (atk def_ : PType)
    (hw : weakness def_ atk = true) (hr : resistance def_ atk = true) :
    effectiveDamage base atk def_ = base * 2 - 30 := by
  simp [effectiveDamage, applyWeakness, applyResistance, hw, hr]

/-- (10) NO_SELF_WEAKNESS: no type is weak to itself. -/
theorem NO_SELF_WEAKNESS : ∀ t : PType, weakness t t = false := by
  intro t; cases t <;> rfl

/-- (11) WEAKNESS_NOT_SYMMETRIC: weakness is not symmetric.
    Fire is weak to Water, but Water is not weak to Fire. -/
theorem WEAKNESS_NOT_SYMMETRIC :
    weakness PType.fire PType.water = true ∧
    weakness PType.water PType.fire = false := by
  exact ⟨rfl, rfl⟩

/-- (12) COLORLESS_NEUTRAL: Colorless (normal) has no resistances.
    (Its only type interaction is weakness to Fighting, which is standard TCG.) -/
theorem COLORLESS_NEUTRAL :
    ∀ a : PType, resistance PType.normal a = false := by
  intro a; cases a <;> rfl

/-- (13) TYPE_ADVANTAGE_OHKO: with weakness, a 90-damage attack on a Fire Pokémon
    deals 180 damage (enough to KO 180 HP). Without weakness, 90 < 180. -/
theorem TYPE_ADVANTAGE_OHKO :
    applyWeakness 90 PType.water PType.fire = 180 ∧ 90 < 180 := by
  constructor
  · rfl
  · omega

/-- (14) TRIANGLE: there exist types A, B, C forming a weakness triangle
    (A weak to B, B weak to C, C weak to A). Witness: Grass/Fire/Water. -/
theorem TRIANGLE :
    ∃ A B C : PType,
      weakness A B = true ∧ weakness B C = true ∧ weakness C A = true := by
  exact ⟨PType.grass, PType.fire, PType.water, rfl, rfl, rfl⟩

/-- (15) COVERAGE: for any defending type, there exists an attacking type
    that hits for weakness. -/
theorem COVERAGE :
    ∀ def_ : PType, ∃ atk : PType, weakness def_ atk = true := by
  intro def_
  -- PType constructors: fire, water, grass, electric, psychic, fighting,
  --                     dark, steel, dragon, fairy, normal
  cases def_
  · exact ⟨PType.water, rfl⟩     -- fire: weak to water
  · exact ⟨PType.grass, rfl⟩     -- water: weak to grass
  · exact ⟨PType.fire, rfl⟩      -- grass: weak to fire
  · exact ⟨PType.fighting, rfl⟩  -- electric: weak to fighting
  · exact ⟨PType.dark, rfl⟩      -- psychic: weak to dark
  · exact ⟨PType.psychic, rfl⟩   -- fighting: weak to psychic
  · exact ⟨PType.grass, rfl⟩     -- dark: weak to grass
  · exact ⟨PType.fire, rfl⟩      -- steel: weak to fire
  · exact ⟨PType.fairy, rfl⟩     -- dragon: weak to fairy
  · exact ⟨PType.steel, rfl⟩     -- fairy: weak to steel
  · exact ⟨PType.fighting, rfl⟩  -- normal: weak to fighting

end PokemonLean.TypeEffectiveness
