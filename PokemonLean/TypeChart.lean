import PokemonLean.Basic

set_option maxHeartbeats 800000

namespace PokemonLean.TypeChart

open PokemonLean

-- ============================================================================
-- EFFECTIVENESS LEVELS
-- ============================================================================

/-- Effectiveness multiplier represented as a scaled natural number (×10).
    So 0 = immune, 5 = not very effective, 10 = normal, 20 = super effective -/
inductive Effectiveness
  | immune      -- 0×
  | notVery     -- 0.5×
  | normal      -- 1×
  | superEffect -- 2×
  deriving Repr, BEq, DecidableEq

def Effectiveness.toNat10 : Effectiveness → Nat
  | .immune      => 0
  | .notVery     => 5
  | .normal      => 10
  | .superEffect => 20

-- ============================================================================
-- TYPE EFFECTIVENESS CHART (11×11)
-- ============================================================================

/-- Full type chart: effectiveness of attacker type against defender type.
    Based on Pokémon TCG rules simplified to 11 types. -/
def effectiveness : EnergyType → EnergyType → Effectiveness
  -- Fire attacks
  | .fire, .grass     => .superEffect
  | .fire, .metal     => .superEffect
  | .fire, .fairy     => .superEffect
  | .fire, .water     => .notVery
  | .fire, .fire      => .notVery
  | .fire, .dragon    => .notVery
  -- Water attacks
  | .water, .fire     => .superEffect
  | .water, .water    => .notVery
  | .water, .grass    => .notVery
  | .water, .dragon   => .notVery
  -- Grass attacks
  | .grass, .water    => .superEffect
  | .grass, .grass    => .notVery
  | .grass, .fire     => .notVery
  | .grass, .dragon   => .notVery
  -- Electric attacks
  | .lightning, .water    => .superEffect
  | .lightning, .lightning => .notVery
  | .lightning, .grass    => .notVery
  | .lightning, .dragon   => .notVery
  -- Psychic attacks
  | .psychic, .fighting => .superEffect
  | .psychic, .psychic  => .notVery
  | .psychic, .dark     => .immune
  -- Fighting attacks
  | .fighting, .lightning => .superEffect
  | .fighting, .metal    => .superEffect
  | .fighting, .psychic  => .notVery
  | .fighting, .fairy    => .notVery
  -- Dark attacks
  | .dark, .psychic   => .superEffect
  | .dark, .dark       => .notVery
  | .dark, .fairy      => .notVery
  | .dark, .fighting   => .notVery
  -- Metal attacks
  | .metal, .fairy    => .superEffect
  | .metal, .fire     => .notVery
  | .metal, .water    => .notVery
  | .metal, .lightning => .notVery
  | .metal, .metal    => .notVery
  -- Dragon attacks
  | .dragon, .dragon  => .superEffect
  | .dragon, .metal   => .notVery
  | .dragon, .fairy   => .immune
  -- Fairy attacks
  | .fairy, .dragon   => .superEffect
  | .fairy, .dark     => .superEffect
  | .fairy, .fighting => .superEffect
  | .fairy, .fire     => .notVery
  | .fairy, .metal    => .notVery
  -- Colorless: no special advantages or disadvantages
  | .colorless, _     => .normal
  -- Default: normal effectiveness
  | _, _              => .normal

-- ============================================================================
-- MULTIPLIER COMPUTATION
-- ============================================================================

/-- Apply effectiveness to base damage (scaled by 10, then divide) -/
def applyEffectiveness (baseDamage : Nat) (eff : Effectiveness) : Nat :=
  baseDamage * eff.toNat10 / 10

/-- Apply weakness from the existing Card structure -/
def applyWeakness (damage : Nat) (attackType : EnergyType) (w : Option Weakness) : Nat :=
  match w with
  | none => damage
  | some weakness =>
    if weakness.energyType == attackType then damage * weakness.multiplier
    else damage

/-- Apply resistance from the existing Card structure -/
def applyResistance (damage : Nat) (attackType : EnergyType) (r : Option Resistance) : Nat :=
  match r with
  | none => damage
  | some resistance =>
    if resistance.energyType == attackType then damage - resistance.amount
    else damage

/-- Full damage calculation: base × chart effectiveness, then weakness, then resistance -/
def calcDamage (baseDamage : Nat) (attackType defenderType : EnergyType)
    (w : Option Weakness) (r : Option Resistance) : Nat :=
  let chartDamage := applyEffectiveness baseDamage (effectiveness attackType defenderType)
  let afterWeak := applyWeakness chartDamage attackType w
  applyResistance afterWeak attackType r

-- ============================================================================
-- WEAKNESS / RESISTANCE DERIVED FROM CHART
-- ============================================================================

/-- A type is weak to another if the chart says super effective -/
def isWeakTo (defender attacker : EnergyType) : Prop :=
  effectiveness attacker defender = .superEffect

/-- A type resists another if the chart says not very effective -/
def isResistantTo (defender attacker : EnergyType) : Prop :=
  effectiveness attacker defender = .notVery

/-- A type is immune to another if the chart says immune -/
def isImmuneTo (defender attacker : EnergyType) : Prop :=
  effectiveness attacker defender = .immune

instance (defender attacker : EnergyType) : Decidable (isWeakTo defender attacker) :=
  inferInstanceAs (Decidable (effectiveness attacker defender = .superEffect))

instance (defender attacker : EnergyType) : Decidable (isResistantTo defender attacker) :=
  inferInstanceAs (Decidable (effectiveness attacker defender = .notVery))

instance (defender attacker : EnergyType) : Decidable (isImmuneTo defender attacker) :=
  inferInstanceAs (Decidable (effectiveness attacker defender = .immune))

-- ============================================================================
-- DUAL-TYPE SUPPORT
-- ============================================================================

/-- Combine two effectiveness values (multiply the ×10 values, then normalize) -/
def combineEffectiveness (e1 e2 : Effectiveness) : Nat :=
  e1.toNat10 * e2.toNat10

/-- Effectiveness against a dual-type Pokémon.
    Result is the product of effectiveness against each type (scaled by 100).
    So 100 = normal, 200 = super, 50 = not very, 400 = double super, 0 = immune -/
def dualTypeEffectiveness (attackType type1 type2 : EnergyType) : Nat :=
  combineEffectiveness (effectiveness attackType type1) (effectiveness attackType type2)

/-- Apply dual-type effectiveness to base damage (result × 100, divide by 100) -/
def applyDualTypeEffectiveness (baseDamage : Nat) (attackType type1 type2 : EnergyType) : Nat :=
  baseDamage * dualTypeEffectiveness attackType type1 type2 / 100

-- ============================================================================
-- CORE MATCHUP THEOREMS: FIRE/WATER/GRASS TRIANGLE
-- ============================================================================


-- ============================================================================
-- ELECTRIC / PSYCHIC / FIGHTING / DARK / METAL / DRAGON / FAIRY MATCHUPS
-- ============================================================================


-- ============================================================================
-- IMMUNITY THEOREMS
-- ============================================================================


-- ============================================================================
-- NO TYPE IS WEAK TO ITSELF
-- ============================================================================


/-- Dragon is the unique type that is super effective against itself -/

theorem no_type_super_against_self_except_dragon (t : EnergyType) (hNotDragon : t ≠ .dragon) :
    effectiveness t t ≠ .superEffect := by
  cases t <;> first | decide | (exfalso; exact hNotDragon rfl)

-- ============================================================================
-- COLORLESS THEOREMS
-- ============================================================================

theorem colorless_always_normal (t : EnergyType) :
    effectiveness .colorless t = .normal := by
  cases t <;> rfl

theorem colorless_no_weakness (t : EnergyType) :
    ¬isWeakTo .colorless t := by
  intro h
  unfold isWeakTo at h
  cases t <;> simp [effectiveness] at h

theorem colorless_no_resistance (t : EnergyType) :
    ¬isResistantTo .colorless t := by
  intro h
  unfold isResistantTo at h
  cases t <;> simp [effectiveness] at h

theorem colorless_no_immunity (t : EnergyType) :
    ¬isImmuneTo .colorless t := by
  intro h
  unfold isImmuneTo at h
  cases t <;> simp [effectiveness] at h

-- ============================================================================
-- EFFECTIVENESS MULTIPLIER THEOREMS
-- ============================================================================

@[simp] theorem effectiveness_immune_toNat10 : Effectiveness.immune.toNat10 = 0 := rfl
@[simp] theorem effectiveness_notVery_toNat10 : Effectiveness.notVery.toNat10 = 5 := rfl
@[simp] theorem effectiveness_normal_toNat10 : Effectiveness.normal.toNat10 = 10 := rfl
@[simp] theorem effectiveness_super_toNat10 : Effectiveness.superEffect.toNat10 = 20 := rfl

theorem applyEffectiveness_normal (d : Nat) :
    applyEffectiveness d .normal = d := by
  simp [applyEffectiveness]

theorem applyEffectiveness_immune (d : Nat) :
    applyEffectiveness d .immune = 0 := by
  simp [applyEffectiveness]

theorem applyEffectiveness_super_double (d : Nat) :
    applyEffectiveness d .superEffect = d * 2 := by
  simp [applyEffectiveness]
  omega

-- ============================================================================
-- WEAKNESS / RESISTANCE APPLICATION THEOREMS
-- ============================================================================


theorem applyWeakness_match (d : Nat) (t : EnergyType) (w : Weakness)
    (hMatch : (w.energyType == t) = true) :
    applyWeakness d t (some w) = d * w.multiplier := by
  simp [applyWeakness, hMatch]

theorem applyWeakness_nomatch (d : Nat) (t : EnergyType) (w : Weakness)
    (hNoMatch : (w.energyType == t) = false) :
    applyWeakness d t (some w) = d := by
  simp [applyWeakness, hNoMatch]

theorem applyResistance_match (d : Nat) (t : EnergyType) (r : Resistance)
    (hMatch : (r.energyType == t) = true) :
    applyResistance d t (some r) = d - r.amount := by
  simp [applyResistance, hMatch]

theorem applyResistance_nomatch (d : Nat) (t : EnergyType) (r : Resistance)
    (hNoMatch : (r.energyType == t) = false) :
    applyResistance d t (some r) = d := by
  simp [applyResistance, hNoMatch]

-- ============================================================================
-- DUAL-TYPE THEOREMS
-- ============================================================================

theorem dualType_immune_if_first_immune (attackType type1 type2 : EnergyType)
    (h : effectiveness attackType type1 = .immune) :
    dualTypeEffectiveness attackType type1 type2 = 0 := by
  simp [dualTypeEffectiveness, combineEffectiveness, h]

theorem dualType_immune_if_second_immune (attackType type1 type2 : EnergyType)
    (h : effectiveness attackType type2 = .immune) :
    dualTypeEffectiveness attackType type1 type2 = 0 := by
  simp [dualTypeEffectiveness, combineEffectiveness, h]

theorem dualType_normal_normal (attackType type1 type2 : EnergyType)
    (h1 : effectiveness attackType type1 = .normal)
    (h2 : effectiveness attackType type2 = .normal) :
    dualTypeEffectiveness attackType type1 type2 = 100 := by
  simp [dualTypeEffectiveness, combineEffectiveness, h1, h2]

theorem dualType_double_super (attackType type1 type2 : EnergyType)
    (h1 : effectiveness attackType type1 = .superEffect)
    (h2 : effectiveness attackType type2 = .superEffect) :
    dualTypeEffectiveness attackType type1 type2 = 400 := by
  simp [dualTypeEffectiveness, combineEffectiveness, h1, h2]

-- ============================================================================
-- TRIANGLE CONSISTENCY THEOREMS
-- ============================================================================

/-- The fire-water-grass triangle: each type beats the next -/
theorem triangle_fire_water_grass :
    effectiveness .fire .grass = .superEffect ∧
    effectiveness .water .fire = .superEffect ∧
    effectiveness .grass .water = .superEffect := by
  exact ⟨by decide, by decide, by decide⟩

/-- The triangle is also reflected in resistances -/
theorem triangle_resistance :
    effectiveness .fire .water = .notVery ∧
    effectiveness .water .grass = .notVery ∧
    effectiveness .grass .fire = .notVery := by
  exact ⟨by decide, by decide, by decide⟩

/-- Every type has at least one type it's super effective against
    (except colorless, which is normal against everything) -/
theorem every_noncolorless_has_advantage (t : EnergyType) (hNonColorless : t ≠ .colorless) :
    ∃ u : EnergyType, effectiveness t u = .superEffect := by
  cases t with
  | fire      => exact ⟨.grass, by decide⟩
  | water     => exact ⟨.fire, by decide⟩
  | grass     => exact ⟨.water, by decide⟩
  | lightning => exact ⟨.water, by decide⟩
  | psychic   => exact ⟨.fighting, by decide⟩
  | fighting  => exact ⟨.lightning, by decide⟩
  | dark      => exact ⟨.psychic, by decide⟩
  | metal     => exact ⟨.fairy, by decide⟩
  | dragon    => exact ⟨.dragon, by decide⟩
  | fairy     => exact ⟨.dragon, by decide⟩
  | colorless => exact absurd rfl hNonColorless

/-- Effectiveness toNat10 is always one of the four valid values -/
theorem effectiveness_values (e : Effectiveness) :
    e.toNat10 = 0 ∨ e.toNat10 = 5 ∨ e.toNat10 = 10 ∨ e.toNat10 = 20 := by
  cases e <;> simp [Effectiveness.toNat10]

/-- Super effective deals more damage than normal -/
theorem super_gt_normal (d : Nat) (hd : 0 < d) :
    applyEffectiveness d .superEffect > applyEffectiveness d .normal := by
  simp [applyEffectiveness]
  omega

/-- Normal deals more damage than not very effective -/
theorem normal_gt_notVery (d : Nat) (hd : 1 < d) :
    applyEffectiveness d .normal > applyEffectiveness d .notVery := by
  simp [applyEffectiveness]
  omega

/-- Immune always does zero damage -/
theorem immune_zero_damage (d : Nat) :
    applyEffectiveness d .immune = 0 := by
  simp [applyEffectiveness]

end PokemonLean.TypeChart
