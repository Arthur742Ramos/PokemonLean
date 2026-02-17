/-
  PokemonLean / Core / DamageCalc.lean

  Pokémon TCG damage calculation pipeline formalised in Lean 4.
  Self-contained: defines minimal types inline (PType, Effectiveness).

  Pipeline stages:
    baseDamage → applyWeakness (×2) → applyResistance (−30, floor 0)
    → applyModifiers (Choice Band +30, etc.) → applyShield (−20)
    → finalDamage

  All proofs are sorry-free.  37 theorems.
-/

namespace PokemonLean.Core.DamageCalc

-- ============================================================
-- §1  Core Types (self-contained, mirrors future Core/Types.lean)
-- ============================================================

/-- Pokémon energy types (TCG). -/
inductive PType where
  | fire | water | grass | lightning | psychic | fighting
  | darkness | metal | dragon | fairy | normal | colorless
  deriving DecidableEq, Repr

/-- Type effectiveness result. -/
inductive Effectiveness where
  | weak       -- ×2 damage
  | resist     -- −30 damage
  | neutral    -- no modifier
  deriving DecidableEq, Repr

/-- Weakness chart (simplified TCG type matchups). -/
def typeChart : PType → PType → Effectiveness
  | .fire,      .water     => .weak
  | .water,     .grass     => .weak
  | .water,     .lightning => .weak
  | .grass,     .fire      => .weak
  | .lightning, .fighting  => .weak
  | .psychic,   .darkness  => .weak
  | .fighting,  .psychic   => .weak
  | .darkness,  .fighting  => .weak
  | .metal,     .fire      => .weak
  | .fairy,     .metal     => .weak
  | .dragon,    .dragon    => .weak
  | .fire,      .metal     => .resist
  | .grass,     .water     => .resist
  | .lightning, .metal     => .resist
  | .fighting,  .grass     => .resist
  | .metal,     .lightning => .resist
  | .fairy,     .darkness  => .resist
  | _,          _          => .neutral

/-- Modifier item attached to the attacking Pokémon. -/
inductive AttackModifier where
  | choiceBand    -- +30 to V/GX/EX
  | muscleBand    -- +20 to all
  | none
  deriving DecidableEq, Repr

/-- Defensive item attached to the defending Pokémon. -/
inductive DefenseModifier where
  | bigCharm      -- effectively +30 HP (modelled as −30 damage)
  | protectiveGoggles  -- negate bench damage (not modelled here)
  | none
  deriving DecidableEq, Repr

-- ============================================================
-- §2  Pipeline Stage Functions
-- ============================================================

/-- Stage 1: Apply weakness (×2). -/
def applyWeakness (base : Nat) (eff : Effectiveness) : Nat :=
  match eff with
  | .weak    => base * 2
  | _        => base

/-- Stage 2: Apply resistance (−30, floored at 0). -/
def applyResistance (dmg : Nat) (eff : Effectiveness) : Nat :=
  match eff with
  | .resist  => if dmg ≥ 30 then dmg - 30 else 0
  | _        => dmg

/-- Stage 3: Apply attack modifier (Choice Band +30, Muscle Band +20). -/
def applyModifier (dmg : Nat) (m : AttackModifier) : Nat :=
  match m with
  | .choiceBand  => dmg + 30
  | .muscleBand  => dmg + 20
  | .none        => dmg

/-- Stage 4: Apply defensive shield (Big Charm: −30, floored at 0). -/
def applyShield (dmg : Nat) (d : DefenseModifier) : Nat :=
  match d with
  | .bigCharm => if dmg ≥ 30 then dmg - 30 else 0
  | _         => dmg

/-- Stage 5: Final floor at 0 (always non-negative). -/
def floorZero (d : Int) : Nat :=
  if d < 0 then 0 else d.toNat

/-- Full damage pipeline. -/
def fullPipeline (base : Nat) (eff : Effectiveness)
    (atkMod : AttackModifier) (defMod : DefenseModifier) : Nat :=
  let d1 := applyWeakness base eff
  let d2 := applyResistance d1 eff
  let d3 := applyModifier d2 atkMod
  applyShield d3 defMod

/-- Double weakness for dual-type (×4 effective). -/
def applyDoubleWeakness (base : Nat) (eff1 eff2 : Effectiveness) : Nat :=
  applyWeakness (applyWeakness base eff1) eff2

/-- Double resistance (−30 twice = −60, floored at 0). -/
def applyDoubleResistance (dmg : Nat) (eff1 eff2 : Effectiveness) : Nat :=
  applyResistance (applyResistance dmg eff1) eff2

-- ============================================================
-- §3  Worked Examples — Specific Pokémon Matchups
-- ============================================================

/-- Example: Charizard (Fire) attacks Venusaur (Grass).
    Venusaur is weak to Fire. 130 base × 2 = 260. -/
def charizardVsVenusaur : Nat :=
  fullPipeline 130 .weak .none .none

/-- Example: Blastoise (Water) attacks Charizard (Fire).
    Charizard is weak to Water. 120 base × 2 = 240. -/
def blastoiseVsCharizard : Nat :=
  fullPipeline 120 .weak .none .none

/-- Example: Pikachu (Lightning) attacks Geodude (Fighting).
    Geodude has resistance to Lightning.
    40 base − 30 resist = 10. -/
def pikachuVsGeodude : Nat :=
  fullPipeline 40 .resist .none .none

/-- Example: Gardevoir (Psychic) attacks Umbreon (Darkness) with Muscle Band.
    Neutral matchup. 130 base + 20 Muscle Band = 150. -/
def gardevoirVsUmbreon : Nat :=
  fullPipeline 130 .neutral .muscleBand .none

/-- Example: Lucario V (Fighting) attacks Arceus VSTAR (Normal) with Choice Band.
    Neutral matchup. 120 base + 30 = 150, defender has Big Charm: 150 − 30 = 120. -/
def lucarioVsArceus : Nat :=
  fullPipeline 120 .neutral .choiceBand .bigCharm

-- ============================================================
-- §4  Weakness & Resistance Theorems
-- ============================================================

/-- Theorem 1: Weakness doubles damage. -/
theorem weakness_doubles (base : Nat) :
    applyWeakness base .weak = base * 2 := by
  rfl

/-- Theorem 2: Neutral weakness is identity. -/
theorem weakness_neutral_id (base : Nat) :
    applyWeakness base .neutral = base := by
  rfl

/-- Theorem 3: Resistance subtracts 30 when damage ≥ 30. -/
theorem resistance_sub30 (dmg : Nat) (h : dmg ≥ 30) :
    applyResistance dmg .resist = dmg - 30 := by
  simp [applyResistance, h]

/-- Theorem 4: Resistance floors at 0 for small damage. -/
theorem resistance_floor (dmg : Nat) (h : ¬(dmg ≥ 30)) :
    applyResistance dmg .resist = 0 := by
  simp [applyResistance, h]

/-- Theorem 5: Neutral resistance is identity. -/
theorem resistance_neutral_id (dmg : Nat) :
    applyResistance dmg .neutral = dmg := by
  rfl

/-- Theorem 6: Weakness before resistance: weak + resist on 60 → 60×2−30 = 90. -/
theorem weak_then_resist_60 :
    applyResistance (applyWeakness 60 .weak) .resist = 90 := by
  native_decide

/-- Theorem 7: Resistance before weakness would give (60−30)×2 = 60 — different! -/
theorem resist_then_weak_60 :
    applyWeakness (applyResistance 60 .resist) .weak = 60 := by
  native_decide

/-- Theorem 8: Order matters — weakness before resistance ≠ resistance before weakness. -/
theorem weakness_resistance_order_matters :
    applyResistance (applyWeakness 60 .weak) .resist ≠
    applyWeakness (applyResistance 60 .resist) .weak := by
  native_decide

/-- Theorem 9: Double weakness (dual type) gives ×4. -/
theorem double_weakness_x4 (base : Nat) :
    applyDoubleWeakness base .weak .weak = base * 4 := by
  simp [applyDoubleWeakness, applyWeakness, Nat.mul_assoc]

/-- Theorem 10: Double resistance on 100 subtracts 60 → 40. -/
theorem double_resistance_example :
    applyDoubleResistance 100 .resist .resist = 40 := by
  native_decide

-- ============================================================
-- §5  Modifier Theorems
-- ============================================================

/-- Theorem 11: Choice Band adds 30. -/
theorem choice_band_adds_30 (dmg : Nat) :
    applyModifier dmg .choiceBand = dmg + 30 := by
  rfl

/-- Theorem 12: Muscle Band adds 20. -/
theorem muscle_band_adds_20 (dmg : Nat) :
    applyModifier dmg .muscleBand = dmg + 20 := by
  rfl

/-- Theorem 13: No modifier is identity. -/
theorem no_modifier_id (dmg : Nat) :
    applyModifier dmg .none = dmg := by
  rfl

/-- Theorem 14: Modifiers are additive — applying Muscle Band then Choice Band
    is the same as adding 50 (on the function level). -/
theorem modifiers_additive (dmg : Nat) :
    applyModifier (applyModifier dmg .muscleBand) .choiceBand = dmg + 50 := by
  simp [applyModifier, Nat.add_assoc]

/-- Theorem 15: Big Charm subtracts 30 when damage is sufficient. -/
theorem big_charm_sub30 (dmg : Nat) (h : dmg ≥ 30) :
    applyShield dmg .bigCharm = dmg - 30 := by
  simp [applyShield, h]

/-- Theorem 16: Big Charm floors at 0 for small damage. -/
theorem big_charm_floor (dmg : Nat) (h : ¬(dmg ≥ 30)) :
    applyShield dmg .bigCharm = 0 := by
  simp [applyShield, h]

/-- Theorem 17: No defensive modifier is identity. -/
theorem no_defense_id (dmg : Nat) :
    applyShield dmg .none = dmg := by
  rfl

-- ============================================================
-- §6  Pipeline Monotonicity and Composition Theorems
-- ============================================================

/-- Theorem 18: Weakness is monotone in base damage. -/
theorem weakness_monotone (a b : Nat) (h : a ≤ b) (eff : Effectiveness) :
    applyWeakness a eff ≤ applyWeakness b eff := by
  cases eff <;> simp [applyWeakness] <;> omega

/-- Theorem 19: Modifier preserves ordering. -/
theorem modifier_monotone (a b : Nat) (h : a ≤ b) (m : AttackModifier) :
    applyModifier a m ≤ applyModifier b m := by
  cases m <;> simp [applyModifier] <;> omega

/-- Theorem 20: Damage is always ≥ 0 (trivially true for Nat, but stated for clarity). -/
theorem damage_nonneg (base : Nat) (eff : Effectiveness) (m : AttackModifier) (d : DefenseModifier) :
    0 ≤ fullPipeline base eff m d := by
  omega

/-- Theorem 21: Full pipeline with all-neutral/none is identity. -/
theorem pipeline_identity (base : Nat) :
    fullPipeline base .neutral .none .none = base := by
  rfl

-- ============================================================
-- §7  Worked Example Verification Theorems
-- ============================================================

/-- Theorem 22: Charizard (130) vs Venusaur (weak) = 260. -/
theorem verify_charizard_vs_venusaur :
    charizardVsVenusaur = 260 := by
  native_decide

/-- Theorem 23: Blastoise (120) vs Charizard (weak) = 240. -/
theorem verify_blastoise_vs_charizard :
    blastoiseVsCharizard = 240 := by
  native_decide

/-- Theorem 24: Pikachu (40) vs Geodude (resist) = 10. -/
theorem verify_pikachu_vs_geodude :
    pikachuVsGeodude = 10 := by
  native_decide

/-- Theorem 25: Gardevoir (130) vs Umbreon (neutral, Muscle Band) = 150. -/
theorem verify_gardevoir_vs_umbreon :
    gardevoirVsUmbreon = 150 := by
  native_decide

/-- Theorem 26: Lucario V (120) vs Arceus VSTAR (neutral, Choice Band, Big Charm) = 120. -/
theorem verify_lucario_vs_arceus :
    lucarioVsArceus = 120 := by
  native_decide

-- ============================================================
-- §8  Advanced Pipeline Composition Theorems
-- ============================================================

/-- Theorem 27: Weakness-only pipeline on 50 (weak matchup):
    50 × 2 = 100 (no resistance in a weak matchup). -/
theorem weak_pipeline_50 :
    fullPipeline 50 .weak .none .none = 100 := by
  native_decide

/-- Theorem 28: In a weak matchup, resistance stage is skipped
    (only resist matchup triggers the −30). -/
theorem weak_matchup_no_resist (base : Nat) :
    applyResistance (applyWeakness base .weak) .weak = base * 2 := by
  simp [applyWeakness, applyResistance]

/-- Theorem 29: Resistance on 10 base → floors at 0. -/
theorem resistance_floors_low :
    fullPipeline 10 .resist .none .none = 0 := by
  native_decide

/-- Theorem 30: Weakness + Choice Band on 60: 60×2=120, 120+30=150. -/
theorem weak_plus_choice_band :
    fullPipeline 60 .weak .choiceBand .none = 150 := by
  native_decide

/-- Theorem 31: Pipeline with everything on 90:
    90×2=180 (weak), +30 (Choice Band)=210, −30 (Big Charm)=180. -/
theorem full_pipeline_everything :
    fullPipeline 90 .weak .choiceBand .bigCharm = 180 := by
  native_decide

-- ============================================================
-- §9  Type Chart Verification
-- ============================================================

/-- Theorem 32: Fire vs Water is weak (Charizard's nightmare). -/
theorem fire_weak_to_water : typeChart .fire .water = .weak := by rfl

/-- Theorem 33: Grass resists Water (Venusaur's advantage). -/
theorem grass_resists_water : typeChart .grass .water = .resist := by rfl

/-- Theorem 34: Dragon vs Dragon is weak (Rayquaza mirror). -/
theorem dragon_weak_to_dragon : typeChart .dragon .dragon = .weak := by rfl

/-- Theorem 35: Normal vs Fire is neutral. -/
theorem normal_neutral_fire : typeChart .normal .fire = .neutral := by rfl

/-- Theorem 36: Resistance monotone for specific cases. -/
theorem resistance_monotone_example :
    applyResistance 50 .resist ≤ applyResistance 80 .resist := by
  native_decide

/-- Theorem 37: Shield monotone for specific cases. -/
theorem shield_monotone_example :
    applyShield 40 .bigCharm ≤ applyShield 70 .bigCharm := by
  native_decide

end PokemonLean.Core.DamageCalc
