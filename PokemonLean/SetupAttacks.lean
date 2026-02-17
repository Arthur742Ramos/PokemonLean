/-
  PokemonLean / SetupAttacks.lean

  Setup attack mechanics for Pokémon TCG formalised in Lean 4.
  Swords Dance (+damage), Dragon Dance (+speed+attack), setup vs
  immediate damage trade-off, setup sweeper strategy, reset mechanics
  (switching resets boosts), boost stacking limits.

  All proofs are sorry-free.  Uses computational paths for
  turn-by-turn state transitions.
  Multi-step trans / symm / congrArg chains — paths ARE the math.
  25+ theorems.
-/

set_option linter.unusedVariables false

namespace PokemonLean.SetupAttacks

-- ============================================================
-- §1  Computational Path Infrastructure
-- ============================================================

inductive Step (α : Type) : α → α → Type where
  | refl : (a : α) → Step α a a
  | rule : (name : String) → (a b : α) → Step α a b

inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

def Path.trans : Path α a b → Path α b c → Path α a c
  | .nil _,    q => q
  | .cons s p, q => .cons s (p.trans q)

def Path.single (s : Step α a b) : Path α a b :=
  .cons s (.nil _)

def Step.symm : Step α a b → Step α b a
  | .refl a     => .refl a
  | .rule n a b => .rule (n ++ "⁻¹") b a

def Path.symm : Path α a b → Path α b a
  | .nil a    => .nil a
  | .cons s p => p.symm.trans (.cons s.symm (.nil _))

def Path.length : Path α a b → Nat
  | .nil _    => 0
  | .cons _ p => 1 + p.length

theorem path_trans_assoc (p : Path α a b) (q : Path α b c) (r : Path α c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  induction p with
  | nil _ => simp [Path.trans]
  | cons s _ ih => simp [Path.trans, ih]

theorem path_trans_nil_right (p : Path α a b) :
    Path.trans p (.nil b) = p := by
  induction p with
  | nil _ => simp [Path.trans]
  | cons s _ ih => simp [Path.trans, ih]

theorem path_length_trans (p : Path α a b) (q : Path α b c) :
    (Path.trans p q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [Path.trans, Path.length]
  | cons s _ ih => simp [Path.trans, Path.length, ih, Nat.add_assoc]

-- ============================================================
-- §2  Core Types: Boosts, Pokémon State
-- ============================================================

/-- Stat boost levels (-6 to +6 in the games). -/
structure Boosts where
  attack  : Int
  speed   : Int
  defense : Int
deriving DecidableEq, Repr

def Boosts.zero : Boosts := ⟨0, 0, 0⟩

/-- Clamp a boost to the [-6, +6] range. -/
def clampBoost (n : Int) : Int :=
  if n > 6 then 6 else if n < -6 then -6 else n

/-- Apply clamp to all boosts. -/
def Boosts.clamp (b : Boosts) : Boosts :=
  ⟨clampBoost b.attack, clampBoost b.speed, clampBoost b.defense⟩

/-- A Pokémon's battle state (simplified). -/
structure PokemonState where
  name    : String
  hp      : Nat
  baseAtk : Nat
  baseSpd : Nat
  baseDef : Nat
  boosts  : Boosts
  isActive : Bool    -- on the field or benched
deriving DecidableEq, Repr

/-- Effective attack: base + boost modifier. -/
def effectiveAtk (s : PokemonState) : Int :=
  s.baseAtk + s.boosts.attack * 10   -- simplified: each boost stage = +10

/-- Effective speed. -/
def effectiveSpd (s : PokemonState) : Int :=
  s.baseSpd + s.boosts.speed * 10

-- ============================================================
-- §3  Setup Moves as Steps
-- ============================================================

/-- Apply Swords Dance: +2 attack boost. -/
def swordsDance (s : PokemonState) : PokemonState :=
  { s with boosts := { s.boosts with attack := clampBoost (s.boosts.attack + 2) } }

/-- Apply Dragon Dance: +1 attack, +1 speed. -/
def dragonDance (s : PokemonState) : PokemonState :=
  { s with boosts := { s.boosts with
      attack := clampBoost (s.boosts.attack + 1)
      speed  := clampBoost (s.boosts.speed + 1) } }

/-- Apply Iron Defense: +2 defense. -/
def ironDefense (s : PokemonState) : PokemonState :=
  { s with boosts := { s.boosts with defense := clampBoost (s.boosts.defense + 2) } }

/-- Reset all boosts (e.g., on switch). -/
def resetBoosts (s : PokemonState) : PokemonState :=
  { s with boosts := Boosts.zero, isActive := false }

/-- Switch in: activate with zero boosts. -/
def switchIn (s : PokemonState) : PokemonState :=
  { s with isActive := true, boosts := Boosts.zero }

/-- Step types for setup moves. -/
def swordsDanceStep (s : PokemonState) :
    Step PokemonState s (swordsDance s) :=
  .rule "swords-dance" _ _

def dragonDanceStep (s : PokemonState) :
    Step PokemonState s (dragonDance s) :=
  .rule "dragon-dance" _ _

def ironDefenseStep (s : PokemonState) :
    Step PokemonState s (ironDefense s) :=
  .rule "iron-defense" _ _

def switchOutStep (s : PokemonState) :
    Step PokemonState s (resetBoosts s) :=
  .rule "switch-out" _ _

def switchInStep (s : PokemonState) :
    Step PokemonState s (switchIn s) :=
  .rule "switch-in" _ _

-- ============================================================
-- §4  Core Theorems: Boost Mechanics
-- ============================================================

/-- Theorem 1: Swords Dance increases attack boost by 2 (from zero). -/
theorem swords_dance_from_zero (s : PokemonState) (h : s.boosts.attack = 0) :
    (swordsDance s).boosts.attack = 2 := by
  simp [swordsDance, clampBoost, h]

/-- Theorem 2: Dragon Dance increases attack by 1 and speed by 1 from zero. -/
theorem dragon_dance_from_zero (s : PokemonState)
    (ha : s.boosts.attack = 0) (hs : s.boosts.speed = 0) :
    (dragonDance s).boosts.attack = 1 ∧ (dragonDance s).boosts.speed = 1 := by
  constructor <;> simp [dragonDance, clampBoost, ha, hs]

/-- Theorem 3: Switching out resets attack boost to 0. -/
theorem switch_resets_attack (s : PokemonState) :
    (resetBoosts s).boosts.attack = 0 := by
  simp [resetBoosts, Boosts.zero]

/-- Theorem 4: Switching out resets speed boost to 0. -/
theorem switch_resets_speed (s : PokemonState) :
    (resetBoosts s).boosts.speed = 0 := by
  simp [resetBoosts, Boosts.zero]

/-- Theorem 5: Switching out resets defense boost to 0. -/
theorem switch_resets_defense (s : PokemonState) :
    (resetBoosts s).boosts.defense = 0 := by
  simp [resetBoosts, Boosts.zero]

/-- Theorem 6: Clamp at max — boost can't exceed 6. -/
theorem clamp_upper (n : Int) : clampBoost n ≤ 6 := by
  simp [clampBoost]
  split
  · omega
  · split <;> omega

/-- Theorem 7: Clamp at min — boost can't go below -6. -/
theorem clamp_lower (n : Int) : clampBoost n ≥ -6 := by
  simp [clampBoost]
  split
  · omega
  · split <;> omega

/-- Theorem 8: Triple Swords Dance can't exceed +6. -/
theorem triple_swords_dance_capped (s : PokemonState) (h : s.boosts.attack = 0) :
    (swordsDance (swordsDance (swordsDance s))).boosts.attack = 6 := by
  simp [swordsDance, clampBoost, h]

-- ============================================================
-- §5  Setup Path Constructions
-- ============================================================

/-- 1: Swords Dance path (single step). -/
def swords_dance_path (s : PokemonState) :
    Path PokemonState s (swordsDance s) :=
  Path.single (swordsDanceStep s)

/-- 2: Dragon Dance path (single step). -/
def dragon_dance_path (s : PokemonState) :
    Path PokemonState s (dragonDance s) :=
  Path.single (dragonDanceStep s)

/-- 3: Double Swords Dance (2-step trans chain). -/
def double_swords_dance (s : PokemonState) :
    Path PokemonState s (swordsDance (swordsDance s)) :=
  (swords_dance_path s).trans (swords_dance_path (swordsDance s))

/-- 4: Triple Swords Dance (3-step trans chain). -/
def triple_swords_dance (s : PokemonState) :
    Path PokemonState s (swordsDance (swordsDance (swordsDance s))) :=
  (double_swords_dance s).trans (swords_dance_path (swordsDance (swordsDance s)))

/-- 5: Setup then switch-out (2-step: boost then lose it). -/
def setup_then_switch (s : PokemonState) :
    Path PokemonState s (resetBoosts (swordsDance s)) :=
  (swords_dance_path s).trans (Path.single (switchOutStep (swordsDance s)))

/-- 6: Dragon Dance x2 chain. -/
def double_dragon_dance (s : PokemonState) :
    Path PokemonState s (dragonDance (dragonDance s)) :=
  (dragon_dance_path s).trans (dragon_dance_path (dragonDance s))

-- ============================================================
-- §6  Path Length Theorems
-- ============================================================

/-- Theorem 9: Single setup is 1 step. -/
theorem swords_dance_len (s : PokemonState) :
    (swords_dance_path s).length = 1 := by
  simp [swords_dance_path, Path.single, Path.length]

/-- Theorem 10: Double setup is 2 steps. -/
theorem double_sd_len (s : PokemonState) :
    (double_swords_dance s).length = 2 := by
  simp [double_swords_dance, swords_dance_path, Path.trans,
        Path.single, Path.length]

/-- Theorem 11: Triple setup is 3 steps. -/
theorem triple_sd_len (s : PokemonState) :
    (triple_swords_dance s).length = 3 := by
  simp [triple_swords_dance, double_swords_dance, swords_dance_path,
        Path.trans, Path.single, Path.length]

/-- Theorem 12: Setup-then-switch is 2 steps. -/
theorem setup_switch_len (s : PokemonState) :
    (setup_then_switch s).length = 2 := by
  simp [setup_then_switch, swords_dance_path, switchOutStep,
        Path.trans, Path.single, Path.length]

/-- Theorem 13: Double Dragon Dance is 2 steps. -/
theorem double_dd_len (s : PokemonState) :
    (double_dragon_dance s).length = 2 := by
  simp [double_dragon_dance, dragon_dance_path, Path.trans,
        Path.single, Path.length]

-- ============================================================
-- §7  Setup vs. Immediate Damage Trade-off
-- ============================================================

/-- Damage dealt by attacking directly. -/
def immediateDamage (s : PokemonState) (movePower : Nat) : Nat :=
  movePower + s.baseAtk

/-- Damage after one Swords Dance then attacking. -/
def setupOneDamage (s : PokemonState) (movePower : Nat) : Int :=
  movePower + (effectiveAtk (swordsDance s))

/-- Theorem 14: Setup damage exceeds immediate damage (from zero boosts). -/
theorem setup_better_damage (s : PokemonState) (movePower : Nat)
    (h : s.boosts.attack = 0) :
    setupOneDamage s movePower = movePower + (s.baseAtk : Int) + 20 := by
  simp [setupOneDamage, effectiveAtk, swordsDance, clampBoost, h]
  omega

/-- Theorem 15: With zero boosts, immediate damage = movePower + baseAtk. -/
theorem immediate_damage_calc (s : PokemonState) (movePower : Nat) :
    immediateDamage s movePower = movePower + s.baseAtk := by
  simp [immediateDamage]

-- ============================================================
-- §8  Setup Sweeper Strategy
-- ============================================================

/-- A setup sweep: multiple turns of setup followed by attacks. -/
structure SetupSweep where
  setupTurns  : Nat
  attackTurns : Nat
  boostPerSetup : Int  -- attack boost gained per setup turn

/-- Total effective boost after setup (clamped). -/
def totalBoost (sw : SetupSweep) : Int :=
  clampBoost (sw.boostPerSetup * sw.setupTurns)

/-- Theorem 16: Zero setup turns means zero boost. -/
theorem zero_setup_no_boost (sw : SetupSweep) (h : sw.setupTurns = 0) :
    totalBoost sw = 0 := by
  simp [totalBoost, h, clampBoost]

/-- Theorem 17: One Swords Dance sweep has boost 2 (clamped). -/
theorem one_sd_sweep_boost :
    totalBoost ⟨1, 3, 2⟩ = 2 := by
  simp [totalBoost, clampBoost]

/-- Theorem 18: Three Swords Dance sweep caps at 6. -/
theorem three_sd_sweep_cap :
    totalBoost ⟨3, 3, 2⟩ = 6 := by
  simp [totalBoost, clampBoost]

/-- Theorem 19: Four Swords Dance also caps at 6. -/
theorem four_sd_sweep_same :
    totalBoost ⟨4, 3, 2⟩ = 6 := by
  simp [totalBoost, clampBoost]

-- ============================================================
-- §9  Symm and Multi-step Coherence
-- ============================================================

/-- 7: Reversed swords dance path. -/
def swords_dance_rev (s : PokemonState) :
    Path PokemonState (swordsDance s) s :=
  (swords_dance_path s).symm

/-- Theorem 20: Reversed path has length 1. -/
theorem swords_dance_rev_len (s : PokemonState) :
    (swords_dance_rev s).length = 1 := by
  simp [swords_dance_rev, Path.symm, swords_dance_path, Path.single,
        swordsDanceStep, Step.symm, Path.trans, Path.length]

/-- 8: Setup-reset cycle: setup, then switch out (boosts lost), then switch in. -/
def setup_reset_cycle (s : PokemonState) :
    Path PokemonState s (switchIn (resetBoosts (swordsDance s))) :=
  let p1 := swords_dance_path s
  let p2 := Path.single (switchOutStep (swordsDance s))
  let p3 := Path.single (switchInStep (resetBoosts (swordsDance s)))
  p1.trans (p2.trans p3)

/-- Theorem 21: Setup-reset cycle is 3 steps. -/
theorem setup_reset_cycle_len (s : PokemonState) :
    (setup_reset_cycle s).length = 3 := by
  simp [setup_reset_cycle, swords_dance_path, switchOutStep, switchInStep,
        Path.trans, Path.single, Path.length]

/-- Theorem 22: After setup-reset cycle, attack boost is 0. -/
theorem setup_reset_zeroes_atk (s : PokemonState) :
    (switchIn (resetBoosts (swordsDance s))).boosts.attack = 0 := by
  simp [switchIn, resetBoosts, Boosts.zero]

/-- Theorem 23: After setup-reset cycle, speed boost is 0. -/
theorem setup_reset_zeroes_spd (s : PokemonState) :
    (switchIn (resetBoosts (swordsDance s))).boosts.speed = 0 := by
  simp [switchIn, resetBoosts, Boosts.zero]

-- ============================================================
-- §10  Stacking Limits & Additional Coherence
-- ============================================================

/-- Theorem 24: Clamp is idempotent. -/
theorem clamp_idempotent (n : Int) :
    clampBoost (clampBoost n) = clampBoost n := by
  simp only [clampBoost]
  split <;> split <;> (first | rfl | (split <;> omega))

/-- Theorem 25: Iron defense from zero gives +2 defense. -/
theorem iron_defense_from_zero (s : PokemonState) (h : s.boosts.defense = 0) :
    (ironDefense s).boosts.defense = 2 := by
  simp [ironDefense, clampBoost, h]

/-- Theorem 26: Dragon Dance doesn't change defense. -/
theorem dd_preserves_defense (s : PokemonState) :
    (dragonDance s).boosts.defense = s.boosts.defense := by
  simp [dragonDance]

/-- Theorem 27: Swords Dance doesn't change speed. -/
theorem sd_preserves_speed (s : PokemonState) :
    (swordsDance s).boosts.speed = s.boosts.speed := by
  simp [swordsDance]

/-- Theorem 28: Switch-in sets isActive to true. -/
theorem switch_in_active (s : PokemonState) :
    (switchIn s).isActive = true := by
  simp [switchIn]

/-- Theorem 29: Switch-out sets isActive to false. -/
theorem switch_out_inactive (s : PokemonState) :
    (resetBoosts s).isActive = false := by
  simp [resetBoosts]

/-- Theorem 30: Effective attack strictly increases with swords dance (from 0 boost). -/
theorem eff_atk_increases (s : PokemonState) (h : s.boosts.attack = 0) :
    effectiveAtk (swordsDance s) = effectiveAtk s + 20 := by
  simp [effectiveAtk, swordsDance, clampBoost, h]

end PokemonLean.SetupAttacks
