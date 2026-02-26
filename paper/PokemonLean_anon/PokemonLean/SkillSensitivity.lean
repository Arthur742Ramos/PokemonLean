/-
  PokemonLean/SkillSensitivity.lean — Player-skill sensitivity bounds

  Reviewer question: "How large must a skill confound be to reverse the paradox?"

  Model: if Dragapult's observed matchup WRs are uniformly depressed by `b`
  percentage points due to weaker pilots, the true expected WR would be
  `dragapultExpectedWR + b/1000`. We find tight integer thresholds.

  Key results:
  - Break-even threshold: b ∈ (33, 34] — Dragapult needs ≥3.4pp boost for 50%
  - Grimmsnarl-matching threshold: b ∈ (60, 61] — needs ≥6.1pp to match best deck
-/
import PokemonLean.FullReplicator

namespace PokemonLean.SkillSensitivity

open PokemonLean.NashEquilibrium
open PokemonLean.RealMetagame
open PokemonLean.EvolutionaryDynamics
open PokemonLean.FullReplicator

-- ============================================================================
-- UNADJUSTED EXPECTED WIN RATES
-- ============================================================================

/-- Dragapult's unadjusted expected field win rate (rational, 0–1 scale). -/
def dragapultExpectedWR : Rat :=
  fitness 14 fullPayoff normalizedShares ixDragapult

/-- Grimmsnarl's unadjusted expected field win rate (rational, 0–1 scale). -/
def grimmsnarlExpectedWR : Rat :=
  fitness 14 fullPayoff normalizedShares ixGrimmsnarl

-- ============================================================================
-- BASELINE: THE PARADOX EXISTS
-- ============================================================================

/-- Dragapult's expected WR is below 50%. -/
theorem dragapult_below_breakeven :
    dragapultExpectedWR < 1/2 := by native_decide

/-- Grimmsnarl's expected WR is above 50%. -/
theorem grimmsnarl_above_breakeven :
    grimmsnarlExpectedWR > 1/2 := by native_decide

/-- The paradox gap: Grimmsnarl's expected WR exceeds Dragapult's. -/
theorem paradox_gap :
    dragapultExpectedWR < grimmsnarlExpectedWR := by native_decide

-- ============================================================================
-- BREAK-EVEN THRESHOLD: 3.4 percentage points
-- Adding a uniform bias b to all Dragapult matchup WRs shifts the expected
-- field WR by exactly b/1000 (since normalized shares sum to 1).
-- ============================================================================

/-- With a 3.4pp uniform skill boost, Dragapult reaches break-even (≥50%). -/
theorem skill_threshold_breakeven :
    dragapultExpectedWR + 34/1000 ≥ 1/2 := by native_decide

/-- But 3.3pp is NOT enough — Dragapult stays below 50%. -/
theorem skill_threshold_breakeven_tight :
    dragapultExpectedWR + 33/1000 < 1/2 := by native_decide

-- ============================================================================
-- GRIMMSNARL-MATCHING THRESHOLD: 6.1 percentage points
-- ============================================================================

/-- With a 6.1pp uniform skill boost, Dragapult matches Grimmsnarl's WR. -/
theorem skill_threshold_match_grimmsnarl :
    dragapultExpectedWR + 61/1000 ≥ grimmsnarlExpectedWR := by native_decide

/-- But 6.0pp is NOT enough — Dragapult remains below Grimmsnarl. -/
theorem skill_threshold_match_grimmsnarl_tight :
    dragapultExpectedWR + 60/1000 < grimmsnarlExpectedWR := by native_decide

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-- Summary: the popularity paradox requires at least a 3.4pp uniform skill
    confound to reach break-even, and 6.1pp to match Grimmsnarl. -/
theorem skill_sensitivity_summary :
    dragapultExpectedWR + 34/1000 ≥ 1/2 ∧
    dragapultExpectedWR + 33/1000 < 1/2 ∧
    dragapultExpectedWR + 61/1000 ≥ grimmsnarlExpectedWR ∧
    dragapultExpectedWR + 60/1000 < grimmsnarlExpectedWR := by
  exact ⟨skill_threshold_breakeven, skill_threshold_breakeven_tight,
         skill_threshold_match_grimmsnarl, skill_threshold_match_grimmsnarl_tight⟩

end PokemonLean.SkillSensitivity
