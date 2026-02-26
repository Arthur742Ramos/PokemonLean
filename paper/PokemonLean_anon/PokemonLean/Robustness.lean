/-
  PokemonLean/Robustness.lean

  Formal robustness bounds for the 30.5% "Other" metagame bucket.
  All arithmetic is exact over `Rat`, with no `sorry`.
-/
import PokemonLean.TournamentStrategy

namespace PokemonLean.Robustness

open PokemonLean.NashEquilibrium (Rat)
open PokemonLean.RealMetagame
open PokemonLean.TournamentStrategy

/-- Top-14 field share from Trainer Hill data (69.5%). -/
def top14Share : Rat := 695 / 1000

/-- "Other" archetypes share from Trainer Hill data (30.5%). -/
def otherShare : Rat := 305 / 1000

/-- Total share (top-14 + other). -/
def totalShare : Rat := top14Share + otherShare

/-- Dragapult Dusknoir expected WR vs the normalized top-14 field. -/
def dragapultTop14WR : Rat := 324243 / 695000

/-- Grimmsnarl Froslass expected WR vs the normalized top-14 field. -/
def grimmsnarlTop14WR : Rat := 366061 / 695000

/-- Adjust top-14 expected WR with an assumed win rate vs `Other`. -/
def adjustedWR (topWR otherWR : Rat) : Rat :=
  (top14Share * topWR + otherShare * otherWR) / totalShare

/-- The minimum Dragapult WR vs `Other` needed to reach 50% overall. -/
def dragapultToFiftyOtherWR : Rat := 175757 / 305000

/-- The maximum Grimmsnarl WR vs `Other` that still keeps it at exactly 50% overall. -/
def grimmsnarlToFiftyOtherWR : Rat := 133939 / 305000

/-- Reversal gap on `Other` WR (Dragapult minus Grimmsnarl) for equal adjusted WR. -/
def paradoxReversalDelta : Rat := 41818 / 305000

theorem total_share_eq_one : totalShare = 1 := by decide

theorem dragapult_top14_wr_exact :
    expectedWinRateVsField .DragapultDusknoir = dragapultTop14WR := by
  simpa [dragapultTop14WR] using EXPECTED_WR_DRAGAPULT_VS_FIELD

theorem grimmsnarl_top14_wr_exact :
    expectedWinRateVsField .GrimssnarlFroslass = grimmsnarlTop14WR := by
  simpa [grimmsnarlTop14WR] using EXPECTED_WR_GRIMMSNARL_VS_FIELD

/-- Worst case for the paradox direction: Dragapult 100% vs Other, Grimmsnarl 0% vs Other. -/
theorem popularity_paradox_robust_worst_case :
    adjustedWR dragapultTop14WR 1 = 629243 / 1000000 ∧
    adjustedWR grimmsnarlTop14WR 0 = 366061 / 1000000 ∧
    adjustedWR dragapultTop14WR 1 - adjustedWR grimmsnarlTop14WR 0 = 131591 / 500000 := by
  constructor
  · decide
  constructor
  · decide
  · decide

/-- 80/20 stress test (highly favorable to Dragapult in `Other`). -/
theorem popularity_paradox_survives_80pct :
    adjustedWR dragapultTop14WR (4 / 5) = 568243 / 1000000 ∧
    adjustedWR grimmsnarlTop14WR (1 / 5) = 427061 / 1000000 ∧
    adjustedWR dragapultTop14WR (4 / 5) > adjustedWR grimmsnarlTop14WR (1 / 5) := by
  constructor
  · decide
  constructor
  · decide
  · decide

/-- Dragapult needs 175757/305000 (~57.625%) vs `Other` to hit 50% overall. -/
theorem dragapult_below_50_robust :
    adjustedWR dragapultTop14WR dragapultToFiftyOtherWR = 1 / 2 ∧
    dragapultToFiftyOtherWR > 1 / 2 := by
  constructor
  · decide
  · decide

/-- Grimmsnarl stays above 50% unless its WR vs `Other` drops below 133939/305000 (~43.914%). -/
theorem grimmsnarl_above_50_robust :
    adjustedWR grimmsnarlTop14WR grimmsnarlToFiftyOtherWR = 1 / 2 ∧
    grimmsnarlToFiftyOtherWR < 1 / 2 := by
  constructor
  · decide
  · decide

/-- Exact reversal points:
    - if Grimmsnarl is 0% vs Other, Dragapult must be 41818/305000 (~13.711%);
    - if Dragapult is 100% vs Other, Grimmsnarl must be 263182/305000 (~86.289%). -/
theorem paradox_reversal_bound :
    adjustedWR dragapultTop14WR paradoxReversalDelta = adjustedWR grimmsnarlTop14WR 0 ∧
    adjustedWR dragapultTop14WR 1 = adjustedWR grimmsnarlTop14WR (263182 / 305000) := by
  constructor
  · decide
  · decide

end PokemonLean.Robustness
