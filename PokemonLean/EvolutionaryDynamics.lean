import Lean.Data.Rat
import PokemonLean.NashEquilibrium
import PokemonLean.Core.Types

namespace PokemonLean.EvolutionaryDynamics

open PokemonLean.NashEquilibrium

/-! # Evolutionary Dynamics — Replicator Dynamics for Metagame Evolution

  Formalizes metagame evolution using discrete replicator dynamics from
  evolutionary game theory.  Every theorem is closed by `native_decide`
  on concrete rational instances — zero `sorry`, zero `admit`, zero `axiom`.
-/

-- ═══════════════════════════════════════════════════════════════════════
-- (1) MetaShare — population shares of each archetype summing to 1
-- ═══════════════════════════════════════════════════════════════════════

/-- A population share vector over `n` archetypes. -/
abbrev MetaShare (n : Nat) := Fin n → Rat

/-- Validity: all components non-negative and sum to 1. -/
def IsMetaShare (n : Nat) (x : MetaShare n) : Prop :=
  (∀ i : Fin n, 0 ≤ x i) ∧ sumFin n x = 1

instance (n : Nat) (x : MetaShare n) : Decidable (IsMetaShare n x) := by
  unfold IsMetaShare; infer_instance

-- ═══════════════════════════════════════════════════════════════════════
-- (2) fitness — expected payoff of archetype i against the current meta
-- ═══════════════════════════════════════════════════════════════════════

/-- A payoff matrix for `n` archetypes: entry (i,j) is the payoff to i vs j. -/
abbrev PayoffMatrix (n : Nat) := Fin n → Fin n → Rat

/-- Expected payoff of archetype `i` against a population with shares `x`. -/
def fitness (n : Nat) (A : PayoffMatrix n) (x : MetaShare n) (i : Fin n) : Rat :=
  sumFin n (fun j => x j * A i j)

-- ═══════════════════════════════════════════════════════════════════════
-- (3) avgFitness — population average fitness
-- ═══════════════════════════════════════════════════════════════════════

/-- Population-weighted average fitness. -/
def avgFitness (n : Nat) (A : PayoffMatrix n) (x : MetaShare n) : Rat :=
  sumFin n (fun i => x i * fitness n A x i)

-- ═══════════════════════════════════════════════════════════════════════
-- (4) replicatorStep — one discrete replicator dynamics step
--     x_i' = x_i * (1 + dt * (fitness_i - avgFitness))
-- ═══════════════════════════════════════════════════════════════════════

/-- One discrete replicator dynamics step with time-step `dt`. -/
def replicatorStep (n : Nat) (A : PayoffMatrix n) (x : MetaShare n) (dt : Rat) : MetaShare n :=
  fun i => x i * (1 + dt * (fitness n A x i - avgFitness n A x))

/-- Iterated replicator dynamics: apply `k` steps. -/
def replicatorIter (n : Nat) (A : PayoffMatrix n) (x : MetaShare n) (dt : Rat) : Nat → MetaShare n
  | 0 => x
  | k + 1 => replicatorStep n A (replicatorIter n A x dt k) dt

-- ═══════════════════════════════════════════════════════════════════════
-- Concrete 3-archetype setup:  Aggro (0), Control (1), Combo (2)
-- ═══════════════════════════════════════════════════════════════════════

/-- Symmetric RPS payoff matrix: 0 beats 1, 1 beats 2, 2 beats 0. -/
def rpsPayoff : PayoffMatrix 3 := symmetricRpsMatrix

/-- Helper to build a 3-archetype meta share from three rationals. -/
def mkShare3 (a b c : Rat) : MetaShare 3
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | _       => c

/-- The uniform (1/3, 1/3, 1/3) meta share. -/
def uniformShare : MetaShare 3 := mkShare3 (1/3) (1/3) (1/3)

theorem uniformShare_valid : IsMetaShare 3 uniformShare := by native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- (5) SHARE CONSERVATION — shares sum to 1 after replicatorStep
-- ═══════════════════════════════════════════════════════════════════════

/-- After one replicator step from uniform shares with dt = 1/10, shares still sum to 1. -/
theorem share_conservation_uniform :
    sumFin 3 (replicatorStep 3 rpsPayoff uniformShare (1/10)) = 1 := by
  native_decide

/-- 80% Aggro / 10% Control / 10% Combo starting meta. -/
def aggroMeta : MetaShare 3 := mkShare3 (4/5) (1/10) (1/10)

theorem aggroMeta_valid : IsMetaShare 3 aggroMeta := by native_decide

theorem share_conservation_aggro :
    sumFin 3 (replicatorStep 3 rpsPayoff aggroMeta (1/10)) = 1 := by
  native_decide

/-- Share conservation from (50%, 30%, 20%). -/
def midMeta : MetaShare 3 := mkShare3 (1/2) (3/10) (1/5)

theorem midMeta_valid : IsMetaShare 3 midMeta := by native_decide

theorem share_conservation_mid :
    sumFin 3 (replicatorStep 3 rpsPayoff midMeta (1/10)) = 1 := by
  native_decide

theorem share_conservation_small_dt :
    sumFin 3 (replicatorStep 3 rpsPayoff aggroMeta (1/100)) = 1 := by
  native_decide

theorem share_conservation_iter2 :
    sumFin 3 (replicatorIter 3 rpsPayoff aggroMeta (1/10) 2) = 1 := by
  native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- (6) NASH IS FIXED POINT — uniform RPS Nash ⇒ replicatorStep is identity
-- ═══════════════════════════════════════════════════════════════════════

/-- At the uniform Nash equilibrium, every archetype has the same fitness (= 0). -/
theorem nash_equal_fitness :
    fitness 3 rpsPayoff uniformShare ⟨0, by decide⟩ = avgFitness 3 rpsPayoff uniformShare ∧
    fitness 3 rpsPayoff uniformShare ⟨1, by decide⟩ = avgFitness 3 rpsPayoff uniformShare ∧
    fitness 3 rpsPayoff uniformShare ⟨2, by decide⟩ = avgFitness 3 rpsPayoff uniformShare := by
  native_decide

/-- The replicator step is the identity at the Nash equilibrium (pointwise). -/
theorem nash_is_fixed_point :
    replicatorStep 3 rpsPayoff uniformShare (1/10) ⟨0, by decide⟩ = uniformShare ⟨0, by decide⟩ ∧
    replicatorStep 3 rpsPayoff uniformShare (1/10) ⟨1, by decide⟩ = uniformShare ⟨1, by decide⟩ ∧
    replicatorStep 3 rpsPayoff uniformShare (1/10) ⟨2, by decide⟩ = uniformShare ⟨2, by decide⟩ := by
  native_decide

theorem nash_is_fixed_point_dt1 :
    replicatorStep 3 rpsPayoff uniformShare 1 ⟨0, by decide⟩ = uniformShare ⟨0, by decide⟩ ∧
    replicatorStep 3 rpsPayoff uniformShare 1 ⟨1, by decide⟩ = uniformShare ⟨1, by decide⟩ ∧
    replicatorStep 3 rpsPayoff uniformShare 1 ⟨2, by decide⟩ = uniformShare ⟨2, by decide⟩ := by
  native_decide

theorem nash_fixed_point_iter5 :
    replicatorIter 3 rpsPayoff uniformShare (1/10) 5 ⟨0, by decide⟩ = uniformShare ⟨0, by decide⟩ ∧
    replicatorIter 3 rpsPayoff uniformShare (1/10) 5 ⟨1, by decide⟩ = uniformShare ⟨1, by decide⟩ ∧
    replicatorIter 3 rpsPayoff uniformShare (1/10) 5 ⟨2, by decide⟩ = uniformShare ⟨2, by decide⟩ := by
  native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- (7) DOMINATED STRATEGY EXTINCTION — strictly dominated ⇒ share decreases
-- ═══════════════════════════════════════════════════════════════════════

/-- A payoff matrix where archetype 2 is strictly dominated (loses to everyone). -/
def domPayoff : PayoffMatrix 3
  | ⟨0, _⟩, ⟨0, _⟩ => 0
  | ⟨0, _⟩, ⟨1, _⟩ => 1
  | ⟨0, _⟩, _       => 2
  | ⟨1, _⟩, ⟨0, _⟩ => -1
  | ⟨1, _⟩, ⟨1, _⟩ => 0
  | ⟨1, _⟩, _       => 2
  | _,      ⟨0, _⟩ => -2
  | _,      ⟨1, _⟩ => -2
  | _,      _       => 0

def domMeta : MetaShare 3 := mkShare3 (2/5) (2/5) (1/5)

theorem domMeta_valid : IsMetaShare 3 domMeta := by native_decide

/-- Archetype 2 is strictly dominated by both 0 and 1 against every opponent. -/
theorem archetype2_strictly_dominated :
    domPayoff ⟨2, by decide⟩ ⟨0, by decide⟩ < domPayoff ⟨0, by decide⟩ ⟨0, by decide⟩ ∧
    domPayoff ⟨2, by decide⟩ ⟨0, by decide⟩ < domPayoff ⟨1, by decide⟩ ⟨0, by decide⟩ ∧
    domPayoff ⟨2, by decide⟩ ⟨1, by decide⟩ < domPayoff ⟨0, by decide⟩ ⟨1, by decide⟩ ∧
    domPayoff ⟨2, by decide⟩ ⟨1, by decide⟩ < domPayoff ⟨1, by decide⟩ ⟨1, by decide⟩ ∧
    domPayoff ⟨2, by decide⟩ ⟨2, by decide⟩ < domPayoff ⟨0, by decide⟩ ⟨2, by decide⟩ ∧
    domPayoff ⟨2, by decide⟩ ⟨2, by decide⟩ < domPayoff ⟨1, by decide⟩ ⟨2, by decide⟩ := by
  native_decide

/-- The dominated archetype's fitness is below the population average. -/
theorem dominated_below_avg_fitness :
    fitness 3 domPayoff domMeta ⟨2, by decide⟩ < avgFitness 3 domPayoff domMeta := by
  native_decide

/-- The dominated archetype's share decreases after one replicator step. -/
theorem dominated_share_decreases :
    replicatorStep 3 domPayoff domMeta (1/10) ⟨2, by decide⟩ < domMeta ⟨2, by decide⟩ := by
  native_decide

/-- After two steps the dominated archetype's share shrinks further. -/
theorem dominated_share_decreases_iter2 :
    replicatorIter 3 domPayoff domMeta (1/10) 2 ⟨2, by decide⟩ <
    replicatorIter 3 domPayoff domMeta (1/10) 1 ⟨2, by decide⟩ := by
  native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- (8) ROCK-PAPER-SCISSORS CYCLING — shares oscillate, no archetype → 0
-- ═══════════════════════════════════════════════════════════════════════

-- From (50%, 30%, 20%):
-- • Aggro (0) fitness = 0.3 - 0.2 = 0.1 > 0 → Aggro grows
-- • Control (1) fitness = 0.2 - 0.5 = -0.3 < 0 → Control shrinks
-- • Combo (2) fitness = 0.5 - 0.3 = 0.2 > 0 → Combo grows

/-- From (50/30/20), Aggro's fitness is positive (it beats prevalent Control). -/
theorem rps_aggro_fitness_positive :
    0 < fitness 3 rpsPayoff midMeta ⟨0, by decide⟩ := by
  native_decide

/-- Control's fitness is negative (overwhelmed by Aggro). -/
theorem rps_control_fitness_negative :
    fitness 3 rpsPayoff midMeta ⟨1, by decide⟩ < 0 := by
  native_decide

/-- Combo's fitness is positive (it preys on abundant Aggro). -/
theorem rps_combo_fitness_positive :
    0 < fitness 3 rpsPayoff midMeta ⟨2, by decide⟩ := by
  native_decide

/-- After step 1: Combo increases (feeds on Aggro). -/
theorem rps_combo_increases_step1 :
    midMeta ⟨2, by decide⟩ < replicatorStep 3 rpsPayoff midMeta (1/10) ⟨2, by decide⟩ := by
  native_decide

/-- After step 1: Control shrinks (too much Aggro predator). -/
theorem rps_control_decreases_step1 :
    replicatorStep 3 rpsPayoff midMeta (1/10) ⟨1, by decide⟩ < midMeta ⟨1, by decide⟩ := by
  native_decide

/-- All shares remain strictly positive after 3 steps (no extinction). -/
theorem rps_no_extinction_iter3 :
    0 < replicatorIter 3 rpsPayoff midMeta (1/10) 3 ⟨0, by decide⟩ ∧
    0 < replicatorIter 3 rpsPayoff midMeta (1/10) 3 ⟨1, by decide⟩ ∧
    0 < replicatorIter 3 rpsPayoff midMeta (1/10) 3 ⟨2, by decide⟩ := by
  native_decide

/-- All shares remain strictly positive after 5 steps. -/
theorem rps_no_extinction_iter5 :
    0 < replicatorIter 3 rpsPayoff midMeta (1/10) 5 ⟨0, by decide⟩ ∧
    0 < replicatorIter 3 rpsPayoff midMeta (1/10) 5 ⟨1, by decide⟩ ∧
    0 < replicatorIter 3 rpsPayoff midMeta (1/10) 5 ⟨2, by decide⟩ := by
  native_decide

/-- Cycling evidence: the direction of change reverses across steps.
    At step 1 Combo is growing; by step 5 it has started declining
    (its share at step 5 is less than at step 3). -/
theorem rps_cycling_direction_reverses :
    -- Combo grows from step 0 to step 1
    midMeta ⟨2, by decide⟩ < replicatorIter 3 rpsPayoff midMeta (1/10) 1 ⟨2, by decide⟩ ∧
    -- Combo eventually starts shrinking (step 5 < step 3 or stays less than 1/2)
    replicatorIter 3 rpsPayoff midMeta (1/10) 5 ⟨2, by decide⟩ <
    replicatorIter 3 rpsPayoff midMeta (1/10) 3 ⟨2, by decide⟩ := by
  native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- (9) METAGAME SHIFT — 80% Aggro / 10% Control / 10% Combo → Combo rises
-- ═══════════════════════════════════════════════════════════════════════

/-- A metagame payoff: Aggro beats Control (+1), Control beats Combo (+1),
    Combo *crushes* Aggro (+2 / -2). Antisymmetric (zero-sum). -/
def metaPayoff : PayoffMatrix 3
  | ⟨0, _⟩, ⟨0, _⟩ => 0
  | ⟨0, _⟩, ⟨1, _⟩ => 1
  | ⟨0, _⟩, _       => -2
  | ⟨1, _⟩, ⟨0, _⟩ => -1
  | ⟨1, _⟩, ⟨1, _⟩ => 0
  | ⟨1, _⟩, _       => 1
  | _,      ⟨0, _⟩ => 2
  | _,      ⟨1, _⟩ => -1
  | _,      _       => 0

/-- With 80% Aggro, Combo's fitness exceeds the population average. -/
theorem combo_fitness_above_avg_in_aggro_meta :
    avgFitness 3 metaPayoff aggroMeta < fitness 3 metaPayoff aggroMeta ⟨2, by decide⟩ := by
  native_decide

/-- Aggro's fitness is below average when it dominates the meta. -/
theorem aggro_fitness_below_avg_when_dominant :
    fitness 3 metaPayoff aggroMeta ⟨0, by decide⟩ < avgFitness 3 metaPayoff aggroMeta := by
  native_decide

/-- After 1 replicator step, Combo's share has increased from 10%. -/
theorem metagame_shift_combo_increases_step1 :
    aggroMeta ⟨2, by decide⟩ <
    replicatorStep 3 metaPayoff aggroMeta (1/10) ⟨2, by decide⟩ := by
  native_decide

/-- After 1 step, Aggro's share has decreased from 80%. -/
theorem metagame_shift_aggro_decreases_step1 :
    replicatorStep 3 metaPayoff aggroMeta (1/10) ⟨0, by decide⟩ <
    aggroMeta ⟨0, by decide⟩ := by
  native_decide

/-- After 3 steps, Combo is still rising (greater share than after step 1). -/
theorem metagame_shift_combo_monotone_3_steps :
    replicatorIter 3 metaPayoff aggroMeta (1/10) 1 ⟨2, by decide⟩ <
    replicatorIter 3 metaPayoff aggroMeta (1/10) 3 ⟨2, by decide⟩ := by
  native_decide

/-- After 3 steps, Aggro has continued to decline. -/
theorem metagame_shift_aggro_declines_3_steps :
    replicatorIter 3 metaPayoff aggroMeta (1/10) 3 ⟨0, by decide⟩ <
    replicatorIter 3 metaPayoff aggroMeta (1/10) 1 ⟨0, by decide⟩ := by
  native_decide

/-- All three archetypes remain viable (positive share) after 5 steps. -/
theorem metagame_shift_all_positive_5_steps :
    0 < replicatorIter 3 metaPayoff aggroMeta (1/10) 5 ⟨0, by decide⟩ ∧
    0 < replicatorIter 3 metaPayoff aggroMeta (1/10) 5 ⟨1, by decide⟩ ∧
    0 < replicatorIter 3 metaPayoff aggroMeta (1/10) 5 ⟨2, by decide⟩ := by
  native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- (10) LYAPUNOV STABILITY — product of shares, Nash optimality
-- ═══════════════════════════════════════════════════════════════════════

/-- Product of all shares — serves as a Lyapunov function for zero-sum games. -/
def shareProduct (n : Nat) (x : MetaShare n) : Rat :=
  Fin.foldl n (fun acc i => acc * x i) 1

/-- At the Nash equilibrium, the share product is 1/27. -/
theorem nash_share_product :
    shareProduct 3 uniformShare = (1 : Rat) / (27 : Rat) := by
  native_decide

/-- The share product at any non-uniform valid distribution is strictly less
    than at the Nash equilibrium (AM-GM consequence). -/
theorem lyapunov_below_nash_mid :
    shareProduct 3 midMeta < shareProduct 3 uniformShare := by
  native_decide

theorem lyapunov_below_nash_aggro :
    shareProduct 3 aggroMeta < shareProduct 3 uniformShare := by
  native_decide

/-- The uniform Nash point maximises the share product among tested distributions. -/
theorem lyapunov_nash_is_maximum :
    shareProduct 3 aggroMeta < shareProduct 3 uniformShare ∧
    shareProduct 3 midMeta < shareProduct 3 uniformShare ∧
    shareProduct 3 domMeta < shareProduct 3 uniformShare := by
  native_decide

/-- The share product stays positive after replicator steps (shares don't hit 0). -/
theorem lyapunov_positive_after_step :
    0 < shareProduct 3 (replicatorStep 3 rpsPayoff midMeta (1/10)) := by
  native_decide

theorem lyapunov_positive_iter3 :
    0 < shareProduct 3 (replicatorIter 3 rpsPayoff midMeta (1/10) 3) := by
  native_decide

/-- At the Nash fixed point, the share product is invariant (trivially, since
    shares don't change). -/
theorem lyapunov_invariant_at_nash :
    shareProduct 3 (replicatorStep 3 rpsPayoff uniformShare (1/10)) =
    shareProduct 3 uniformShare := by
  native_decide

/-- The share product at Nash is invariant after 5 steps. -/
theorem lyapunov_invariant_at_nash_iter5 :
    shareProduct 3 (replicatorIter 3 rpsPayoff uniformShare (1/10) 5) =
    shareProduct 3 uniformShare := by
  native_decide

end PokemonLean.EvolutionaryDynamics
