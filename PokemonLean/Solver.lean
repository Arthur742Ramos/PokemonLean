-- Verified Solver for Maximum Damage Calculation
-- Phase 4: Scaling, Tooling & Integration

import Init.Data.List.Find
import PokemonLean.Basic

namespace PokemonLean.Solver

open PokemonLean

-- ============================================================================
-- MAXIMUM DAMAGE SOLVER
-- ============================================================================

-- Find the maximum damage from a list of attacks against a defender
def maxDamageFromAttacks (attacks : List Attack) (attackerType : EnergyType) (defender : Card) : Nat :=
  attacks.foldl (fun acc atk => max acc (calculateDamage atk attackerType defender)) 0

-- Find the best attack index (0-indexed) that deals maximum damage
def bestAttackIndex (attacks : List Attack) (attackerType : EnergyType) (defender : Card) : Option Nat :=
  match attacks with
  | [] => none
  | _ =>
    let damages := attacks.map (fun atk => calculateDamage atk attackerType defender)
    let maxDmg := damages.foldl max 0
    damages.findIdx? (· == maxDmg)

-- ============================================================================
-- SOUNDNESS PROOFS
-- ============================================================================

-- The solver only returns legal attack indices
theorem bestAttackIndex_sound (attacks : List Attack) (attackerType : EnergyType) (defender : Card) :
    ∀ idx, bestAttackIndex attacks attackerType defender = some idx →
    idx < attacks.length := by
  intro idx hIdx
  simp only [bestAttackIndex] at hIdx
  cases attacks with
  | nil => simp at hIdx
  | cons a as =>
    simp only at hIdx
    have hLen : idx < ((a :: as).map (fun atk => calculateDamage atk attackerType defender)).length :=
      (List.findIdx?_eq_some_iff_findIdx_eq.mp hIdx).1
    simpa using hLen

-- ============================================================================
-- COMPLETENESS PROOFS
-- ============================================================================

private theorem foldl_max_ge (attacks : List Attack) (attackerType : EnergyType) (defender : Card) (acc : Nat) :
    acc ≤ attacks.foldl (fun acc atk => max acc (calculateDamage atk attackerType defender)) acc := by
  induction attacks generalizing acc with
  | nil => simp
  | cons head tail ih =>
    simp [List.foldl]
    exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem maxDamage_complete_acc (attacks : List Attack) (attackerType : EnergyType) (defender : Card) (acc : Nat) :
    ∀ atk ∈ attacks,
      calculateDamage atk attackerType defender ≤
        attacks.foldl (fun acc atk => max acc (calculateDamage atk attackerType defender)) acc := by
  intro atk hIn
  induction attacks generalizing acc with
  | nil => cases hIn
  | cons attackHead tail ih =>
    cases hIn with
    | head =>
      simp [List.foldl]
      have hBase : calculateDamage atk attackerType defender ≤
          max acc (calculateDamage atk attackerType defender) := by
        simpa using (Nat.le_max_right acc (calculateDamage atk attackerType defender))
      have hAcc :
          max acc (calculateDamage atk attackerType defender) ≤
            tail.foldl (fun acc atk => max acc (calculateDamage atk attackerType defender))
              (max acc (calculateDamage atk attackerType defender)) := by
        exact foldl_max_ge tail attackerType defender (max acc (calculateDamage atk attackerType defender))
      exact Nat.le_trans hBase hAcc
    | tail _ hTail =>
      simpa [List.foldl] using
        (ih (acc := max acc (calculateDamage attackHead attackerType defender)) hTail)

-- The solver finds the true maximum (never misses a higher damage option)
theorem maxDamage_complete (attacks : List Attack) (attackerType : EnergyType) (defender : Card) :
    ∀ atk ∈ attacks, calculateDamage atk attackerType defender ≤ maxDamageFromAttacks attacks attackerType defender := by
  intro atk hIn
  simpa [maxDamageFromAttacks] using
    (maxDamage_complete_acc attacks attackerType defender 0 atk hIn)

-- ============================================================================
-- DAMAGE RANGE ANALYSIS
-- ============================================================================

-- Minimum possible damage from an attack (considering resistance)
def minPossibleDamage (attack : Attack) : Nat :=
  if attack.baseDamage > 30 then attack.baseDamage - 30 else 0

-- Maximum possible damage from an attack (considering weakness)
def maxPossibleDamage (attack : Attack) : Nat :=
  (attack.baseDamage + damageBonus attack.effects) * 2

-- ============================================================================
-- SOLVER INTERFACE
-- ============================================================================

-- Result of the solver
structure SolverResult where
  attackIndex : Nat
  expectedDamage : Nat
  isLethal : Bool
  deriving Repr

-- Compute if an attack would knock out the defender
def isKnockout (damage : Nat) (defenderHP : Nat) (currentDamage : Nat) : Bool :=
  damage + currentDamage >= defenderHP

-- Main solver function
def solve (attacker : Card) (defender : PokemonInPlay) : Option SolverResult :=
  match bestAttackIndex attacker.attacks attacker.energyType defender.card with
  | none => none
  | some idx =>
    match listGet? attacker.attacks idx with
    | none => none
    | some attack =>
      let damage := calculateDamage attack attacker.energyType defender.card
      some {
        attackIndex := idx
        expectedDamage := damage
        isLethal := isKnockout damage defender.card.hp defender.damage
      }

-- ============================================================================
-- EXAMPLE USAGE
-- ============================================================================

#eval solve sampleCharmander { card := samplePikachu, damage := 40, status := none }
-- Should return: attackIndex 0, expectedDamage 30, isLethal true (60 - 40 = 20 remaining, 30 >= 20)

#eval solve sampleSquirtle { card := sampleCharmander, damage := 0, status := none }
-- Should return: attackIndex 0, expectedDamage 40 (weakness), isLethal false

end PokemonLean.Solver
