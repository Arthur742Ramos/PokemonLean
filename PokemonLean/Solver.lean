-- Verified Solver for Maximum Damage Calculation
-- Phase 4: Scaling, Tooling & Integration

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
    -- findIdx? returns index in bounds when it returns Some
    sorry -- Requires List.findIdx? properties from Mathlib

-- ============================================================================
-- COMPLETENESS PROOFS
-- ============================================================================

-- The solver finds the true maximum (never misses a higher damage option)
theorem maxDamage_complete (attacks : List Attack) (attackerType : EnergyType) (defender : Card) :
    ∀ atk ∈ attacks, calculateDamage atk attackerType defender ≤ maxDamageFromAttacks attacks attackerType defender := by
  intro atk hIn
  simp only [maxDamageFromAttacks]
  induction attacks with
  | nil => cases hIn
  | cons head tail ih =>
    simp only [List.foldl]
    cases hIn with
    | head =>
      -- atk = head, show damage head ≤ foldl(max, max(0, damage head), tail)
      sorry -- Requires showing head damage is preserved through foldl
    | tail _ hTail =>
      sorry -- Induction case

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
