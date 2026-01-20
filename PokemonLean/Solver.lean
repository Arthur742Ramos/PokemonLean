-- Verified Solver for Maximum Damage Calculation
-- Phase 4: Scaling, Tooling & Integration

import Init.Data.List.Find
import PokemonLean.Basic
import PokemonLean.Cards

namespace PokemonLean.Solver

open PokemonLean

-- ============================================================================
-- MAXIMUM DAMAGE SOLVER
-- ============================================================================

-- Find the maximum damage from a list of attacks against a defender
def maxDamageFromAttacks (attacks : List Attack) (attackerType : EnergyType) (defender : Card) : Nat :=
  attacks.foldl (fun acc atk => max acc (calculateDamage atk attackerType defender)) 0

-- Damage from an attack with the current attacker and defender
def attackDamage (attacker : PokemonInPlay) (defender : PokemonInPlay) (attack : Attack) : Nat :=
  calculateDamage attack attacker.card.energyType defender.card

-- Attack legality is driven by energy costs for now
def legalAttack (attacker : PokemonInPlay) (attack : Attack) : Prop :=
  hasEnergyCost attack attacker.energy = true

def legalAttackIndex (attacker : PokemonInPlay) (attacks : List Attack) (idx : Nat) : Prop :=
  ∃ attack, listGet? attacks idx = some attack ∧ legalAttack attacker attack

-- Find the best legal attack (index + attack)
def bestAttackFrom (attacker : PokemonInPlay) (defender : PokemonInPlay) : List Attack → Option (Nat × Attack)
  | [] => none
  | attack :: rest =>
      let current : Option (Nat × Attack) :=
        if hasEnergyCost attack attacker.energy then some (0, attack) else none
      let tail := (bestAttackFrom attacker defender rest).map (fun (idx, atk) => (idx + 1, atk))
      match current, tail with
      | none, none => none
      | some c, none => some c
      | none, some b => some b
      | some c, some b =>
          if attackDamage attacker defender c.2 >= attackDamage attacker defender b.2 then some c else some b

def bestAttack (attacker : PokemonInPlay) (defender : PokemonInPlay) : Option (Nat × Attack) :=
  bestAttackFrom attacker defender attacker.card.attacks

-- ============================================================================
-- SOUNDNESS PROOFS
-- ============================================================================

theorem listGet?_lt_length {α : Type} :
    ∀ {xs : List α} {idx : Nat} {x : α}, listGet? xs idx = some x → idx < xs.length := by
  intro xs idx x h
  induction xs generalizing idx with
  | nil =>
    cases idx <;> simp [listGet?] at h
  | cons head tail ih =>
    cases idx with
    | zero =>
      simp [listGet?] at h
      simp [List.length]
    | succ idx =>
      simp [listGet?] at h
      have h' := ih h
      simpa [List.length] using Nat.succ_lt_succ h'

theorem bestAttackFrom_sound (attacker : PokemonInPlay) (defender : PokemonInPlay) :
    ∀ attacks idx attack,
      bestAttackFrom attacker defender attacks = some (idx, attack) →
      listGet? attacks idx = some attack ∧ hasEnergyCost attack attacker.energy = true := by
  intro attacks idx attack hChoice
  induction attacks generalizing idx attack with
  | nil =>
    simp [bestAttackFrom] at hChoice
  | cons head tail ih =>
    by_cases hCost : hasEnergyCost head attacker.energy
    · cases hTail : bestAttackFrom attacker defender tail with
      | none =>
        simp [bestAttackFrom, hCost, hTail] at hChoice
        rcases hChoice with ⟨rfl, rfl⟩
        simp [listGet?, hCost]
      | some tailChoice =>
        by_cases hCmp :
          attackDamage attacker defender head >=
            attackDamage attacker defender tailChoice.2
        · simp [bestAttackFrom, hCost, hTail, hCmp] at hChoice
          rcases hChoice with ⟨rfl, rfl⟩
          simp [listGet?, hCost]
        · simp [bestAttackFrom, hCost, hTail, hCmp] at hChoice
          rcases hChoice with ⟨rfl, rfl⟩
          have hSound := ih _ _ hTail
          rcases hSound with ⟨hGet, hLegal⟩
          exact ⟨by simpa [listGet?] using hGet, hLegal⟩
    · cases hTail : bestAttackFrom attacker defender tail with
      | none =>
        simp [bestAttackFrom, hCost, hTail] at hChoice
      | some tailChoice =>
        simp [bestAttackFrom, hCost, hTail] at hChoice
        rcases hChoice with ⟨rfl, rfl⟩
        have hSound := ih _ _ hTail
        rcases hSound with ⟨hGet, hLegal⟩
        exact ⟨by simpa [listGet?] using hGet, hLegal⟩

theorem bestAttack_sound (attacker : PokemonInPlay) (defender : PokemonInPlay) :
    ∀ idx attack,
      bestAttack attacker defender = some (idx, attack) →
      idx < attacker.card.attacks.length ∧ hasEnergyCost attack attacker.energy = true := by
  intro idx attack hChoice
  have hSound :=
    bestAttackFrom_sound attacker defender attacker.card.attacks idx attack (by
      simpa [bestAttack] using hChoice)
  exact ⟨listGet?_lt_length hSound.1, hSound.2⟩

-- ============================================================================
-- OPTIMALITY PROOFS
-- ============================================================================

theorem bestAttackFrom_none_no_legal (attacker : PokemonInPlay) (defender : PokemonInPlay) :
    ∀ attacks idx attack,
      bestAttackFrom attacker defender attacks = none →
      listGet? attacks idx = some attack →
      hasEnergyCost attack attacker.energy = true →
      False := by
  intro attacks idx attack hNone hGet hLegal
  induction attacks generalizing idx attack with
  | nil =>
    simp [listGet?] at hGet
  | cons head tail ih =>
    by_cases hCost : hasEnergyCost head attacker.energy
    · cases hTail : bestAttackFrom attacker defender tail with
      | none =>
        simp [bestAttackFrom, hCost, hTail] at hNone
      | some tailChoice =>
        by_cases hCmp :
          attackDamage attacker defender head >=
            attackDamage attacker defender tailChoice.2
        · simp [bestAttackFrom, hCost, hTail, hCmp] at hNone
        · simp [bestAttackFrom, hCost, hTail, hCmp] at hNone
    · cases hTail : bestAttackFrom attacker defender tail with
      | none =>
        cases idx with
        | zero =>
          simp [listGet?] at hGet
          cases hGet
          simp [hCost] at hLegal
        | succ idx =>
          have hGetTail : listGet? tail idx = some attack := by
            simpa [listGet?] using hGet
          exact ih _ _ hTail hGetTail hLegal
      | some tailChoice =>
        simp [bestAttackFrom, hCost, hTail] at hNone

theorem bestAttackFrom_optimal (attacker : PokemonInPlay) (defender : PokemonInPlay) :
    ∀ attacks idx attack,
      bestAttackFrom attacker defender attacks = some (idx, attack) →
      ∀ j attack',
        listGet? attacks j = some attack' →
        hasEnergyCost attack' attacker.energy = true →
        attackDamage attacker defender attack' ≤ attackDamage attacker defender attack := by
  intro attacks idx attack hChoice
  induction attacks generalizing idx attack with
  | nil =>
    simp [bestAttackFrom] at hChoice
  | cons head tail ih =>
    intro j attack' hGet hLegal
    by_cases hCost : hasEnergyCost head attacker.energy
    · cases hTail : bestAttackFrom attacker defender tail with
      | none =>
        simp [bestAttackFrom, hCost, hTail] at hChoice
        rcases hChoice with ⟨rfl, rfl⟩
        cases j with
        | zero =>
          simp [listGet?] at hGet
          cases hGet
          exact Nat.le_refl _
        | succ j =>
          have hGetTail : listGet? tail j = some attack' := by
            simpa [listGet?] using hGet
          cases (bestAttackFrom_none_no_legal attacker defender tail j attack' hTail hGetTail hLegal)
      | some tailChoice =>
        by_cases hCmp :
          attackDamage attacker defender head >=
            attackDamage attacker defender tailChoice.2
        · simp [bestAttackFrom, hCost, hTail, hCmp] at hChoice
          rcases hChoice with ⟨rfl, rfl⟩
          cases j with
          | zero =>
            simp [listGet?] at hGet
            cases hGet
            exact Nat.le_refl _
          | succ j =>
            have hGetTail : listGet? tail j = some attack' := by
              simpa [listGet?] using hGet
            have hOptimal :=
              ih (idx := tailChoice.1) (attack := tailChoice.2) hTail j attack' hGetTail hLegal
            exact Nat.le_trans hOptimal (by simpa using hCmp)
        · simp [bestAttackFrom, hCost, hTail, hCmp] at hChoice
          rcases hChoice with ⟨rfl, rfl⟩
          cases j with
          | zero =>
            simp [listGet?] at hGet
            cases hGet
            exact Nat.le_of_lt (Nat.lt_of_not_ge hCmp)
          | succ j =>
            have hGetTail : listGet? tail j = some attack' := by
              simpa [listGet?] using hGet
            have hOptimal :=
              ih (idx := tailChoice.1) (attack := tailChoice.2) hTail j attack' hGetTail hLegal
            simpa using hOptimal
    · cases hTail : bestAttackFrom attacker defender tail with
      | none =>
        simp [bestAttackFrom, hCost, hTail] at hChoice
      | some tailChoice =>
        simp [bestAttackFrom, hCost, hTail] at hChoice
        rcases hChoice with ⟨rfl, rfl⟩
        cases j with
        | zero =>
          simp [listGet?] at hGet
          cases hGet
          simp [hCost] at hLegal
        | succ j =>
          have hGetTail : listGet? tail j = some attack' := by
            simpa [listGet?] using hGet
          have hOptimal :=
            ih (idx := tailChoice.1) (attack := tailChoice.2) hTail j attack' hGetTail hLegal
          simpa using hOptimal

theorem bestAttack_optimal (attacker : PokemonInPlay) (defender : PokemonInPlay) :
    ∀ idx attack,
      bestAttack attacker defender = some (idx, attack) →
      ∀ j attack',
        listGet? attacker.card.attacks j = some attack' →
        hasEnergyCost attack' attacker.energy = true →
        attackDamage attacker defender attack' ≤ attackDamage attacker defender attack := by
  intro idx attack hChoice j attack' hGet hLegal
  have hChoice' :
      bestAttackFrom attacker defender attacker.card.attacks = some (idx, attack) := by
    simpa [bestAttack] using hChoice
  exact bestAttackFrom_optimal attacker defender _ _ _ hChoice' _ _ hGet hLegal

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
  (attack.baseDamage + attackBonus attack.effects) * 2

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
def solve (attacker : PokemonInPlay) (defender : PokemonInPlay) : Option SolverResult :=
  match bestAttack attacker defender with
  | none => none
  | some (idx, attack) =>
    let damage := attackDamage attacker defender attack
    some {
      attackIndex := idx
      expectedDamage := damage
      isLethal := isKnockout damage defender.card.hp defender.damage
    }

theorem solve_sound (attacker : PokemonInPlay) (defender : PokemonInPlay) :
    ∀ result, solve attacker defender = some result →
      result.attackIndex < attacker.card.attacks.length ∧
        ∃ attack,
          listGet? attacker.card.attacks result.attackIndex = some attack ∧
            hasEnergyCost attack attacker.energy = true ∧
            result.expectedDamage = attackDamage attacker defender attack := by
  intro result hSolve
  cases hBest : bestAttack attacker defender with
  | none =>
    simp [solve, hBest] at hSolve
  | some choice =>
    cases choice with
    | mk idx attack =>
      simp [solve, hBest] at hSolve
      cases hSolve
      have hSound := bestAttack_sound attacker defender idx attack hBest
      have hGet :=
        (bestAttackFrom_sound attacker defender attacker.card.attacks idx attack (by
          simpa [bestAttack] using hBest)).1
      exact ⟨hSound.1, ⟨attack, hGet, hSound.2, rfl⟩⟩

theorem solve_optimal (attacker : PokemonInPlay) (defender : PokemonInPlay) :
    ∀ result, solve attacker defender = some result →
      ∀ j attack',
        listGet? attacker.card.attacks j = some attack' →
        hasEnergyCost attack' attacker.energy = true →
        attackDamage attacker defender attack' ≤ result.expectedDamage := by
  intro result hSolve j attack' hGet hLegal
  cases hBest : bestAttack attacker defender with
  | none =>
    simp [solve, hBest] at hSolve
  | some choice =>
    cases choice with
    | mk idx attack =>
      simp [solve, hBest] at hSolve
      cases hSolve
      have hOptimal := bestAttack_optimal attacker defender idx attack hBest j attack' hGet hLegal
      simpa using hOptimal

def demoDefender : PokemonInPlay :=
  { card := sampleCharmander, damage := 0, status := none, energy := [.fire] }

def corpusSolverResults : List (Card × Option SolverResult) :=
  PokemonLean.Cards.corpus.map (fun card =>
    let attacker : PokemonInPlay := { card := card, damage := 0, status := none, energy := [card.energyType] }
    (card, solve attacker demoDefender))

-- ============================================================================
-- EXAMPLE USAGE
-- ============================================================================

#eval solve { card := sampleCharmander, damage := 0, status := none, energy := [.fire] }
  { card := samplePikachu, damage := 40, status := none, energy := [.lightning] }
-- Should return: attackIndex 0, expectedDamage 30, isLethal true (60 - 40 = 20 remaining, 30 >= 20)

#eval solve { card := sampleSquirtle, damage := 0, status := none, energy := [.water] }
  { card := sampleCharmander, damage := 0, status := none, energy := [.fire] }
-- Should return: attackIndex 0, expectedDamage 40 (weakness), isLethal false

#eval corpusSolverResults

end PokemonLean.Solver
