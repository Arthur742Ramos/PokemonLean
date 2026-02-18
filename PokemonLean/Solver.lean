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

-- Consider one energy attachment before attacking.
def applyAttachment (attacker : PokemonInPlay) (energyType : EnergyType) : PokemonInPlay :=
  { attacker with energy := energyType :: attacker.energy }

def bestAttackWithAttachment (attacker : PokemonInPlay) (defender : PokemonInPlay) (energyType : EnergyType) :
    Option (Nat × Attack) :=
  bestAttack (applyAttachment attacker energyType) defender

def bestAttackIndexWithAttachment (attacker : PokemonInPlay) (defender : PokemonInPlay) (energyType : EnergyType) :
    Option Nat :=
  (bestAttackWithAttachment attacker defender energyType).map (fun choice => choice.1)

def attachmentResultDamage (attacker : PokemonInPlay) (defender : PokemonInPlay) (energyType : EnergyType) : Nat :=
  match bestAttackWithAttachment attacker defender energyType with
  | none => 0
  | some (_, attack) => attackDamage (applyAttachment attacker energyType) defender attack

def bestAttachmentFrom (attacker : PokemonInPlay) (defender : PokemonInPlay) : List EnergyType → Option EnergyType
  | [] => none
  | energyType :: rest =>
    let currentDamage := attachmentResultDamage attacker defender energyType
    match bestAttachmentFrom attacker defender rest with
    | none => some energyType
    | some bestEnergy =>
      if currentDamage >= attachmentResultDamage attacker defender bestEnergy then
        some energyType
      else
        some bestEnergy

def allEnergyTypes : List EnergyType :=
  [.fire, .water, .grass, .lightning, .psychic, .fighting, .dark, .metal, .fairy, .dragon, .colorless]

def bestAttachment (attacker : PokemonInPlay) (defender : PokemonInPlay) : Option EnergyType :=
  bestAttachmentFrom attacker defender allEnergyTypes

private theorem bestAttachmentFrom_ne_none (attacker : PokemonInPlay) (defender : PokemonInPlay) :
    ∀ energies, energies ≠ [] → bestAttachmentFrom attacker defender energies ≠ none := by
  intro energies hNonEmpty
  cases energies with
  | nil =>
    cases hNonEmpty rfl
  | cons energyHead rest =>
    intro hNone
    cases hRest : bestAttachmentFrom attacker defender rest with
    | none =>
      simp [bestAttachmentFrom, hRest] at hNone
    | some best =>
      by_cases hCmp :
        attachmentResultDamage attacker defender energyHead >=
          attachmentResultDamage attacker defender best
      · simp [bestAttachmentFrom, hRest, hCmp] at hNone
      · simp [bestAttachmentFrom, hRest, hCmp] at hNone

private theorem bestAttachmentFrom_cons (attacker : PokemonInPlay) (defender : PokemonInPlay)
    (energyHead : EnergyType) (rest : List EnergyType) :
    bestAttachmentFrom attacker defender (energyHead :: rest) =
      match bestAttachmentFrom attacker defender rest with
      | none => some energyHead
      | some bestEnergy =>
        if attachmentResultDamage attacker defender energyHead >=
            attachmentResultDamage attacker defender bestEnergy then
          some energyHead
        else
          some bestEnergy := by
  rfl

theorem bestAttachmentFrom_optimal (attacker : PokemonInPlay) (defender : PokemonInPlay) :
    ∀ energies bestEnergy,
      bestAttachmentFrom attacker defender energies = some bestEnergy →
      ∀ energy ∈ energies,
        attachmentResultDamage attacker defender energy ≤
          attachmentResultDamage attacker defender bestEnergy := by
  intro energies bestEnergy hChoice
  induction energies generalizing bestEnergy with
  | nil =>
    intro energy hMem
    cases hMem
  | cons energyHead rest ih =>
    intro energy hMem
    cases rest with
    | nil =>
      have hChoice' : bestEnergy = energyHead := by
        simpa [bestAttachmentFrom_cons, bestAttachmentFrom] using hChoice.symm
      subst hChoice'
      have hMem' := (List.mem_cons).1 hMem
      cases hMem' with
      | inl hEq =>
        subst hEq
        exact Nat.le_refl _
      | inr hMemTail =>
        cases hMemTail
    | cons energyNext restTail =>
      have hTailNotNone :
          bestAttachmentFrom attacker defender (energyNext :: restTail) ≠ none :=
        bestAttachmentFrom_ne_none attacker defender (energyNext :: restTail) (by simp)
      cases hTail : bestAttachmentFrom attacker defender (energyNext :: restTail) with
      | none =>
        cases (hTailNotNone hTail)
      | some bestTail =>
        by_cases hCmp :
          attachmentResultDamage attacker defender energyHead >=
            attachmentResultDamage attacker defender bestTail
        · have hChoice' : bestEnergy = energyHead := by
            simpa [bestAttachmentFrom_cons, hTail, hCmp] using hChoice.symm
          subst hChoice'
          have hMem' := (List.mem_cons).1 hMem
          cases hMem' with
          | inl hEq =>
            subst hEq
            exact Nat.le_refl _
          | inr hMemTail =>
            have hOptimalTail := ih (bestEnergy := bestTail) hTail energy hMemTail
            exact Nat.le_trans hOptimalTail (by simpa using hCmp)
        · have hChoice' : bestEnergy = bestTail := by
            simpa [bestAttachmentFrom_cons, hTail, hCmp] using hChoice.symm
          subst hChoice'
          have hTail' :
              bestAttachmentFrom attacker defender (energyNext :: restTail) = some bestEnergy := by
            simpa using hTail
          have hMem' := (List.mem_cons).1 hMem
          cases hMem' with
          | inl hEq =>
            subst hEq
            exact Nat.le_of_lt (Nat.lt_of_not_ge hCmp)
          | inr hMemTail =>
            exact ih (bestEnergy := bestEnergy) hTail' energy hMemTail

theorem bestAttachmentFrom_mem (attacker : PokemonInPlay) (defender : PokemonInPlay) :
    ∀ energies bestEnergy,
      bestAttachmentFrom attacker defender energies = some bestEnergy →
      bestEnergy ∈ energies := by
  intro energies bestEnergy hChoice
  induction energies generalizing bestEnergy with
  | nil =>
    cases hChoice
  | cons energyHead rest ih =>
    cases hTail : bestAttachmentFrom attacker defender rest with
    | none =>
      have hChoice' : energyHead = bestEnergy := by
        simpa [bestAttachmentFrom, hTail] using hChoice
      simp [hChoice']
    | some bestTail =>
      by_cases hCmp :
        attachmentResultDamage attacker defender energyHead >=
          attachmentResultDamage attacker defender bestTail
      · have hChoice' : energyHead = bestEnergy := by
          simpa [bestAttachmentFrom, hTail, hCmp] using hChoice
        simp [hChoice']
      · have hChoice' : bestTail = bestEnergy := by
          simpa [bestAttachmentFrom, hTail, hCmp] using hChoice
        have hMemTail : bestTail ∈ rest := ih (bestEnergy := bestTail) hTail
        simpa [hChoice'] using (List.mem_cons_of_mem energyHead hMemTail)

theorem energyType_mem_all (energyType : EnergyType) : energyType ∈ allEnergyTypes := by
  cases energyType <;> simp [allEnergyTypes]

theorem bestAttachment_mem_all (attacker : PokemonInPlay) (defender : PokemonInPlay) :
    ∀ bestEnergy,
      bestAttachment attacker defender = some bestEnergy →
      bestEnergy ∈ allEnergyTypes := by
  intro bestEnergy hChoice
  exact
    bestAttachmentFrom_mem attacker defender allEnergyTypes bestEnergy
      (by simpa [bestAttachment] using hChoice)

theorem bestAttachment_optimal (attacker : PokemonInPlay) (defender : PokemonInPlay) :
    ∀ bestEnergy,
      bestAttachment attacker defender = some bestEnergy →
      ∀ energyType,
        attachmentResultDamage attacker defender energyType ≤
          attachmentResultDamage attacker defender bestEnergy := by
  intro bestEnergy hChoice energyType
  have hChoice' :
      bestAttachmentFrom attacker defender allEnergyTypes = some bestEnergy := by
    simpa [bestAttachment] using hChoice
  exact
    bestAttachmentFrom_optimal attacker defender allEnergyTypes bestEnergy hChoice' energyType
      (energyType_mem_all energyType)

structure TurnSolverResult where
  attachedEnergy : EnergyType
  attackIndex : Nat
  expectedDamage : Nat
  isLethal : Bool
  deriving Repr

def solveTurn (attacker : PokemonInPlay) (defender : PokemonInPlay) : Option TurnSolverResult :=
  match bestAttachment attacker defender with
  | none => none
  | some energyType =>
    match bestAttackWithAttachment attacker defender energyType with
    | none => none
    | some (idx, attack) =>
      let updatedAttacker := applyAttachment attacker energyType
      let damage := attackDamage updatedAttacker defender attack
      let isLethal := damage + defender.damage >= defender.card.hp
      some {
        attachedEnergy := energyType
        attackIndex := idx
        expectedDamage := damage
        isLethal := isLethal
      }

structure TwoPlyResult where
  firstEnergy : EnergyType
  secondEnergy : EnergyType
  attackIndex : Nat
  expectedDamage : Nat
  isLethal : Bool
  deriving Repr

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

theorem bestAttackWithAttachment_sound (attacker : PokemonInPlay) (defender : PokemonInPlay) (energyType : EnergyType) :
    ∀ idx attack,
      bestAttackWithAttachment attacker defender energyType = some (idx, attack) →
      idx < attacker.card.attacks.length ∧
        hasEnergyCost attack (energyType :: attacker.energy) = true := by
  intro idx attack hChoice
  have hSound :=
    bestAttack_sound (applyAttachment attacker energyType) defender idx attack (by
      simpa [bestAttackWithAttachment] using hChoice)
  simpa [applyAttachment] using hSound

theorem solveTurn_optimal (attacker : PokemonInPlay) (defender : PokemonInPlay) :
    ∀ result, solveTurn attacker defender = some result →
      ∀ idx attack,
        listGet? attacker.card.attacks idx = some attack →
        hasEnergyCost attack (result.attachedEnergy :: attacker.energy) = true →
        attackDamage (applyAttachment attacker result.attachedEnergy) defender attack ≤ result.expectedDamage := by
  intro result hSolve idx attack hGet hLegal
  cases hBestEnergy : bestAttachment attacker defender with
  | none =>
    simp [solveTurn, hBestEnergy] at hSolve
  | some energyType =>
    cases hBestAttack : bestAttackWithAttachment attacker defender energyType with
    | none =>
      simp [solveTurn, hBestEnergy, hBestAttack] at hSolve
    | some choice =>
      cases choice with
      | mk bestIdx bestAtk =>
        simp [solveTurn, hBestEnergy, hBestAttack] at hSolve
        cases hSolve
        have hBest :=
          bestAttack_optimal (applyAttachment attacker energyType) defender bestIdx bestAtk
            (by simpa [bestAttackWithAttachment, bestAttack, applyAttachment] using hBestAttack)
        have hGet' : listGet? (applyAttachment attacker energyType).card.attacks idx = some attack := by
          simpa [applyAttachment] using hGet
        have hOptimalAttack :=
          hBest idx attack hGet' (by simpa [applyAttachment] using hLegal)
        simpa [applyAttachment] using hOptimalAttack

theorem solveTurn_sound (attacker : PokemonInPlay) (defender : PokemonInPlay) :
    ∀ result, solveTurn attacker defender = some result →
      ∃ energyType attack,
        result.attachedEnergy = energyType ∧
          listGet? attacker.card.attacks result.attackIndex = some attack ∧
          hasEnergyCost attack (energyType :: attacker.energy) = true ∧
          result.expectedDamage = attackDamage (applyAttachment attacker energyType) defender attack := by
  intro result hSolve
  cases hBestEnergy : bestAttachment attacker defender with
  | none =>
    simp [solveTurn, hBestEnergy] at hSolve
  | some energyType =>
    cases hBestAttack : bestAttackWithAttachment attacker defender energyType with
    | none =>
      simp [solveTurn, hBestEnergy, hBestAttack] at hSolve
    | some choice =>
      cases choice with
      | mk idx attack =>
        simp [solveTurn, hBestEnergy, hBestAttack] at hSolve
        cases hSolve
        have hSound := bestAttackWithAttachment_sound attacker defender energyType idx attack hBestAttack
        refine ⟨energyType, attack, rfl, ?_, hSound.2, rfl⟩
        simpa [bestAttackWithAttachment, applyAttachment] using
          (bestAttackFrom_sound (applyAttachment attacker energyType) defender attacker.card.attacks idx attack
            (by simpa [bestAttack, applyAttachment] using hBestAttack)).1

def applyAttachments (attacker : PokemonInPlay) (first second : EnergyType) : PokemonInPlay :=
  applyAttachment (applyAttachment attacker first) second

def bestAttackWithAttachments (attacker : PokemonInPlay) (defender : PokemonInPlay)
    (first second : EnergyType) : Option (Nat × Attack) :=
  bestAttack (applyAttachments attacker first second) defender

def solveTwoPly (attacker : PokemonInPlay) (defender : PokemonInPlay) : Option TwoPlyResult :=
  match solveTurn attacker defender with
  | none => none
  | some firstResult =>
    let updatedAttacker := applyAttachment attacker firstResult.attachedEnergy
    match solveTurn updatedAttacker defender with
    | none => none
    | some secondResult =>
      some {
        firstEnergy := firstResult.attachedEnergy
        secondEnergy := secondResult.attachedEnergy
        attackIndex := secondResult.attackIndex
        expectedDamage := secondResult.expectedDamage
        isLethal := secondResult.isLethal
      }

theorem solveTwoPly_sound (attacker : PokemonInPlay) (defender : PokemonInPlay) :
    ∀ result, solveTwoPly attacker defender = some result →
      ∃ first second attack,
        result.firstEnergy = first ∧
          result.secondEnergy = second ∧
          listGet? attacker.card.attacks result.attackIndex = some attack ∧
          hasEnergyCost attack (second :: first :: attacker.energy) = true ∧
          result.expectedDamage =
            attackDamage (applyAttachment (applyAttachment attacker first) second) defender attack := by
  intro result hSolve
  cases hFirst : solveTurn attacker defender with
  | none =>
    simp [solveTwoPly, hFirst] at hSolve
  | some firstResult =>
    cases hSecond : solveTurn (applyAttachment attacker firstResult.attachedEnergy) defender with
    | none =>
      simp [solveTwoPly, hFirst, hSecond] at hSolve
    | some secondResult =>
      simp [solveTwoPly, hFirst, hSecond] at hSolve
      cases hSolve
      have hSound :=
        solveTurn_sound (applyAttachment attacker firstResult.attachedEnergy) defender secondResult
          (by simpa using hSecond)
      rcases hSound with ⟨second, attack, hSecondEnergy, hGet, hLegal, hDamage⟩
      refine ⟨firstResult.attachedEnergy, second, attack, rfl, hSecondEnergy, ?_, ?_, ?_⟩
      · simpa [applyAttachment] using hGet
      · simpa [applyAttachment] using hLegal
      · simpa [applyAttachment] using hDamage

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
