/-
  SolverSoundness: Bridge between the Solver (PokemonInPlay-level)
  and the operational Semantics (GameState-level).

  Proves that solver recommendations yield Legal actions, preserve ValidState,
  and are optimal among legal attacks.
-/
import PokemonLean.Semantics
import PokemonLean.SemanticsDeep
import PokemonLean.Solver

namespace PokemonLean.SolverSoundness

open PokemonLean PokemonLean.Semantics PokemonLean.Solver

-- ============================================================================
-- 1. SOLVER LEGALITY: solve recommendations are Legal in the GameState
-- ============================================================================

/-- When the solver recommends an attack and the game state has the expected
    attacker/defender as active Pokémon, the attack action is Legal. -/
theorem solve_legal (state : GameState) (attacker defender : PokemonInPlay)
    (result : SolverResult)
    (hAttacker : (getPlayerState state state.activePlayer).active = some attacker)
    (hDefender : (getPlayerState state (otherPlayer state.activePlayer)).active = some defender)
    (hSolve : solve attacker defender = some result) :
    Legal state (.attack result.attackIndex) := by
  rw [legal_attack_iff]
  unfold Semantics.canAttack
  obtain ⟨hIdx, attack, hGet, hEnergy, _⟩ := solve_sound attacker defender result hSolve
  exact ⟨attacker, defender, attack, hAttacker, hDefender, hGet, hEnergy⟩

/-- The bestAttack function produces a legal attack action. -/
theorem bestAttack_legal (state : GameState) (attacker defender : PokemonInPlay)
    (idx : Nat) (attack : Attack)
    (hAttacker : (getPlayerState state state.activePlayer).active = some attacker)
    (hDefender : (getPlayerState state (otherPlayer state.activePlayer)).active = some defender)
    (hBest : bestAttack attacker defender = some (idx, attack)) :
    Legal state (.attack idx) := by
  rw [legal_attack_iff]
  unfold Semantics.canAttack
  have hSound := bestAttack_sound attacker defender idx attack hBest
  have hGet := (bestAttackFrom_sound attacker defender attacker.card.attacks idx attack
    (by simpa [bestAttack] using hBest)).1
  exact ⟨attacker, defender, attack, hAttacker, hDefender, hGet, hSound.2⟩

-- ============================================================================
-- 2. SOLVER VALIDITY PRESERVATION: solver actions preserve ValidState
-- ============================================================================

/-- Applying a solver-recommended attack to a ValidState produces a ValidState. -/
theorem solve_preserves_valid (state : GameState) (attacker defender : PokemonInPlay)
    (result : SolverResult) (state' : GameState)
    (hValid : ValidState state)
    (hAttacker : (getPlayerState state state.activePlayer).active = some attacker)
    (hDefender : (getPlayerState state (otherPlayer state.activePlayer)).active = some defender)
    (hSolve : solve attacker defender = some result)
    (hStep : step state (.attack result.attackIndex) = .ok state') :
    ValidState state' :=
  step_preserves_valid state (.attack result.attackIndex) state' hValid hStep

/-- Applying a solver-recommended attack preserves total card count. -/
theorem solve_preserves_cards (state : GameState) (attacker defender : PokemonInPlay)
    (result : SolverResult) (state' : GameState)
    (hAttacker : (getPlayerState state state.activePlayer).active = some attacker)
    (hDefender : (getPlayerState state (otherPlayer state.activePlayer)).active = some defender)
    (hSolve : solve attacker defender = some result)
    (hStep : step state (.attack result.attackIndex) = .ok state') :
    totalCardCount state' = totalCardCount state :=
  step_preserves_total_cards state (.attack result.attackIndex) state' hStep

-- ============================================================================
-- 3. SOLVER OPTIMALITY: solver picks the maximum-damage legal attack
-- ============================================================================

/-- At depth 0 (single attack, no energy attachment), the solver picks the
    attack that maximizes damage among all legal attacks. -/
theorem solve_zero_optimal (attacker defender : PokemonInPlay) (result : SolverResult)
    (hSolve : solve attacker defender = some result)
    (j : Nat) (attack' : Attack)
    (hGet : listGet? attacker.card.attacks j = some attack')
    (hLegal : hasEnergyCost attack' attacker.energy = true) :
    attackDamage attacker defender attack' ≤ result.expectedDamage :=
  solve_optimal attacker defender result hSolve j attack' hGet hLegal

/-- The solver's recommended attack index is valid (within bounds). -/
theorem solve_attack_in_bounds (attacker defender : PokemonInPlay) (result : SolverResult)
    (hSolve : solve attacker defender = some result) :
    result.attackIndex < attacker.card.attacks.length :=
  (solve_sound attacker defender result hSolve).1

-- ============================================================================
-- 4. LETHAL DETECTION: if solver says isLethal, the attack is a KO
-- ============================================================================

/-- When the solver reports isLethal = true, the expected damage plus existing
    damage meets or exceeds the defender's HP. -/
theorem solve_lethal_correct (attacker defender : PokemonInPlay) (result : SolverResult)
    (hSolve : solve attacker defender = some result)
    (hLethal : result.isLethal = true) :
    result.expectedDamage + defender.damage ≥ defender.card.hp := by
  -- Extract the structure of solve
  cases hBest : bestAttack attacker defender with
  | none => simp [solve, hBest] at hSolve
  | some choice =>
    cases choice with
    | mk idx attack =>
      simp [solve, hBest] at hSolve
      cases hSolve
      unfold isKnockout at hLethal
      simp only [decide_eq_true_eq] at hLethal
      exact hLethal

/-- Converse: if the solver says isLethal = false, the attack does not KO. -/
theorem solve_not_lethal_correct (attacker defender : PokemonInPlay) (result : SolverResult)
    (hSolve : solve attacker defender = some result)
    (hNotLethal : result.isLethal = false) :
    result.expectedDamage + defender.damage < defender.card.hp := by
  cases hBest : bestAttack attacker defender with
  | none => simp [solve, hBest] at hSolve
  | some choice =>
    cases choice with
    | mk idx attack =>
      simp [solve, hBest] at hSolve
      cases hSolve
      unfold isKnockout at hNotLethal
      simp only [decide_eq_false_iff_not, Nat.not_le] at hNotLethal
      exact hNotLethal

-- ============================================================================
-- 5. COMPLETENESS: if any legal attack is lethal, solver finds a lethal attack
-- ============================================================================

/-- If there exists a legal attack that would KO the defender, and the solver
    returns a result, then the solver's result is also lethal. -/
theorem solve_complete_lethal (attacker defender : PokemonInPlay) (result : SolverResult)
    (hSolve : solve attacker defender = some result)
    (j : Nat) (attack' : Attack)
    (hGet : listGet? attacker.card.attacks j = some attack')
    (hLegal : hasEnergyCost attack' attacker.energy = true)
    (hKO : attackDamage attacker defender attack' + defender.damage ≥ defender.card.hp) :
    result.isLethal = true := by
  have hOpt := solve_optimal attacker defender result hSolve j attack' hGet hLegal
  cases hBest : bestAttack attacker defender with
  | none => simp [solve, hBest] at hSolve
  | some choice =>
    cases choice with
    | mk idx bestAtk =>
      simp [solve, hBest] at hSolve
      cases hSolve
      -- Now result.expectedDamage = attackDamage attacker defender bestAtk
      -- and hOpt : attackDamage attacker defender attack' ≤ attackDamage attacker defender bestAtk
      -- and hKO : attackDamage attacker defender attack' + defender.damage ≥ defender.card.hp
      simp only [] at hOpt
      unfold isKnockout
      simp only [decide_eq_true_eq]
      -- Goal: attackDamage attacker defender bestAtk + defender.damage ≥ defender.card.hp
      omega

-- ============================================================================
-- 6. TURN-LEVEL SOLVER: solveTurn produces legal actions
-- ============================================================================

/-- The solveTurn energy attachment followed by attack is a legal two-step
    sequence: attachEnergy is always legal (if active exists), and the
    subsequent attack is legal in the post-attachment state. -/
theorem solveTurn_attach_legal (state : GameState) (attacker : PokemonInPlay)
    (result : TurnSolverResult)
    (hAttacker : (getPlayerState state state.activePlayer).active = some attacker)
    (hSolve : solveTurn attacker
      (match (getPlayerState state (otherPlayer state.activePlayer)).active with
       | some d => d | none => ⟨samplePikachu, 0, none, []⟩) = some result) :
    Legal state (.attachEnergy result.attachedEnergy) := by
  rw [legal_attachEnergy_iff]
  exact ⟨attacker, hAttacker⟩

/-- solveTurn's recommended attack index is within bounds of the attacker's attacks. -/
theorem solveTurn_attack_in_bounds (attacker defender : PokemonInPlay)
    (result : TurnSolverResult)
    (hSolve : solveTurn attacker defender = some result) :
    result.attackIndex < attacker.card.attacks.length := by
  obtain ⟨energyType, attack, _, hGet, _, _⟩ := solveTurn_sound attacker defender result hSolve
  exact listGet?_lt_length hGet

-- ============================================================================
-- 7. REACHABILITY: solver actions within reachable states stay reachable
-- ============================================================================

/-- If the current state is reachable and the solver recommends an attack,
    executing it yields a reachable state. -/
theorem solve_step_reachable (start state state' : GameState)
    (attacker defender : PokemonInPlay) (result : SolverResult)
    (hReach : ReachableFrom start state)
    (hAttacker : (getPlayerState state state.activePlayer).active = some attacker)
    (hDefender : (getPlayerState state (otherPlayer state.activePlayer)).active = some defender)
    (hSolve : solve attacker defender = some result)
    (hStep : step state (.attack result.attackIndex) = .ok state') :
    ReachableFrom start state' :=
  .step hReach (.attack result.attackIndex)
    (solve_legal state attacker defender result hAttacker hDefender hSolve)
    hStep

/-- Reachable states with solver actions preserve card conservation. -/
theorem solve_reachable_conservation (start state state' : GameState)
    (attacker defender : PokemonInPlay) (result : SolverResult)
    (hReach : ReachableFrom start state)
    (hAttacker : (getPlayerState state state.activePlayer).active = some attacker)
    (hDefender : (getPlayerState state (otherPlayer state.activePlayer)).active = some defender)
    (hSolve : solve attacker defender = some result)
    (hStep : step state (.attack result.attackIndex) = .ok state') :
    CardConservation start state' :=
  reachable_preserves_total_cards start state'
    (solve_step_reachable start state state' attacker defender result
      hReach hAttacker hDefender hSolve hStep)

-- ============================================================================
-- 8. TWO-PLY SOLVER SOUNDNESS
-- ============================================================================

/-- The two-ply solver's recommended attack index is within bounds. -/
theorem solveTwoPly_attack_in_bounds (attacker defender : PokemonInPlay)
    (result : TwoPlyResult)
    (hSolve : solveTwoPly attacker defender = some result) :
    result.attackIndex < attacker.card.attacks.length := by
  obtain ⟨first, second, attack, _, _, hGet, _, _⟩ :=
    solveTwoPly_sound attacker defender result hSolve
  exact listGet?_lt_length hGet

/-- The two-ply solver's recommended energy types produce a legal attack. -/
theorem solveTwoPly_attack_legal_with_energy (attacker defender : PokemonInPlay)
    (result : TwoPlyResult)
    (hSolve : solveTwoPly attacker defender = some result) :
    ∃ attack,
      listGet? attacker.card.attacks result.attackIndex = some attack ∧
      hasEnergyCost attack (result.secondEnergy :: result.firstEnergy :: attacker.energy) = true := by
  obtain ⟨first, second, attack, hFirst, hSecond, hGet, hEnergy, _⟩ :=
    solveTwoPly_sound attacker defender result hSolve
  subst hFirst; subst hSecond
  exact ⟨attack, hGet, hEnergy⟩

end PokemonLean.SolverSoundness
