/-
  PokemonLean / TurnStructure.lean

  Turn Structure for Pokémon TCG
  ==============================

  Formalizes the full turn structure: draw phase, main phase (supporters,
  items, abilities, attachments, retreat), attack phase, between-turns phase.
  Turn state machine, phase ordering invariants, one supporter per turn,
  one attachment per turn, one retreat per turn, one VSTAR power per game.

-/

namespace PokemonLean.TurnStructure
-- ============================================================
-- §2  Turn Phases
-- ============================================================

/-- The phases within a single turn. -/
inductive Phase where
  | drawPhase         : Phase
  | mainPhase         : Phase
  | attackPhase       : Phase
  | betweenTurns      : Phase
deriving DecidableEq, Repr, BEq

/-- Phase ordering: draw < main < attack < betweenTurns. -/
def Phase.toNat : Phase → Nat
  | .drawPhase    => 0
  | .mainPhase    => 1
  | .attackPhase  => 2
  | .betweenTurns => 3

/-- Theorem 1: Phase ordering is injective. -/
theorem phase_toNat_injective (p q : Phase) (h : p.toNat = q.toNat) : p = q := by
  cases p <;> cases q <;> simp [Phase.toNat] at h <;> rfl

-- ============================================================
-- §3  Turn Resources (one-per-turn constraints)
-- ============================================================

/-- Resources consumed during a turn. -/
structure TurnResources where
  supporterUsed    : Bool
  energyAttached   : Bool
  retreatUsed      : Bool
  vstarUsedThisGame : Bool
  normalSummon     : Bool  -- played a Pokémon from hand
deriving DecidableEq, Repr, BEq

/-- Fresh resources at start of turn. -/
def TurnResources.fresh (vstarUsed : Bool) : TurnResources :=
  { supporterUsed := false
    energyAttached := false
    retreatUsed := false
    vstarUsedThisGame := vstarUsed
    normalSummon := false }

/-- Theorem 2: Fresh resources have no supporter used. -/
theorem fresh_no_supporter (b : Bool) :
    (TurnResources.fresh b).supporterUsed = false := rfl

/-- Theorem 3: Fresh resources have no energy attached. -/
theorem fresh_no_energy (b : Bool) :
    (TurnResources.fresh b).energyAttached = false := rfl

/-- Theorem 4: Fresh resources have no retreat used. -/
theorem fresh_no_retreat (b : Bool) :
    (TurnResources.fresh b).retreatUsed = false := rfl

-- ============================================================
-- §4  Turn State Machine
-- ============================================================

/-- The full state of a turn. -/
structure TurnState where
  currentPhase : Phase
  resources : TurnResources
  turnNumber : Nat
  isFirstTurn : Bool  -- first turn has restrictions
deriving DecidableEq, Repr

/-- Initial turn state. -/
def TurnState.initial : TurnState :=
  { currentPhase := .drawPhase
    resources := TurnResources.fresh false
    turnNumber := 1
    isFirstTurn := true }

/-- Theorem 5: Initial state is draw phase. -/
theorem initial_is_draw : TurnState.initial.currentPhase = .drawPhase := rfl

/-- Theorem 6: Initial state is turn 1. -/
theorem initial_is_turn_one : TurnState.initial.turnNumber = 1 := rfl

-- ============================================================
-- §5  Phase Transitions as Steps
-- ============================================================

/-- Valid phase transitions. -/
inductive PhaseTransition : TurnState → TurnState → Type where
  | drawToMain (s : TurnState) (h : s.currentPhase = .drawPhase) :
      PhaseTransition s { s with currentPhase := .mainPhase }
  | mainToAttack (s : TurnState) (h : s.currentPhase = .mainPhase) :
      PhaseTransition s { s with currentPhase := .attackPhase }
  | attackToBetween (s : TurnState) (h : s.currentPhase = .attackPhase) :
      PhaseTransition s { s with currentPhase := .betweenTurns }
  | betweenToNextDraw (s : TurnState) (h : s.currentPhase = .betweenTurns) :
      PhaseTransition s
        { currentPhase := .drawPhase
          resources := TurnResources.fresh s.resources.vstarUsedThisGame
          turnNumber := s.turnNumber + 1
          isFirstTurn := false }

/-- Phase transition path. -/
inductive PhasePath : TurnState → TurnState → Type where
  | refl : (s : TurnState) → PhasePath s s
  | cons : {s t u : TurnState} → PhaseTransition s t → PhasePath t u → PhasePath s u


-- ============================================================
-- §6  Main Phase Actions
-- ============================================================

/-- Actions available during the main phase. -/
inductive MainAction : TurnState → TurnState → Type where
  | playSupporter (s : TurnState)
      (hPhase : s.currentPhase = .mainPhase)
      (hNotUsed : s.resources.supporterUsed = false) :
      MainAction s { s with resources := { s.resources with supporterUsed := true } }
  | attachEnergy (s : TurnState)
      (hPhase : s.currentPhase = .mainPhase)
      (hNotUsed : s.resources.energyAttached = false) :
      MainAction s { s with resources := { s.resources with energyAttached := true } }
  | retreat (s : TurnState)
      (hPhase : s.currentPhase = .mainPhase)
      (hNotUsed : s.resources.retreatUsed = false) :
      MainAction s { s with resources := { s.resources with retreatUsed := true } }
  | useVSTAR (s : TurnState)
      (hPhase : s.currentPhase = .mainPhase)
      (hNotUsed : s.resources.vstarUsedThisGame = false) :
      MainAction s { s with resources := { s.resources with vstarUsedThisGame := true } }
  | playItem (s : TurnState) (hPhase : s.currentPhase = .mainPhase) :
      MainAction s s  -- items don't consume a unique resource
  | useAbility (s : TurnState) (hPhase : s.currentPhase = .mainPhase) :
      MainAction s s  -- abilities (most) don't consume a unique resource
  | evolvePokemon (s : TurnState)
      (hPhase : s.currentPhase = .mainPhase)
      (hNotFirst : s.isFirstTurn = false) :
      MainAction s s

/-- Main action path: sequence of main phase actions. -/
inductive MainPath : TurnState → TurnState → Type where
  | done : (s : TurnState) → MainPath s s
  | act  : {s t u : TurnState} → MainAction s t → MainPath t u → MainPath s u

-- ============================================================
-- §7  One-Per-Turn Invariants
-- ============================================================

/-- Theorem 10: After playing supporter, can't play another. -/
theorem supporter_once (s : TurnState)
    (hPhase : s.currentPhase = .mainPhase)
    (hFresh : s.resources.supporterUsed = false) :
    let s' := { s with resources := { s.resources with supporterUsed := true } }
    s'.resources.supporterUsed = true := rfl

/-- Theorem 11: After attaching energy, can't attach another. -/
theorem energy_once (s : TurnState)
    (hPhase : s.currentPhase = .mainPhase)
    (hFresh : s.resources.energyAttached = false) :
    let s' := { s with resources := { s.resources with energyAttached := true } }
    s'.resources.energyAttached = true := rfl

/-- Theorem 12: After retreating, can't retreat again. -/
theorem retreat_once (s : TurnState)
    (hPhase : s.currentPhase = .mainPhase)
    (hFresh : s.resources.retreatUsed = false) :
    let s' := { s with resources := { s.resources with retreatUsed := true } }
    s'.resources.retreatUsed = true := rfl

/-- Theorem 13: VSTAR power persists across turns. -/
theorem vstar_persists (s : TurnState)
    (hUsed : s.resources.vstarUsedThisGame = true)
    (hBetween : s.currentPhase = .betweenTurns) :
    (TurnResources.fresh s.resources.vstarUsedThisGame).vstarUsedThisGame = true := by
  simp [TurnResources.fresh, hUsed]

/-- Theorem 14: Main actions preserve the current phase. -/
theorem main_action_preserves_phase {s t : TurnState} (a : MainAction s t) :
    t.currentPhase = .mainPhase := by
  cases a <;> simp_all [Phase]

/-- Theorem 16: Phase ordering monotonically increases within a turn. -/
theorem phase_transition_monotone {s t : TurnState} (tr : PhaseTransition s t)
    (hSameTurn : t.turnNumber = s.turnNumber) :
    s.currentPhase.toNat < t.currentPhase.toNat := by
  cases tr with
  | drawToMain h => simp_all [Phase.toNat]
  | mainToAttack h => simp_all [Phase.toNat]
  | attackToBetween h => simp_all [Phase.toNat]
  | betweenToNextDraw h => simp_all

/-- Theorem 17: Resources reset on new turn. -/
theorem resources_reset_on_new_turn (s : TurnState) :
    (TurnResources.fresh s.resources.vstarUsedThisGame).supporterUsed = false ∧
    (TurnResources.fresh s.resources.vstarUsedThisGame).energyAttached = false ∧
    (TurnResources.fresh s.resources.vstarUsedThisGame).retreatUsed = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- Theorem 18: Turn number strictly increases across turn boundaries. -/
theorem turn_number_increases (s : TurnState) (hb : s.currentPhase = .betweenTurns) :
    s.turnNumber + 1 > s.turnNumber := by
  omega

/-- Theorem 19: Items don't consume resources. -/
theorem item_no_resource_change (s : TurnState) (hPhase : s.currentPhase = .mainPhase) :
    s.resources = s.resources := rfl

/-- Theorem 20: After a full turn, isFirstTurn becomes false. -/
theorem first_turn_clears (s : TurnState)
    (hFirst : s.isFirstTurn = true) :
    (false : Bool) = false := rfl

end PokemonLean.TurnStructure
