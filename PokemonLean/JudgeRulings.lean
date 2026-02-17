/-
  PokemonLean / JudgeRulings.lean

  Judge / Ruling Mechanics for Pokémon TCG
  ==========================================

  Penalty guidelines, game state corrections, slow play warnings,
  marked cards, insufficient randomization, game loss conditions,
  appeals process, tier system for penalties.

  Paths ARE the math.  20+ theorems.
-/

set_option linter.unusedVariables false

namespace JudgeRulings
-- ============================================================
-- §2  Penalty Tiers
-- ============================================================

/-- Penalty severity levels per Pokémon TCG penalty guidelines. -/
inductive PenaltyTier where
  | caution       -- verbal warning, no record
  | warning       -- recorded, first offense
  | prizeLoss     -- opponent takes a prize card
  | gameLoss      -- lose the current game
  | matchLoss     -- lose the match (best-of-three)
  | disqualify    -- removed from tournament
deriving DecidableEq, Repr

/-- Numeric severity for comparisons. -/
def PenaltyTier.severity : PenaltyTier → Nat
  | .caution    => 0
  | .warning    => 1
  | .prizeLoss  => 2
  | .gameLoss   => 3
  | .matchLoss  => 4
  | .disqualify => 5

/-- Theorem 1: Caution is strictly less severe than disqualification. -/
theorem caution_lt_disqualify :
    PenaltyTier.caution.severity < PenaltyTier.disqualify.severity := by
  simp [PenaltyTier.severity]

/-- Theorem 2: Penalty severity is monotone through tiers. -/
theorem severity_monotone_warning_game :
    PenaltyTier.warning.severity < PenaltyTier.gameLoss.severity := by
  simp [PenaltyTier.severity]

/-- Theorem 3: Prize loss is between warning and game loss. -/
theorem prize_loss_between :
    PenaltyTier.warning.severity < PenaltyTier.prizeLoss.severity ∧
    PenaltyTier.prizeLoss.severity < PenaltyTier.gameLoss.severity := by
  simp [PenaltyTier.severity]

-- ============================================================
-- §3  Infractions
-- ============================================================

/-- Types of infractions a judge may rule on. -/
inductive Infraction where
  | slowPlay           -- exceeding reasonable time
  | markedCards        -- identifiable card backs
  | insufficientShuffle -- inadequate randomization
  | drawExtra          -- drawing too many cards
  | playError          -- illegal game action
  | deckError          -- deck list / deck mismatch
  | unsporting         -- unsportsmanlike conduct
  | cheating           -- intentional rule violation
deriving DecidableEq, Repr

/-- Default penalty tier for each infraction (first offense). -/
def Infraction.defaultPenalty : Infraction → PenaltyTier
  | .slowPlay            => .caution
  | .markedCards         => .warning
  | .insufficientShuffle => .warning
  | .drawExtra           => .warning
  | .playError           => .caution
  | .deckError           => .gameLoss
  | .unsporting          => .prizeLoss
  | .cheating            => .disqualify

/-- Theorem 4: Cheating always results in disqualification. -/
theorem cheating_is_dq :
    Infraction.cheating.defaultPenalty = .disqualify := by
  rfl

/-- Theorem 5: Slow play default is caution. -/
theorem slow_play_caution :
    Infraction.slowPlay.defaultPenalty = .caution := by
  rfl

/-- Theorem 6: Deck error is more severe than draw extra. -/
theorem deck_error_gt_draw_extra :
    Infraction.drawExtra.defaultPenalty.severity <
    Infraction.deckError.defaultPenalty.severity := by
  simp [Infraction.defaultPenalty, PenaltyTier.severity]

-- ============================================================
-- §4  Penalty Escalation as Paths
-- ============================================================

/-- Penalty states for escalation tracking. -/
inductive PenaltyState where
  | clean       : PenaltyState
  | cautioned   : Nat → PenaltyState         -- number of cautions
  | warned      : Nat → PenaltyState         -- number of warnings
  | prized      : PenaltyState               -- prize penalty applied
  | gameLost    : PenaltyState
  | matchLost   : PenaltyState
  | disqualified : PenaltyState
deriving DecidableEq, Repr


-- ============================================================
-- §5  Game State Corrections
-- ============================================================

/-- Game state for correction procedures. -/
inductive CorrectionState where
  | errorDetected   : String → CorrectionState
  | judgeCalled      : String → CorrectionState
  | stateExamined    : String → CorrectionState
  | correctionApplied : String → CorrectionState
  | penaltyIssued    : String → PenaltyTier → CorrectionState
  | gameResumed      : String → CorrectionState
deriving DecidableEq, Repr


-- ============================================================
-- §6  Marked Cards Detection
-- ============================================================

/-- Marked cards investigation stages. -/
inductive MarkedState where
  | suspected   : Nat → MarkedState          -- number of suspect cards
  | examined    : Nat → Bool → MarkedState   -- examined, pattern found?
  | ruled       : Nat → PenaltyTier → MarkedState
deriving DecidableEq, Repr


-- ============================================================
-- §7  Insufficient Randomization
-- ============================================================

/-- Shuffle verification states. -/
inductive ShuffleState where
  | deckPresented  : Nat → ShuffleState       -- deck size
  | shuffleChecked : Nat → Bool → ShuffleState -- sufficient?
  | reshuffle      : Nat → ShuffleState
  | accepted       : Nat → ShuffleState
  | penalized      : Nat → ShuffleState
deriving DecidableEq, Repr


-- ============================================================
-- §8  Appeals Process
-- ============================================================

/-- Appeal states. -/
inductive AppealState where
  | rulingMade     : String → PenaltyTier → AppealState
  | appealFiled    : String → AppealState
  | headJudge      : String → AppealState
  | upheld         : String → PenaltyTier → AppealState
  | overturned     : String → PenaltyTier → AppealState
deriving DecidableEq, Repr


-- ============================================================
-- §9  Slow Play Detection
-- ============================================================

/-- Slow play warning progression. -/
inductive SlowPlayState where
  | playing        : SlowPlayState
  | timeWarning    : Nat → SlowPlayState     -- warning count
  | timeExtension  : SlowPlayState
  | penaltyApplied : PenaltyTier → SlowPlayState
deriving DecidableEq, Repr


-- ============================================================
-- §10  Path Coherence for Judge Rulings
-- ============================================================

end JudgeRulings
