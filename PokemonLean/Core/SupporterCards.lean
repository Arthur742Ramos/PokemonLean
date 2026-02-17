/-
  PokemonLean / Core / SupporterCards.lean

  Supporter card formalization for core tempo and disruption effects.

  Covers:
  - Supporter timing rules (one per turn, first player cannot play on turn 1)
  - Professor's Research
  - Boss's Orders
  - Judge
  - Iono
  - Roxanne
  - Cynthia's Ambition
  - Hand disruption comparisons

  Self-contained and proof-complete.
-/

namespace PokemonLean.Core.SupporterCards

-- ============================================================
-- §1  Core data model
-- ============================================================

/-- Supporter cards represented in this module. -/
inductive SupporterCard where
  | professorsResearch
  | bossOrders
  | judge
  | iono
  | roxanne
  | cynthiaAmbition
deriving DecidableEq, Repr, BEq, Inhabited

/-- Lightweight Pokémon representation for switching effects. -/
structure PokemonUnit where
  name : String
  hp : Nat := 100
deriving DecidableEq, Repr, Inhabited

/-- Active + bench board representation. -/
structure BoardState where
  active : Option PokemonUnit
  bench : List PokemonUnit
deriving DecidableEq, Repr, Inhabited

/-- Turn-local supporter permissions. -/
structure TurnContext where
  supporterPlayed : Bool
  turnNumber : Nat
  currentPlayerIsFirst : Bool
deriving DecidableEq, Repr, Inhabited

/-- Hand/prize state sufficient for supporter effects here. -/
structure PlayerState where
  handSize : Nat
  prizesRemaining : Nat
deriving DecidableEq, Repr, Inhabited

-- ============================================================
-- §2  Utility helpers
-- ============================================================

/-- Replace item at index in list (structural and total). -/
def replaceAt {α : Type} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, a => a :: xs
  | x :: xs, n + 1, a => x :: replaceAt xs n a

/-- Draw helper: set hand size directly in this abstract model. -/
def setHand (pl : PlayerState) (n : Nat) : PlayerState :=
  { pl with handSize := n }

-- ============================================================
-- §3  Global supporter timing rules
-- ============================================================

/-- Opening-turn restriction for the starting player. -/
def blockedByOpeningRule (ctx : TurnContext) : Bool :=
  ctx.currentPlayerIsFirst && ctx.turnNumber = 1

/-- Can the player play a supporter right now? -/
def canPlaySupporter (ctx : TurnContext) : Bool :=
  !ctx.supporterPlayed && !blockedByOpeningRule ctx

/-- Mark supporter usage for this turn. -/
def markSupporterPlayed (ctx : TurnContext) : TurnContext :=
  { ctx with supporterPlayed := true }

/-- End-turn transition to next player's turn. -/
def endTurn (ctx : TurnContext) : TurnContext :=
  { supporterPlayed := false
    turnNumber := ctx.turnNumber + 1
    currentPlayerIsFirst := !ctx.currentPlayerIsFirst }

/-- Attempt to play a supporter under timing rules. -/
def playSupporterIfLegal (ctx : TurnContext) : Option TurnContext :=
  if canPlaySupporter ctx then
    some (markSupporterPlayed ctx)
  else
    none

-- ============================================================
-- §4  Specific supporter effects
-- ============================================================

/-- Professor's Research fixed draw count in this model. -/
def researchDrawCount : Nat := 7

/-- Professor's Research: discard hand, then draw 7. -/
def applyProfessorsResearch (pl : PlayerState) : PlayerState :=
  setHand pl researchDrawCount

/-- Boss's Orders: force opponent active switch with chosen bench index. -/
def applyBossOrders (oppBoard : BoardState) (benchIdx : Nat) : Option BoardState :=
  match oppBoard.active, oppBoard.bench[benchIdx]? with
  | some currentActive, some target =>
      some
        { active := some target
          bench := replaceAt oppBoard.bench benchIdx currentActive }
  | _, _ => none

/-- Judge draw count. -/
def judgeDrawCount : Nat := 4

/-- Judge: both players shuffle and draw 4. -/
def applyJudge (self opp : PlayerState) : PlayerState × PlayerState :=
  (setHand self judgeDrawCount, setHand opp judgeDrawCount)

/-- Iono: both players shuffle and draw equal to remaining prizes. -/
def applyIono (self opp : PlayerState) : PlayerState × PlayerState :=
  (setHand self self.prizesRemaining, setHand opp opp.prizesRemaining)

/-- Roxanne requirement: opponent at 3 or fewer prizes. -/
def canPlayRoxanne (opp : PlayerState) : Bool :=
  opp.prizesRemaining ≤ 3

/-- Roxanne: if legal, self draws 6 and opponent draws 2. -/
def applyRoxanne (self opp : PlayerState) : Option (PlayerState × PlayerState) :=
  if canPlayRoxanne opp then
    some (setHand self 6, setHand opp 2)
  else
    none

/-- Cynthia's Ambition target hand size model.
    If KO'd last turn: draw 8 extra.
    Otherwise: draw until at least 8 cards. -/
def cynthiaTargetHand (currentHand : Nat) (koLastTurn : Bool) : Nat :=
  if koLastTurn then
    currentHand + 8
  else if currentHand < 8 then
    8
  else
    currentHand

/-- Apply Cynthia's Ambition to a player hand. -/
def applyCynthiaAmbition (pl : PlayerState) (koLastTurn : Bool) : PlayerState :=
  setHand pl (cynthiaTargetHand pl.handSize koLastTurn)

-- ============================================================
-- §5  Hand disruption analysis helpers
-- ============================================================

/-- Hand reduction (Nat-truncated). -/
def handReduction (before after : Nat) : Nat :=
  before - after

/-- Opponent hand reduction from Judge. -/
def judgeReduction (oppHandBefore : Nat) : Nat :=
  handReduction oppHandBefore judgeDrawCount

/-- Opponent hand reduction from Iono. -/
def ionoReduction (oppHandBefore oppPrizes : Nat) : Nat :=
  handReduction oppHandBefore oppPrizes

/-- Opponent hand reduction from Roxanne. -/
def roxanneReduction (oppHandBefore : Nat) : Nat :=
  handReduction oppHandBefore 2

/-- Late-game disruption ordering score used for theoremized ranking. -/
def lateDisruptionRank (card : SupporterCard) (opponentPrizes : Nat) : Nat :=
  match card with
  | .roxanne => 3
  | .iono => if opponentPrizes ≤ 2 then 2 else 1
  | .judge => 1
  | .professorsResearch => 0
  | .bossOrders => 0
  | .cynthiaAmbition => 0

-- ============================================================
-- §6  Sample states
-- ============================================================

def openingFirstCtx : TurnContext :=
  { supporterPlayed := false, turnNumber := 1, currentPlayerIsFirst := true }

def openingSecondCtx : TurnContext :=
  { supporterPlayed := false, turnNumber := 1, currentPlayerIsFirst := false }

def midTurnCtx : TurnContext :=
  { supporterPlayed := false, turnNumber := 4, currentPlayerIsFirst := true }

def alreadyPlayedCtx : TurnContext :=
  { supporterPlayed := true, turnNumber := 5, currentPlayerIsFirst := false }

def selfState : PlayerState :=
  { handSize := 8, prizesRemaining := 4 }

def oppState : PlayerState :=
  { handSize := 8, prizesRemaining := 2 }

def oppLateOnePrize : PlayerState :=
  { handSize := 8, prizesRemaining := 1 }

def oppFourPrizes : PlayerState :=
  { handSize := 8, prizesRemaining := 4 }

def activeMon : PokemonUnit := { name := "Mew ex", hp := 180 }
def benchMon1 : PokemonUnit := { name := "Lumineon V", hp := 170 }
def benchMon2 : PokemonUnit := { name := "Manaphy", hp := 70 }
def benchMon3 : PokemonUnit := { name := "Fezandipiti ex", hp := 210 }

def oppBoard : BoardState :=
  { active := some activeMon
    bench := [benchMon1, benchMon2, benchMon3] }

def boardNoActive : BoardState :=
  { active := none
    bench := [benchMon1] }

def boardNoBench : BoardState :=
  { active := some activeMon
    bench := [] }

-- ============================================================
-- §7  Theorems: supporter timing rules
-- ============================================================

theorem opening_first_player_blocked :
    canPlaySupporter openingFirstCtx = false := by
  decide

theorem opening_second_player_allowed :
    canPlaySupporter openingSecondCtx = true := by
  decide

theorem mid_turn_can_play_if_unused :
    canPlaySupporter midTurnCtx = true := by
  decide

theorem cannot_play_after_supporter_used :
    canPlaySupporter alreadyPlayedCtx = false := by
  decide

theorem mark_supporter_sets_flag (ctx : TurnContext) :
    (markSupporterPlayed ctx).supporterPlayed = true := by
  rfl

theorem mark_supporter_preserves_turn (ctx : TurnContext) :
    (markSupporterPlayed ctx).turnNumber = ctx.turnNumber := by
  rfl

theorem play_supporter_if_legal_succeeds :
    (playSupporterIfLegal midTurnCtx).isSome = true := by
  decide

theorem play_supporter_if_legal_fails_when_blocked :
    playSupporterIfLegal openingFirstCtx = none := by
  decide

theorem one_supporter_per_turn_enforced :
    playSupporterIfLegal (markSupporterPlayed midTurnCtx) = none := by
  decide

theorem end_turn_resets_supporter_usage (ctx : TurnContext) :
    (endTurn ctx).supporterPlayed = false := by
  rfl

theorem end_turn_increments_turn (ctx : TurnContext) :
    (endTurn ctx).turnNumber = ctx.turnNumber + 1 := by
  rfl

theorem end_turn_switches_starting_flag (ctx : TurnContext) :
    (endTurn ctx).currentPlayerIsFirst = !ctx.currentPlayerIsFirst := by
  rfl

-- ============================================================
-- §8  Theorems: Professor's Research
-- ============================================================

theorem research_draw_count_is_seven : researchDrawCount = 7 := by rfl

theorem research_sets_hand_to_seven (pl : PlayerState) :
    (applyProfessorsResearch pl).handSize = 7 := by
  rfl

theorem research_preserves_prizes (pl : PlayerState) :
    (applyProfessorsResearch pl).prizesRemaining = pl.prizesRemaining := by
  rfl

theorem research_from_small_hand_still_seven :
    (applyProfessorsResearch { handSize := 1, prizesRemaining := 6 }).handSize = 7 := by
  rfl

theorem research_from_large_hand_still_seven :
    (applyProfessorsResearch { handSize := 12, prizesRemaining := 2 }).handSize = 7 := by
  rfl

theorem research_always_gives_seven (h p : Nat) :
    (applyProfessorsResearch { handSize := h, prizesRemaining := p }).handSize = 7 := by
  rfl

-- ============================================================
-- §9  Theorems: Boss's Orders
-- ============================================================

theorem boss_valid_index_is_some :
    (applyBossOrders oppBoard 0).isSome = true := by
  decide

theorem boss_forces_switch_to_target :
    (applyBossOrders oppBoard 1).map BoardState.active = some (some benchMon2) := by
  decide

theorem boss_moves_old_active_to_bench_slot :
    (applyBossOrders oppBoard 1).map (fun b => b.bench[1]?) = some (some activeMon) := by
  decide

theorem boss_preserves_bench_length :
    (applyBossOrders oppBoard 2).map (fun b => b.bench.length) = some 3 := by
  decide

theorem boss_invalid_index_fails :
    applyBossOrders oppBoard 99 = none := by
  decide

theorem boss_fails_without_active :
    applyBossOrders boardNoActive 0 = none := by
  decide

theorem boss_fails_without_bench_target :
    applyBossOrders boardNoBench 0 = none := by
  decide

theorem boss_is_forced_switch_not_optional :
    (applyBossOrders oppBoard 0).map BoardState.active ≠ some (some activeMon) := by
  decide

-- ============================================================
-- §10  Theorems: Judge
-- ============================================================

theorem judge_draw_constant : judgeDrawCount = 4 := by rfl

theorem judge_sets_self_to_four :
    (applyJudge selfState oppState).1.handSize = 4 := by
  rfl

theorem judge_sets_opp_to_four :
    (applyJudge selfState oppState).2.handSize = 4 := by
  rfl

theorem judge_is_symmetric_draw :
    (applyJudge selfState oppState).1.handSize = (applyJudge selfState oppState).2.handSize := by
  rfl

theorem judge_reduces_large_opponent_hand :
    judgeReduction 8 = 4 := by
  decide

theorem judge_reduction_positive_when_above_four (h : 4 < oppState.handSize) :
    judgeReduction oppState.handSize > 0 := by
  simpa [judgeReduction, handReduction] using Nat.sub_pos_of_lt h

-- ============================================================
-- §11  Theorems: Iono
-- ============================================================

theorem iono_sets_self_to_own_prizes :
    (applyIono selfState oppState).1.handSize = selfState.prizesRemaining := by
  rfl

theorem iono_sets_opp_to_opp_prizes :
    (applyIono selfState oppState).2.handSize = oppState.prizesRemaining := by
  rfl

theorem iono_late_game_one_prize_draws_one :
    (applyIono selfState oppLateOnePrize).2.handSize = 1 := by
  decide

theorem iono_late_game_two_prize_draws_two :
    (applyIono selfState oppState).2.handSize = 2 := by
  decide

theorem iono_late_game_draw_is_small (self opp : PlayerState)
    (h : opp.prizesRemaining ≤ 2) :
    (applyIono self opp).2.handSize ≤ 2 := by
  simpa [applyIono] using h

theorem iono_reduces_eight_to_two :
    ionoReduction 8 2 = 6 := by
  decide

theorem iono_reduces_eight_to_one :
    ionoReduction 8 1 = 7 := by
  decide

theorem iono_reduction_positive_when_hand_above_prizes (h : oppState.prizesRemaining < oppState.handSize) :
    ionoReduction oppState.handSize oppState.prizesRemaining > 0 := by
  simpa [ionoReduction, handReduction] using Nat.sub_pos_of_lt h

-- ============================================================
-- §12  Theorems: Roxanne
-- ============================================================

theorem roxanne_condition_definition (opp : PlayerState) :
    canPlayRoxanne opp = decide (opp.prizesRemaining ≤ 3) := by
  rfl

theorem roxanne_playable_at_three :
    canPlayRoxanne { handSize := 7, prizesRemaining := 3 } = true := by
  decide

theorem roxanne_playable_at_two :
    canPlayRoxanne { handSize := 7, prizesRemaining := 2 } = true := by
  decide

theorem roxanne_not_playable_at_four :
    canPlayRoxanne oppFourPrizes = false := by
  decide

theorem roxanne_applies_when_legal :
    (applyRoxanne selfState oppState).isSome = true := by
  decide

theorem roxanne_self_draw_is_six :
    (applyRoxanne selfState oppState).map (fun pair => pair.1.handSize) = some 6 := by
  decide

theorem roxanne_opp_draw_is_two :
    (applyRoxanne selfState oppState).map (fun pair => pair.2.handSize) = some 2 := by
  decide

theorem roxanne_fails_when_opponent_above_three :
    applyRoxanne selfState oppFourPrizes = none := by
  decide

theorem roxanne_reduction_from_eight :
    roxanneReduction 8 = 6 := by
  decide

-- ============================================================
-- §13  Theorems: Cynthia's Ambition
-- ============================================================

theorem cynthia_no_ko_draw_to_eight_from_two :
    cynthiaTargetHand 2 false = 8 := by
  decide

theorem cynthia_no_ko_keeps_eight :
    cynthiaTargetHand 8 false = 8 := by
  decide

theorem cynthia_no_ko_keeps_above_eight :
    cynthiaTargetHand 10 false = 10 := by
  decide

theorem cynthia_ko_adds_eight :
    cynthiaTargetHand 3 true = 11 := by
  decide

theorem cynthia_apply_preserves_prizes (pl : PlayerState) (koLastTurn : Bool) :
    (applyCynthiaAmbition pl koLastTurn).prizesRemaining = pl.prizesRemaining := by
  rfl

theorem cynthia_apply_non_ko_sets_minimum_eight :
    (applyCynthiaAmbition { handSize := 1, prizesRemaining := 6 } false).handSize = 8 := by
  decide

theorem cynthia_apply_ko_is_extra_eight :
    (applyCynthiaAmbition { handSize := 5, prizesRemaining := 6 } true).handSize = 13 := by
  decide

-- ============================================================
-- §14  Theorems: hand disruption ordering
-- ============================================================

theorem judge_reduces_opponent_hand_example :
    judgeReduction 9 = 5 := by
  decide

theorem iono_reduces_opponent_hand_example :
    ionoReduction 9 2 = 7 := by
  decide

theorem roxanne_reduces_opponent_hand_example :
    roxanneReduction 9 = 7 := by
  decide

theorem disruption_rank_roxanne_above_iono_late :
    lateDisruptionRank .roxanne 2 > lateDisruptionRank .iono 2 := by
  decide

theorem disruption_rank_iono_late_above_judge :
    lateDisruptionRank .iono 2 > lateDisruptionRank .judge 2 := by
  decide

theorem disruption_rank_ordering_chain :
    lateDisruptionRank .roxanne 2 > lateDisruptionRank .iono 2 ∧
    lateDisruptionRank .iono 2 > lateDisruptionRank .judge 2 := by
  decide

theorem disruption_rank_iono_not_late_equals_judge :
    lateDisruptionRank .iono 4 = lateDisruptionRank .judge 4 := by
  decide

-- ============================================================
-- §15  Small executable checks
-- ============================================================

#eval canPlaySupporter openingFirstCtx
#eval canPlaySupporter openingSecondCtx
#eval (playSupporterIfLegal midTurnCtx).isSome
#eval (applyProfessorsResearch selfState).handSize
#eval (applyBossOrders oppBoard 1).isSome
#eval (applyJudge selfState oppState).2.handSize
#eval (applyIono selfState oppLateOnePrize).2.handSize
#eval (applyRoxanne selfState oppState).isSome
#eval cynthiaTargetHand 5 false
#eval cynthiaTargetHand 5 true
#eval lateDisruptionRank .roxanne 2
#eval lateDisruptionRank .iono 2
#eval lateDisruptionRank .judge 2

end PokemonLean.Core.SupporterCards
