/-
  PokemonLean / Core / PrizeMapping.lean

  Prize card system deep dive.

  Covers:
  - Initial 6 prizes from top of deck
  - Prize values by KO target type
  - Prize-taking and monotonic decrease
  - Win condition at 0 prizes remaining
  - Trade analysis (risk/reward and ratio)
  - Single-prize denial patterns
  - 7-prize mixed-board scenarios
  - Path-to-victory KO counts

  Self-contained and proof-complete.
-/

namespace PokemonLean.Core.PrizeMapping

-- ============================================================
-- §1  Prize value taxonomy
-- ============================================================

/-- KO target classes relevant to prize mapping. -/
inductive PrizeTargetKind where
  | regular
  | ex
  | gx
  | v
  | vstar
  | vmax
  | tagTeam
deriving DecidableEq, Repr, BEq, Inhabited

/-- Prize cards taken when this target is KO'd. -/
def prizesFromKO : PrizeTargetKind → Nat
  | .regular => 1
  | .ex => 2
  | .gx => 2
  | .v => 2
  | .vstar => 2
  | .vmax => 3
  | .tagTeam => 3

/-- Total prizes needed to win by taking prizes. -/
def totalPrizesToWin : Nat := 6

/-- Initial player prize count. -/
def initialPrizeCount : Nat := totalPrizesToWin

-- ============================================================
-- §2  Prize setup from deck top
-- ============================================================

/-- Set aside top six cards as prizes (or fewer if deck is shorter). -/
def setAsidePrizeCards {α : Type} (deckTopToBottom : List α) : List α :=
  deckTopToBottom.take totalPrizesToWin

/-- Count prize cards set aside at setup. -/
def setupPrizeCount {α : Type} (deckTopToBottom : List α) : Nat :=
  (setAsidePrizeCards deckTopToBottom).length

-- ============================================================
-- §3  Prize taking and win progression
-- ============================================================

/-- Remaining prizes after taking some prizes from a KO sequence. -/
def prizesRemainingAfter (currentPrizes : Nat) (taken : Nat) : Nat :=
  currentPrizes - taken

/-- Boolean prize win condition. -/
def wonByPrizes (remaining : Nat) : Bool :=
  remaining = 0

/-- Apply one KO to current prize count. -/
def applyKO (currentPrizes : Nat) (target : PrizeTargetKind) : Nat :=
  prizesRemainingAfter currentPrizes (prizesFromKO target)

-- ============================================================
-- §4  Trade model
-- ============================================================

/-- Simple favorable trade predicate. -/
def favorableTrade (prizesTaken prizesGiven : Nat) : Bool :=
  prizesTaken > prizesGiven

/-- Non-strict favorable trade predicate. -/
def nonLosingTrade (prizesTaken prizesGiven : Nat) : Bool :=
  prizesTaken ≥ prizesGiven

/-- Ratio stored as numerator/denominator pair. -/
def tradeRatio (prizesTaken prizesGiven : Nat) : Nat × Nat :=
  (prizesTaken, prizesGiven)

/-- Compare two trade ratios aTaken/aGiven and bTaken/bGiven by cross-multiplication. -/
def ratioBetter (aTaken aGiven bTaken bGiven : Nat) : Bool :=
  aTaken * bGiven > bTaken * aGiven

-- ============================================================
-- §5  Attacker risk/reward classes
-- ============================================================

/-- Prize liability of your attacker when it gets KO'd. -/
inductive AttackerClass where
  | singlePrize
  | twoPrize
  | threePrize
deriving DecidableEq, Repr, BEq, Inhabited

/-- How many prizes opponent takes when this attacker is KO'd. -/
def prizesGivenOnKO : AttackerClass → Nat
  | .singlePrize => 1
  | .twoPrize => 2
  | .threePrize => 3

/-- Simplified HP profile for risk/reward discussion. -/
def attackerHP : AttackerClass → Nat
  | .singlePrize => 120
  | .twoPrize => 220
  | .threePrize => 330

/-- Simplified attack output profile for risk/reward discussion. -/
def attackerDamage : AttackerClass → Nat
  | .singlePrize => 120
  | .twoPrize => 220
  | .threePrize => 320

/-- Prize denial score: lower prize liability yields higher denial score. -/
def prizeDenialScore (cls : AttackerClass) : Nat :=
  4 - prizesGivenOnKO cls

-- ============================================================
-- §6  Board prize maps
-- ============================================================

/-- Total prizes available on a mapped board. -/
def totalBoardPrizes (board : List PrizeTargetKind) : Nat :=
  board.foldl (fun acc k => acc + prizesFromKO k) 0

/-- Uniform path-to-victory KO count: ceil(6 / prizeValue). -/
def minKOsForUniformTarget (k : PrizeTargetKind) : Nat :=
  (totalPrizesToWin + prizesFromKO k - 1) / prizesFromKO k

-- ============================================================
-- §7  Sample objects
-- ============================================================

def fullDeckSample : List Nat := [1,2,3,4,5,6,7,8,9,10]
def shortDeckSample : List Nat := [1,2,3,4]

def mixedBoardSevenPrizes : List PrizeTargetKind :=
  [.regular, .regular, .regular, .ex, .ex]

def mixedBoardSixPrizes : List PrizeTargetKind :=
  [.regular, .regular, .regular, .regular, .ex]

def mixedBoardEightPrizes : List PrizeTargetKind :=
  [.vmax, .ex, .regular, .regular, .regular]

-- ============================================================
-- §8  Theorems: setup and initial prizes
-- ============================================================

theorem initial_prize_count_is_six : initialPrizeCount = 6 := by rfl

theorem total_prizes_to_win_is_six : totalPrizesToWin = 6 := by rfl

theorem setup_takes_top_six_cards :
    setAsidePrizeCards fullDeckSample = [1,2,3,4,5,6] := by
  rfl

theorem setup_prize_count_full_deck :
    setupPrizeCount fullDeckSample = 6 := by
  rfl

theorem setup_prize_count_short_deck :
    setupPrizeCount shortDeckSample = 4 := by
  rfl

theorem setup_prizes_are_prefix :
    setAsidePrizeCards fullDeckSample ++ [7,8,9,10] = fullDeckSample := by
  rfl

theorem start_with_six_prizes_standard :
    setupPrizeCount fullDeckSample = initialPrizeCount := by
  rfl

-- ============================================================
-- §9  Theorems: prize values by target type
-- ============================================================

theorem regular_gives_one : prizesFromKO .regular = 1 := by rfl

theorem ex_gives_two : prizesFromKO .ex = 2 := by rfl

theorem gx_gives_two : prizesFromKO .gx = 2 := by rfl

theorem v_gives_two : prizesFromKO .v = 2 := by rfl

theorem vstar_gives_two : prizesFromKO .vstar = 2 := by rfl

theorem vmax_gives_three : prizesFromKO .vmax = 3 := by rfl

theorem tag_team_gives_three : prizesFromKO .tagTeam = 3 := by rfl

theorem all_targets_give_at_least_one (k : PrizeTargetKind) : prizesFromKO k ≥ 1 := by
  cases k <;> decide

theorem all_targets_give_at_most_three (k : PrizeTargetKind) : prizesFromKO k ≤ 3 := by
  cases k <;> decide

theorem multi_prize_targets_are_non_regular (k : PrizeTargetKind)
    (h : prizesFromKO k ≥ 2) : k ≠ .regular := by
  cases k <;> simp [prizesFromKO] at h ⊢

-- ============================================================
-- §10  Theorems: monotonic prize decrease and win checks
-- ============================================================

theorem prizes_remaining_nonincreasing (current taken : Nat) :
    prizesRemainingAfter current taken ≤ current := by
  exact Nat.sub_le _ _

theorem taking_more_prizes_decreases_more (current t1 t2 : Nat) (h : t1 ≤ t2) :
    prizesRemainingAfter current t2 ≤ prizesRemainingAfter current t1 := by
  simpa [prizesRemainingAfter] using Nat.sub_le_sub_left h current

theorem apply_ko_nonincreasing (current : Nat) (k : PrizeTargetKind) :
    applyKO current k ≤ current := by
  simpa [applyKO] using prizes_remaining_nonincreasing current (prizesFromKO k)

theorem win_when_remaining_zero : wonByPrizes 0 = true := by rfl

theorem not_win_when_remaining_positive : wonByPrizes 1 = false := by rfl

theorem taking_all_six_is_win : wonByPrizes (prizesRemainingAfter 6 6) = true := by
  rfl

theorem taking_three_from_six_not_yet_win : wonByPrizes (prizesRemainingAfter 6 3) = false := by
  rfl

theorem two_ex_kos_not_enough : wonByPrizes (applyKO (applyKO 6 .ex) .ex) = false := by
  decide

theorem three_ex_kos_win :
    wonByPrizes (applyKO (applyKO (applyKO 6 .ex) .ex) .ex) = true := by
  decide

theorem two_vmax_kos_win :
    wonByPrizes (applyKO (applyKO 6 .vmax) .vmax) = true := by
  decide

-- ============================================================
-- §11  Theorems: trade favorability and ratios
-- ============================================================

theorem favorable_trade_definition_example : favorableTrade 2 1 = true := by rfl

theorem unfavorable_trade_example : favorableTrade 1 2 = false := by rfl

theorem nonlosing_trade_equal_case : nonLosingTrade 2 2 = true := by rfl

theorem strict_favorable_implies_nonlosing (taken given : Nat)
    (h : favorableTrade taken given = true) : nonLosingTrade taken given = true := by
  simp [favorableTrade, nonLosingTrade] at h ⊢
  exact Nat.le_of_lt h

theorem trade_ratio_records_pair : tradeRatio 2 1 = (2, 1) := by rfl

theorem ratio_two_over_one_better_than_two_over_two :
    ratioBetter 2 1 2 2 = true := by
  decide

theorem ratio_two_over_one_better_than_two_over_three :
    ratioBetter 2 1 2 3 = true := by
  decide

theorem ratio_three_over_one_better_than_two_over_one :
    ratioBetter 3 1 2 1 = true := by
  decide

theorem ratio_one_over_one_not_better_than_two_over_one :
    ratioBetter 1 1 2 1 = false := by
  decide

-- ============================================================
-- §12  Theorems: multi-prize attacker risk/reward
-- ============================================================

theorem single_prize_liability : prizesGivenOnKO .singlePrize = 1 := by rfl

theorem two_prize_liability : prizesGivenOnKO .twoPrize = 2 := by rfl

theorem three_prize_liability : prizesGivenOnKO .threePrize = 3 := by rfl

theorem multi_prize_has_higher_liability :
    prizesGivenOnKO .threePrize > prizesGivenOnKO .singlePrize := by
  decide

theorem three_prize_has_higher_hp : attackerHP .threePrize > attackerHP .singlePrize := by
  decide

theorem three_prize_has_higher_damage : attackerDamage .threePrize > attackerDamage .singlePrize := by
  decide

theorem multi_prize_risk_reward_tradeoff :
    prizesGivenOnKO .threePrize > prizesGivenOnKO .singlePrize ∧
    attackerDamage .threePrize > attackerDamage .singlePrize := by
  decide

theorem two_prize_also_outstats_single :
    attackerHP .twoPrize > attackerHP .singlePrize ∧
    attackerDamage .twoPrize > attackerDamage .singlePrize := by
  decide

-- ============================================================
-- §13  Theorems: prize denial and single-prize efficiency
-- ============================================================

theorem denial_score_single : prizeDenialScore .singlePrize = 3 := by rfl

theorem denial_score_two : prizeDenialScore .twoPrize = 2 := by rfl

theorem denial_score_three : prizeDenialScore .threePrize = 1 := by rfl

theorem single_has_best_denial_score :
    prizeDenialScore .singlePrize > prizeDenialScore .twoPrize ∧
    prizeDenialScore .twoPrize > prizeDenialScore .threePrize := by
  decide

theorem single_has_best_trade_ratio_vs_two_prize_targets :
    ratioBetter (prizesFromKO .ex) (prizesGivenOnKO .singlePrize)
                (prizesFromKO .ex) (prizesGivenOnKO .twoPrize) = true := by
  decide

theorem single_has_best_trade_ratio_vs_three_prize_targets :
    ratioBetter (prizesFromKO .vmax) (prizesGivenOnKO .singlePrize)
                (prizesFromKO .vmax) (prizesGivenOnKO .threePrize) = true := by
  decide

theorem single_prize_attackers_best_trade_ratio_statement :
    ratioBetter 2 1 2 2 = true ∧ ratioBetter 2 1 2 3 = true := by
  decide

-- ============================================================
-- §14  Theorems: mixed boards and 7-prize scenario
-- ============================================================

theorem mixed_board_six_total : totalBoardPrizes mixedBoardSixPrizes = 6 := by
  decide

theorem mixed_board_seven_total : totalBoardPrizes mixedBoardSevenPrizes = 7 := by
  decide

theorem mixed_board_eight_total : totalBoardPrizes mixedBoardEightPrizes = 8 := by
  decide

theorem seven_prize_game_exists_with_mix_of_one_and_two :
    totalBoardPrizes [.regular, .regular, .regular, .ex, .ex] = 7 := by
  decide

theorem seven_prize_board_has_enough_to_win :
    totalBoardPrizes mixedBoardSevenPrizes ≥ totalPrizesToWin := by
  decide

theorem six_prize_board_exactly_matches_goal :
    totalBoardPrizes mixedBoardSixPrizes = totalPrizesToWin := by
  decide

-- ============================================================
-- §15  Theorems: path to victory (minimum KOs)
-- ============================================================

theorem min_kos_vs_regular : minKOsForUniformTarget .regular = 6 := by
  decide

theorem min_kos_vs_ex : minKOsForUniformTarget .ex = 3 := by
  decide

theorem min_kos_vs_v : minKOsForUniformTarget .v = 3 := by
  decide

theorem min_kos_vs_vmax : minKOsForUniformTarget .vmax = 2 := by
  decide

theorem min_kos_vs_tag_team : minKOsForUniformTarget .tagTeam = 2 := by
  decide

theorem min_kos_vs_vstar : minKOsForUniformTarget .vstar = 3 := by
  decide

theorem higher_prize_targets_need_fewer_kos :
    minKOsForUniformTarget .vmax < minKOsForUniformTarget .ex ∧
    minKOsForUniformTarget .ex < minKOsForUniformTarget .regular := by
  decide

theorem minimum_kos_path_to_victory_examples :
    minKOsForUniformTarget .regular = 6 ∧
    minKOsForUniformTarget .ex = 3 ∧
    minKOsForUniformTarget .vmax = 2 := by
  decide

-- ============================================================
-- §16  Executable checks
-- ============================================================

#eval initialPrizeCount
#eval setupPrizeCount fullDeckSample
#eval prizesFromKO .ex
#eval prizesFromKO .vmax
#eval applyKO 6 .ex
#eval applyKO 6 .vmax
#eval wonByPrizes (applyKO (applyKO 6 .vmax) .vmax)
#eval favorableTrade 2 1
#eval tradeRatio 2 1
#eval ratioBetter 2 1 2 2
#eval prizeDenialScore .singlePrize
#eval totalBoardPrizes mixedBoardSevenPrizes
#eval minKOsForUniformTarget .regular
#eval minKOsForUniformTarget .ex
#eval minKOsForUniformTarget .vmax

end PokemonLean.Core.PrizeMapping
