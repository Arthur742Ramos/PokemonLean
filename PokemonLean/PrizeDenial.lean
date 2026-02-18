import PokemonLean.Basic

namespace PokemonLean.PrizeDenial

open PokemonLean

-- ============================================================================
-- PRIZE VALUE TYPES
-- ============================================================================

/-- Prize worth when a Pokemon is knocked out -/
inductive PrizeWorth where
  | one    -- basic, single-prize
  | two    -- ex, V, GX, VSTAR
  | three  -- VMAX, Tag Team
  deriving Repr, BEq, DecidableEq

def PrizeWorth.toNat : PrizeWorth → Nat
  | .one => 1
  | .two => 2
  | .three => 3

/-- Pokemon with prize denial relevance -/
structure DenialPokemon where
  card : Card
  prizeWorth : PrizeWorth
  canDenyPrizes : Bool   -- e.g., Roaring Moon ex with single prize ability
  deriving Repr, BEq, DecidableEq

/-- Prize state tracking -/
structure PrizeState where
  myPrizesLeft : Nat      -- opponent still needs to take
  oppPrizesLeft : Nat     -- I still need to take
  deriving Repr, BEq, DecidableEq

def initialPrizeState : PrizeState :=
  { myPrizesLeft := 6, oppPrizesLeft := 6 }

-- ============================================================================
-- PRIZE WORTH BASIC THEOREMS
-- ============================================================================

theorem one_prize_val : PrizeWorth.one.toNat = 1 := rfl
theorem two_prize_val : PrizeWorth.two.toNat = 2 := rfl
theorem three_prize_val : PrizeWorth.three.toNat = 3 := rfl

theorem prize_worth_pos (pw : PrizeWorth) : pw.toNat > 0 := by
  cases pw <;> decide

theorem prize_worth_le_three (pw : PrizeWorth) : pw.toNat ≤ 3 := by
  cases pw <;> decide

theorem prize_worth_ge_one (pw : PrizeWorth) : pw.toNat ≥ 1 := by
  cases pw <;> decide

theorem one_lt_two : PrizeWorth.one.toNat < PrizeWorth.two.toNat := by decide
theorem two_lt_three : PrizeWorth.two.toNat < PrizeWorth.three.toNat := by decide
theorem one_lt_three : PrizeWorth.one.toNat < PrizeWorth.three.toNat := by decide

-- ============================================================================
-- PRIZE MATH: KNOCKOUTS TO WIN
-- ============================================================================

/-- Minimum knockouts needed to take n prizes -/
def minKnockouts (prizesNeeded : Nat) (opponentWorth : PrizeWorth) : Nat :=
  (prizesNeeded + opponentWorth.toNat - 1) / opponentWorth.toNat

/-- Maximum knockouts needed (all single prize) -/
def maxKnockouts (prizesNeeded : Nat) : Nat := prizesNeeded

theorem min_knockouts_le_max_one (n : Nat) :
    minKnockouts n .one ≤ maxKnockouts n := by
  simp [minKnockouts, maxKnockouts, PrizeWorth.toNat]

theorem min_knockouts_le_max_two (n : Nat) :
    minKnockouts n .two ≤ maxKnockouts n := by
  simp [minKnockouts, maxKnockouts, PrizeWorth.toNat]
  suffices h : (n + 1) / 2 < n + 1 by omega
  apply Nat.div_lt_of_lt_mul; omega

theorem min_knockouts_le_max_three (n : Nat) :
    minKnockouts n .three ≤ maxKnockouts n := by
  simp [minKnockouts, maxKnockouts, PrizeWorth.toNat]
  suffices h : (n + 2) / 3 < n + 1 by omega
  apply Nat.div_lt_of_lt_mul; omega

theorem min_knockouts_one_prize (n : Nat) :
    minKnockouts n .one = n := by
  simp [minKnockouts, PrizeWorth.toNat]

theorem min_knockouts_two_prize_six : minKnockouts 6 .two = 3 := rfl

theorem min_knockouts_three_prize_six : minKnockouts 6 .three = 2 := rfl

theorem min_knockouts_two_prize_five : minKnockouts 5 .two = 3 := rfl

theorem min_knockouts_three_prize_three : minKnockouts 3 .three = 1 := rfl

theorem max_knockouts_six : maxKnockouts 6 = 6 := rfl

-- ============================================================================
-- PRIZE TRADE ANALYSIS
-- ============================================================================

/-- A prize trade: attacker takes prizes, then gets KO'd giving prizes -/
structure PrizeTrade where
  prizesGained : Nat      -- prizes attacker takes
  prizesGiven : Nat       -- prizes given up when KO'd
  deriving Repr, BEq, DecidableEq

/-- Net prize advantage of a trade -/
def tradeAdvantage (trade : PrizeTrade) : Int :=
  (trade.prizesGained : Int) - (trade.prizesGiven : Int)

/-- A trade is favorable if you gain more than you give -/
def isFavorableTrade (trade : PrizeTrade) : Bool :=
  decide (trade.prizesGained > trade.prizesGiven)

/-- A trade is even -/
def isEvenTrade (trade : PrizeTrade) : Bool :=
  trade.prizesGained == trade.prizesGiven

/-- A trade is unfavorable -/
def isUnfavorableTrade (trade : PrizeTrade) : Bool :=
  decide (trade.prizesGained < trade.prizesGiven)

theorem favorable_positive (t : PrizeTrade) (h : isFavorableTrade t = true) :
    tradeAdvantage t > 0 := by
  simp [isFavorableTrade] at h
  simp [tradeAdvantage]
  omega

theorem even_trade_zero (t : PrizeTrade) (h : isEvenTrade t = true) :
    tradeAdvantage t = 0 := by
  simp [isEvenTrade] at h
  simp [tradeAdvantage]
  omega

theorem unfavorable_negative (t : PrizeTrade) (h : isUnfavorableTrade t = true) :
    tradeAdvantage t < 0 := by
  simp [isUnfavorableTrade] at h
  simp [tradeAdvantage]
  omega

theorem trade_trichotomy (t : PrizeTrade) :
    isFavorableTrade t = true ∨ isEvenTrade t = true ∨ isUnfavorableTrade t = true := by
  simp [isFavorableTrade, isEvenTrade, isUnfavorableTrade]
  omega

-- ============================================================================
-- SINGLE PRIZE ATTACKER STRATEGY
-- ============================================================================

/-- Single-prize attackers force opponent to take 6 KOs -/
def singlePrizeKOsNeeded : Nat := 6

/-- Multi-prize attackers allow faster wins -/
def multiPrizeKOsNeeded (worth : PrizeWorth) : Nat :=
  minKnockouts 6 worth

theorem single_prize_needs_six : singlePrizeKOsNeeded = 6 := rfl

theorem two_prize_needs_three : multiPrizeKOsNeeded .two = 3 := rfl

theorem three_prize_needs_two : multiPrizeKOsNeeded .three = 2 := rfl

/-- Single prize attackers always need more KOs than multi-prize -/
theorem single_needs_more_kos_than_two :
    singlePrizeKOsNeeded > multiPrizeKOsNeeded .two := by decide

theorem single_needs_more_kos_than_three :
    singlePrizeKOsNeeded > multiPrizeKOsNeeded .three := by decide

-- ============================================================================
-- PRIZE DENIAL: REDUCING OPPONENT'S PRIZE GAIN
-- ============================================================================

/-- Prize denial methods -/
inductive DenialMethod where
  | singlePrizeAttacker     -- use single prize Pokemon
  | scoop                   -- pick up damaged Pokemon
  | healToSurvive           -- heal to prevent KO
  | benchProtection         -- prevent bench snipe KOs
  | sacrificeLowValue       -- sacrifice 1-prizer instead of 2/3
  deriving Repr, BEq, DecidableEq

/-- Prizes denied by a method (compared to worst case) -/
def prizesDenied (method : DenialMethod) (worstCasePrizes : Nat) : Nat :=
  match method with
  | .singlePrizeAttacker => if worstCasePrizes > 1 then worstCasePrizes - 1 else 0
  | .scoop => worstCasePrizes
  | .healToSurvive => worstCasePrizes
  | .benchProtection => worstCasePrizes
  | .sacrificeLowValue => if worstCasePrizes > 1 then worstCasePrizes - 1 else 0

theorem scoop_denies_all (n : Nat) :
    prizesDenied .scoop n = n := rfl

theorem heal_denies_all (n : Nat) :
    prizesDenied .healToSurvive n = n := rfl

theorem bench_protection_denies_all (n : Nat) :
    prizesDenied .benchProtection n = n := rfl

theorem single_prize_denies_some (n : Nat) (h : n > 1) :
    prizesDenied .singlePrizeAttacker n = n - 1 := by
  simp [prizesDenied, h]

theorem sacrifice_denies_some (n : Nat) (h : n > 1) :
    prizesDenied .sacrificeLowValue n = n - 1 := by
  simp [prizesDenied, h]

theorem denial_le_worst_case (method : DenialMethod) (n : Nat) :
    prizesDenied method n ≤ n := by
  cases method <;> simp [prizesDenied] <;> split <;> omega

-- ============================================================================
-- PRIZE RACE MODEL
-- ============================================================================

/-- A prize race tracks both players' progress -/
structure PrizeRace where
  myPrizesRemaining : Nat
  oppPrizesRemaining : Nat
  myTurnNext : Bool
  deriving Repr, BEq, DecidableEq

/-- Who is ahead in the prize race -/
def raceLeader (race : PrizeRace) : Int :=
  (race.oppPrizesRemaining : Int) - (race.myPrizesRemaining : Int)

/-- Am I ahead? (fewer prizes remaining = ahead) -/
def amAhead (race : PrizeRace) : Bool :=
  decide (race.myPrizesRemaining < race.oppPrizesRemaining)

/-- Is the race tied? -/
def raceTied (race : PrizeRace) : Bool :=
  race.myPrizesRemaining == race.oppPrizesRemaining

def initialRace : PrizeRace :=
  { myPrizesRemaining := 6, oppPrizesRemaining := 6, myTurnNext := true }

theorem initial_race_tied : raceTied initialRace = true := rfl

theorem initial_leader_zero : raceLeader initialRace = 0 := rfl

theorem ahead_positive_leader (race : PrizeRace) (h : amAhead race = true) :
    raceLeader race > 0 := by
  simp [amAhead] at h
  simp [raceLeader]
  omega

theorem tied_zero_leader (race : PrizeRace) (h : raceTied race = true) :
    raceLeader race = 0 := by
  simp [raceTied] at h
  simp [raceLeader]
  omega

-- ============================================================================
-- PRIZE MAP: WHICH CARDS ARE PRIZED
-- ============================================================================

/-- Tracking what's in prizes -/
structure PrizeMap where
  totalPrizes : Nat
  keyCardsPrized : Nat    -- how many key cards are stuck in prizes
  energyPrized : Nat
  supportersPrized : Nat
  deriving Repr, BEq, DecidableEq

/-- How bad is the prize situation -/
def prizeMapSeverity (pm : PrizeMap) : Nat :=
  pm.keyCardsPrized * 3 + pm.energyPrized + pm.supportersPrized

/-- Percentage of prizes that are key cards -/
def keyCardPrizeRate (pm : PrizeMap) : Nat :=
  if pm.totalPrizes > 0 then (pm.keyCardsPrized * 100) / pm.totalPrizes else 0

theorem severity_zero_no_key_cards :
    prizeMapSeverity { totalPrizes := 6, keyCardsPrized := 0, energyPrized := 0, supportersPrized := 0 } = 0 := rfl

theorem severity_increases_with_key_cards (e s : Nat) (a b : Nat) (h : a < b) :
    prizeMapSeverity { totalPrizes := 6, keyCardsPrized := a, energyPrized := e, supportersPrized := s } <
    prizeMapSeverity { totalPrizes := 6, keyCardsPrized := b, energyPrized := e, supportersPrized := s } := by
  simp [prizeMapSeverity]
  omega

-- ============================================================================
-- KO EFFICIENCY
-- ============================================================================

/-- KO efficiency: prizes gained per knockout -/
def koEfficiency (prizesGained kos : Nat) : Nat :=
  if kos > 0 then prizesGained / kos else 0

/-- Average prize worth of your attackers getting KO'd -/
def avgPrizeGiven (totalPrizesGiven totalKOsSuffered : Nat) : Nat :=
  if totalKOsSuffered > 0 then totalPrizesGiven / totalKOsSuffered else 0

theorem ko_efficiency_le_gained (gained kos : Nat) :
    koEfficiency gained kos ≤ gained := by
  simp [koEfficiency]
  split
  · exact Nat.div_le_self _ _
  · exact Nat.zero_le _

theorem ko_efficiency_zero_no_kos (n : Nat) :
    koEfficiency n 0 = 0 := rfl

-- ============================================================================
-- BOSS + KO PRIZE CALCULATIONS
-- ============================================================================

/-- Prizes from a boss orders + KO play -/
def bossKOPrizes (targetWorth : PrizeWorth) : Nat :=
  targetWorth.toNat

/-- Is bossing this target worth it compared to active KO -/
def bossWorthIt (activeWorth targetWorth : PrizeWorth) : Bool :=
  decide (targetWorth.toNat ≥ activeWorth.toNat)

theorem boss_vmax_worth_three : bossKOPrizes .three = 3 := rfl

theorem boss_ex_worth_two : bossKOPrizes .two = 2 := rfl

theorem boss_basic_worth_one : bossKOPrizes .one = 1 := rfl

theorem boss_higher_always_worth (low high : PrizeWorth) (h : low.toNat ≤ high.toNat) :
    bossWorthIt low high = true := by
  simp [bossWorthIt]
  omega

theorem boss_vmax_over_basic : bossWorthIt .one .three = true := by decide

theorem boss_ex_over_basic : bossWorthIt .one .two = true := by decide

theorem boss_basic_not_over_vmax : bossWorthIt .three .one = false := by decide

-- ============================================================================
-- GAME-WINNING KO ANALYSIS
-- ============================================================================

/-- Can this KO win the game? -/
def isGameWinningKO (prizesRemaining : Nat) (targetWorth : PrizeWorth) : Bool :=
  decide (targetWorth.toNat ≥ prizesRemaining)

theorem game_winning_last_prize :
    isGameWinningKO 1 .one = true := rfl

theorem game_winning_ex_from_two :
    isGameWinningKO 2 .two = true := rfl

theorem game_winning_vmax_from_three :
    isGameWinningKO 3 .three = true := rfl

theorem not_game_winning_basic_from_two :
    isGameWinningKO 2 .one = false := rfl

theorem not_game_winning_ex_from_three :
    isGameWinningKO 3 .two = false := rfl

theorem game_winning_vmax_from_two :
    isGameWinningKO 2 .three = true := rfl

theorem game_winning_vmax_from_one :
    isGameWinningKO 1 .three = true := rfl

/-- If a KO wins with n prizes, it wins with fewer too -/
theorem game_winning_monotone (n m : Nat) (pw : PrizeWorth)
    (h1 : isGameWinningKO n pw = true) (h2 : m ≤ n) :
    isGameWinningKO m pw = true := by
  simp [isGameWinningKO] at *
  omega

-- ============================================================================
-- TOTAL PRIZE EXCHANGE MODEL
-- ============================================================================

/-- Total prizes exchanged in a game -/
structure PrizeExchange where
  myPrizesTaken : Nat
  oppPrizesTaken : Nat
  myKOs : Nat
  oppKOs : Nat
  deriving Repr, BEq, DecidableEq

/-- I win if I've taken all 6 prizes -/
def iWin (pe : PrizeExchange) : Bool :=
  decide (pe.myPrizesTaken ≥ 6)

/-- Opponent wins if they've taken all 6 -/
def oppWins (pe : PrizeExchange) : Bool :=
  decide (pe.oppPrizesTaken ≥ 6)

/-- Prize efficiency ratio (my prizes per KO suffered) -/
def myEfficiency (pe : PrizeExchange) : Nat :=
  koEfficiency pe.myPrizesTaken pe.myKOs

theorem i_win_at_six : iWin { myPrizesTaken := 6, oppPrizesTaken := 0, myKOs := 3, oppKOs := 0 } = true := rfl

theorem opp_wins_at_six : oppWins { myPrizesTaken := 0, oppPrizesTaken := 6, myKOs := 0, oppKOs := 3 } = true := rfl

theorem not_win_at_five : iWin { myPrizesTaken := 5, oppPrizesTaken := 0, myKOs := 3, oppKOs := 0 } = false := rfl

-- ============================================================================
-- PRIZE DENIAL SCORE
-- ============================================================================

/-- Overall prize denial effectiveness -/
def denialScore (oppKOs oppPrizesTaken : Nat) : Nat :=
  if oppKOs > 0 then
    let avgPrize := oppPrizesTaken / oppKOs
    if avgPrize ≤ 1 then 10
    else if avgPrize ≤ 2 then 5
    else 0
  else 10  -- no KOs = perfect denial

theorem perfect_denial_no_kos :
    denialScore 0 0 = 10 := rfl

theorem good_denial_single_prize :
    denialScore 6 6 = 10 := rfl

theorem ok_denial_two_prize :
    denialScore 3 6 = 5 := rfl

theorem bad_denial_three_prize :
    denialScore 2 6 = 0 := rfl

end PokemonLean.PrizeDenial
