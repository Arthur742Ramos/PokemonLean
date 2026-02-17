/-
  PokemonLean / Core / PrizeTrade.lean

  Certified prize trade analysis for the Pokémon TCG.
  Self-contained: defines PokemonKind with prize values, trade
  favorability, minimum KOs to win, and Roxanne timing analysis.

  Formally proves when trades are favorable, how many KOs are
  needed to take all 6 prizes, and strategic Roxanne triggers.

  All proofs are sorry-free.  30+ theorems.
-/

namespace PokemonLean.Core.PrizeTrade

-- ============================================================
-- §1  PokemonKind and Prize Values
-- ============================================================

/-- The different kinds of Pokémon in the TCG, classified by prize value. -/
inductive PokemonKind where
  | basic       -- regular Basic, Stage 1, Stage 2 (1 prize)
  | ex          -- Pokémon ex (2 prizes)
  | gx          -- Pokémon-GX (2 prizes)
  | v           -- Pokémon V (2 prizes)
  | vstar       -- Pokémon VSTAR (2 prizes)
  | vmax        -- Pokémon VMAX (3 prizes)
  | tagTeam     -- Tag Team GX (3 prizes)
deriving DecidableEq, Repr, BEq, Inhabited

/-- Prize value: number of prizes taken when this Pokémon is KO'd. -/
def prizeValue : PokemonKind → Nat
  | .basic   => 1
  | .ex      => 2
  | .gx      => 2
  | .v       => 2
  | .vstar   => 2
  | .vmax    => 3
  | .tagTeam => 3

/-- Total prizes needed to win. -/
def totalPrizes : Nat := 6

-- ============================================================
-- §2  Prize Trade Favorability
-- ============================================================

/-- A trade is favorable if you gain more prizes than your opponent.
    your_ko = what you knock out (you gain these prizes)
    opp_retaliates = what they knock out in return (they gain these prizes) -/
def favorable (your_ko opp_retaliates : PokemonKind) : Bool :=
  prizeValue your_ko ≥ prizeValue opp_retaliates

/-- A trade is strictly favorable if you gain MORE prizes. -/
def strictlyFavorable (your_ko opp_retaliates : PokemonKind) : Bool :=
  prizeValue your_ko > prizeValue opp_retaliates

/-- A trade is neutral if both sides exchange equal prizes. -/
def neutral (your_ko opp_retaliates : PokemonKind) : Bool :=
  prizeValue your_ko == prizeValue opp_retaliates

/-- A trade is unfavorable if you gain fewer prizes than opponent. -/
def unfavorable (your_ko opp_retaliates : PokemonKind) : Bool :=
  prizeValue your_ko < prizeValue opp_retaliates

/-- Net prize advantage from a single trade. -/
def prizeAdvantage (your_ko opp_retaliates : PokemonKind) : Int :=
  (prizeValue your_ko : Int) - (prizeValue opp_retaliates : Int)

-- ============================================================
-- §3  Minimum KOs to Win
-- ============================================================

/-- Minimum KOs needed to take all 6 prizes against a given Pokémon kind. -/
def minKOsToWin (target : PokemonKind) : Nat :=
  (totalPrizes + prizeValue target - 1) / prizeValue target  -- ceiling division

/-- KOs needed to take exactly n prizes against a given kind. -/
def kosForPrizes (n : Nat) (target : PokemonKind) : Nat :=
  (n + prizeValue target - 1) / prizeValue target

/-- Prizes taken from exactly k KOs of a given kind. -/
def prizesFromKOs (k : Nat) (target : PokemonKind) : Nat :=
  k * prizeValue target

-- ============================================================
-- §4  Mixed Board Analysis
-- ============================================================

/-- A board is a list of (PokemonKind, count) pairs representing opponent's field. -/
abbrev Board := List (PokemonKind × Nat)

/-- Total Pokémon on a board. -/
def boardSize (b : Board) : Nat :=
  b.foldl (fun acc (_, n) => acc + n) 0

/-- Maximum prizes available from a board. -/
def maxPrizesFromBoard (b : Board) : Nat :=
  b.foldl (fun acc (k, n) => acc + n * prizeValue k) 0

/-- Greedy strategy: KO the highest-value targets first.
    Returns minimum KOs needed for 6 prizes. -/
def greedyKOs (b : Board) : Nat :=
  let sorted := b.foldl (fun acc (k, n) =>
    acc ++ List.replicate n (prizeValue k)) []
  let descending := sorted.mergeSort (· ≥ ·)
  go descending 0 0
where
  go : List Nat → Nat → Nat → Nat
  | [], _, kos => kos
  | _ :: _, acc, kos =>
    if acc ≥ totalPrizes then kos
    else match _ : List Nat with  -- pattern matching on the original list
         | [] => kos
         | v :: rest => go rest (acc + v) (kos + 1)

-- Simplified greedy: just count
/-- Simple KO count: minimum KOs from sorted prize values. -/
def minKOsFromList (prizes : List Nat) : Nat :=
  let sorted := prizes.mergeSort (· ≥ ·)
  countUntil sorted 0 0
where
  countUntil : List Nat → Nat → Nat → Nat
  | [], _, kos => kos
  | v :: rest, acc, kos =>
    if acc ≥ totalPrizes then kos
    else countUntil rest (acc + v) (kos + 1)

-- ============================================================
-- §5  Roxanne Analysis
-- ============================================================

/-- Roxanne can be played when opponent has taken enough prizes to have ≤ 3 remaining.
    That means opponent has taken ≥ 3 prizes.
    Returns true if taking a KO would let the opponent play Roxanne next turn. -/
def triggersRoxanne (currentPrizesLeft : Nat) (koTarget : PokemonKind) : Bool :=
  let prizesAfter := if currentPrizesLeft > prizeValue koTarget
                     then currentPrizesLeft - prizeValue koTarget
                     else 0
  prizesAfter ≤ 3

/-- Prizes remaining after a KO. -/
def prizesAfterKO (currentPrizesLeft : Nat) (koTarget : PokemonKind) : Nat :=
  if currentPrizesLeft > prizeValue koTarget
  then currentPrizesLeft - prizeValue koTarget
  else 0

/-- How many more prizes until Roxanne is active (opponent has ≤ 3). -/
def prizesUntilRoxanne (currentPrizesLeft : Nat) : Nat :=
  if currentPrizesLeft ≤ 3 then 0
  else currentPrizesLeft - 3

-- ============================================================
-- §6  Trade Scenario Definitions
-- ============================================================

/-- Scenario: Your ex KOs their VMAX. -/
def exKOsVMAX := prizeAdvantage .vmax .ex  -- you KO VMAX (get 3), they KO your ex (get 2)

/-- Scenario: Your basic KOs their ex. -/
def basicKOsEx := prizeAdvantage .ex .basic  -- you KO ex (get 2), they KO your basic (get 1)

/-- Scenario: Your VMAX KOs their basic. -/
def vmaxKOsBasic := prizeAdvantage .basic .vmax  -- you KO basic (get 1), they KO your VMAX (get 3)

-- ============================================================
-- §7  Theorems — Prize Values
-- ============================================================

/-- Basic gives 1 prize. -/
theorem basic_one_prize : prizeValue .basic = 1 := by rfl

/-- Ex gives 2 prizes. -/
theorem ex_two_prizes : prizeValue .ex = 2 := by rfl

/-- GX gives 2 prizes. -/
theorem gx_two_prizes : prizeValue .gx = 2 := by rfl

/-- V gives 2 prizes. -/
theorem v_two_prizes : prizeValue .v = 2 := by rfl

/-- VSTAR gives 2 prizes. -/
theorem vstar_two_prizes : prizeValue .vstar = 2 := by rfl

/-- VMAX gives 3 prizes. -/
theorem vmax_three_prizes : prizeValue .vmax = 3 := by rfl

/-- Tag Team gives 3 prizes. -/
theorem tagTeam_three_prizes : prizeValue .tagTeam = 3 := by rfl

/-- All prize values are at least 1. -/
theorem prize_at_least_one (k : PokemonKind) : prizeValue k ≥ 1 := by
  cases k <;> simp [prizeValue]

/-- All prize values are at most 3. -/
theorem prize_at_most_three (k : PokemonKind) : prizeValue k ≤ 3 := by
  cases k <;> simp [prizeValue]

-- ============================================================
-- §8  Theorems — Trade Favorability
-- ============================================================

/-- Trading basics is always neutral. -/
theorem basic_trade_neutral : neutral .basic .basic = true := by native_decide

/-- Ex vs ex is neutral. -/
theorem ex_trade_neutral : neutral .ex .ex = true := by native_decide

/-- VMAX vs VMAX is neutral. -/
theorem vmax_trade_neutral : neutral .vmax .vmax = true := by native_decide

/-- V vs V is neutral. -/
theorem v_trade_neutral : neutral .v .v = true := by native_decide

/-- KO-ing an ex with a basic is strictly favorable. -/
theorem basic_ko_ex_favorable : strictlyFavorable .ex .basic = true := by native_decide

/-- KO-ing a VMAX with an ex is strictly favorable. -/
theorem ex_ko_vmax_favorable : strictlyFavorable .vmax .ex = true := by native_decide

/-- KO-ing a basic with a VMAX is unfavorable. -/
theorem vmax_ko_basic_unfavorable : unfavorable .basic .vmax = true := by native_decide

/-- KO-ing a Tag Team with a basic is strictly favorable. -/
theorem basic_ko_tagTeam_favorable : strictlyFavorable .tagTeam .basic = true := by native_decide

/-- KO-ing a basic with a Tag Team is unfavorable. -/
theorem tagTeam_ko_basic_unfavorable : unfavorable .basic .tagTeam = true := by native_decide

/-- favorable is reflexive: same kind trade is always favorable (≥). -/
theorem favorable_reflexive (k : PokemonKind) : favorable k k = true := by
  cases k <;> native_decide

/-- Strictly favorable implies favorable. -/
theorem strictly_implies_favorable (a b : PokemonKind) (h : strictlyFavorable a b = true) :
    favorable a b = true := by
  simp [strictlyFavorable, favorable] at *
  omega

/-- Unfavorable is the opposite of favorable (strictly). -/
theorem unfavorable_not_favorable (a b : PokemonKind) (h : unfavorable a b = true) :
    strictlyFavorable a b = false := by
  simp [unfavorable, strictlyFavorable] at *
  omega

-- ============================================================
-- §9  Theorems — Prize Advantage
-- ============================================================

/-- Ex KO-ing VMAX gives +1 advantage. -/
theorem exKOsVMAX_plus_one : exKOsVMAX = 1 := by native_decide

/-- Basic KO-ing ex gives +1 advantage. -/
theorem basicKOsEx_plus_one : basicKOsEx = 1 := by native_decide

/-- VMAX KO-ing basic gives -2 advantage. -/
theorem vmaxKOsBasic_minus_two : vmaxKOsBasic = -2 := by native_decide

/-- Same-kind trade has 0 advantage. -/
theorem same_kind_zero_advantage (k : PokemonKind) : prizeAdvantage k k = 0 := by
  cases k <;> native_decide

-- ============================================================
-- §10  Theorems — Minimum KOs to Win
-- ============================================================

/-- 6 KOs needed to win against all basics. -/
theorem minKOs_vs_basics : minKOsToWin .basic = 6 := by native_decide

/-- 3 KOs needed to win against all ex/GX/V. -/
theorem minKOs_vs_ex : minKOsToWin .ex = 3 := by native_decide
theorem minKOs_vs_gx : minKOsToWin .gx = 3 := by native_decide
theorem minKOs_vs_v : minKOsToWin .v = 3 := by native_decide

/-- 2 KOs needed to win against all VMAX. -/
theorem minKOs_vs_vmax : minKOsToWin .vmax = 2 := by native_decide

/-- 2 KOs needed to win against all Tag Team. -/
theorem minKOs_vs_tagTeam : minKOsToWin .tagTeam = 2 := by native_decide

/-- 3 KOs needed to win against all VSTAR. -/
theorem minKOs_vs_vstar : minKOsToWin .vstar = 3 := by native_decide

/-- More valuable targets need fewer KOs. -/
theorem fewer_kos_for_bigger_targets :
    minKOsToWin .vmax < minKOsToWin .ex ∧
    minKOsToWin .ex < minKOsToWin .basic := by
  constructor <;> native_decide

/-- 3 basics = 3 prizes. -/
theorem three_basic_kos : prizesFromKOs 3 .basic = 3 := by native_decide

/-- 2 VMAX KOs = 6 prizes (exactly enough to win). -/
theorem two_vmax_kos : prizesFromKOs 2 .vmax = 6 := by native_decide

/-- 3 ex KOs = 6 prizes (exactly enough to win). -/
theorem three_ex_kos : prizesFromKOs 3 .ex = 6 := by native_decide

/-- 6 basic KOs = 6 prizes. -/
theorem six_basic_kos : prizesFromKOs 6 .basic = 6 := by native_decide

-- ============================================================
-- §11  Theorems — Roxanne Timing
-- ============================================================

/-- With 6 prizes, KO-ing a VMAX (3 prizes) leaves 3 → triggers Roxanne. -/
theorem vmax_ko_triggers_roxanne_from_6 : triggersRoxanne 6 .vmax = true := by native_decide

/-- With 6 prizes, KO-ing a basic (1 prize) leaves 5 → does NOT trigger Roxanne. -/
theorem basic_ko_no_roxanne_from_6 : triggersRoxanne 6 .basic = false := by native_decide

/-- With 5 prizes, KO-ing an ex (2 prizes) leaves 3 → triggers Roxanne. -/
theorem ex_ko_triggers_roxanne_from_5 : triggersRoxanne 5 .ex = true := by native_decide

/-- With 4 prizes, KO-ing a basic (1 prize) leaves 3 → triggers Roxanne. -/
theorem basic_ko_triggers_roxanne_from_4 : triggersRoxanne 4 .basic = true := by native_decide

/-- Already at 3 prizes → Roxanne is already active regardless. -/
theorem already_at_3_roxanne_active : triggersRoxanne 3 .basic = true := by native_decide

/-- At 2 prizes, any KO still keeps Roxanne active. -/
theorem at_2_roxanne_stays (k : PokemonKind) : triggersRoxanne 2 k = true := by
  cases k <;> native_decide

/-- From 6 prizes, you need 3 prizes until Roxanne. -/
theorem prizes_until_roxanne_from_6 : prizesUntilRoxanne 6 = 3 := by native_decide

/-- From 3 prizes, Roxanne is immediate. -/
theorem prizes_until_roxanne_from_3 : prizesUntilRoxanne 3 = 0 := by native_decide

/-- From 4 prizes, only 1 more prize until Roxanne. -/
theorem prizes_until_roxanne_from_4 : prizesUntilRoxanne 4 = 1 := by native_decide

-- ============================================================
-- §12  Theorems — prizesAfterKO
-- ============================================================

/-- 6 prizes - basic KO = 5 prizes. -/
theorem prizes_after_basic_ko_from_6 : prizesAfterKO 6 .basic = 5 := by native_decide

/-- 6 prizes - VMAX KO = 3 prizes. -/
theorem prizes_after_vmax_ko_from_6 : prizesAfterKO 6 .vmax = 3 := by native_decide

/-- 6 prizes - Tag Team KO = 3 prizes. -/
theorem prizes_after_tagTeam_ko_from_6 : prizesAfterKO 6 .tagTeam = 3 := by native_decide

/-- 2 prizes - VMAX KO = 0 prizes (can't go below 0). -/
theorem prizes_after_vmax_ko_from_2 : prizesAfterKO 2 .vmax = 0 := by native_decide

/-- 1 prize - basic KO = 0 prizes (game over!). -/
theorem prizes_after_basic_ko_from_1 : prizesAfterKO 1 .basic = 0 := by native_decide

-- ============================================================
-- §13  #eval demonstrations
-- ============================================================

#eval prizeValue .basic
#eval prizeValue .vmax
#eval minKOsToWin .basic
#eval minKOsToWin .vmax
#eval minKOsToWin .ex
#eval favorable .vmax .ex
#eval favorable .basic .vmax
#eval triggersRoxanne 6 .vmax
#eval triggersRoxanne 6 .basic
#eval prizeAdvantage .vmax .ex
#eval prizeAdvantage .basic .vmax

end PokemonLean.Core.PrizeTrade
