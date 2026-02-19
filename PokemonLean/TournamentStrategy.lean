/-
  PokemonLean / TournamentStrategy.lean

  Formalization of Best-of-3 tournament strategy, Swiss tournament math,
  ELO scoring, deck selection, and sideboarding.

  All proofs are kernel-verified via `native_decide` on concrete rational
  values, following the project convention (no Mathlib dependency).
-/
import PokemonLean.NashEquilibrium
import PokemonLean.Core.Types
import PokemonLean.RealMetagame

namespace PokemonLean.TournamentStrategy

open PokemonLean.NashEquilibrium (Rat sumFin)

/-! ## 1. Bo1 Win Rate Matrix -/

/-- Win rate of deck `i` vs deck `j` in a single game. -/
abbrev Bo1WinRate (n : Nat) := Fin n → Fin n → Rat

/-! ## 2. Bo3 Win Rate -/

/-- Bo3 win probability from a per-game win rate `p`.
    Winner must win 2 out of 3:
    P(2-0) = p²
    P(2-1) = 2 · p² · (1 - p)   (lose exactly one of first two, win third)
    Total  = p² · (3 - 2p)
-/
def bo3WinProb (p : Rat) : Rat :=
  p * p * (3 - 2 * p)

/-- Bo3 win rate derived from a Bo1 matchup matrix. -/
def Bo3WinRate {n : Nat} (w : Bo1WinRate n) (i j : Fin n) : Rat :=
  bo3WinProb (w i j)

/-! ## 3. BO3_AMPLIFIES_ADVANTAGE -/

/-- The favored rates: those strictly above 1/2 (5% steps). -/
def favoredRates : List Rat :=
  [11/20, 12/20, 13/20, 14/20, 15/20, 16/20, 17/20, 18/20, 19/20]

/-- If Bo1 win rate p > 1/2, then Bo3 win rate > Bo1 win rate.
    Verified on a grid of rational values. -/
theorem BO3_AMPLIFIES_ADVANTAGE :
    ∀ p ∈ favoredRates, bo3WinProb p > p := by native_decide

/-- Also verify at finer granularity: 51% through 99%. -/
def favoredPercents : List Rat :=
  [51/100, 52/100, 53/100, 54/100, 55/100, 56/100, 57/100, 58/100, 59/100,
   60/100, 61/100, 62/100, 63/100, 64/100, 65/100, 66/100, 67/100, 68/100, 69/100,
   70/100, 71/100, 72/100, 73/100, 74/100, 75/100, 76/100, 77/100, 78/100, 79/100,
   80/100, 81/100, 82/100, 83/100, 84/100, 85/100, 86/100, 87/100, 88/100, 89/100,
   90/100, 91/100, 92/100, 93/100, 94/100, 95/100, 96/100, 97/100, 98/100, 99/100]

theorem BO3_AMPLIFIES_ADVANTAGE_FINE :
    ∀ p ∈ favoredPercents, bo3WinProb p > p := by native_decide

/-- Conversely, if p < 1/2, Bo3 makes it even harder (lower win rate). -/
def unfavoredRates : List Rat :=
  [1/20, 2/20, 3/20, 4/20, 5/20, 6/20, 7/20, 8/20, 9/20]

theorem BO3_AMPLIFIES_DISADVANTAGE :
    ∀ p ∈ unfavoredRates, bo3WinProb p < p := by native_decide

/-! ## 4. BO3_SYMMETRIC -/

/-- If Bo1 win rate is exactly 1/2, then Bo3 win rate is also 1/2. -/
theorem BO3_SYMMETRIC : bo3WinProb (1 / 2) = 1 / 2 := by native_decide

/-! ## 5. Sideboard Strategy -/

/-- A sideboard strategy modifies the matchup matrix for games 2 and 3.
    `pre` is the game-1 matchup, `post` is the post-sideboard matchup. -/
structure SideboardStrategy (n : Nat) where
  pre  : Bo1WinRate n
  post : Bo1WinRate n

/-- Bo3 win rate with sideboarding: game 1 uses `pre`, games 2-3 use `post`.
    P(win Bo3) = P(W1)·P(W2) + P(W1)·P(L2)·P(W3) + P(L1)·P(W2)·P(W3)
    where W1 uses pre rate p, W2/W3 use post rate q. -/
def bo3SideboardWinProb (p q : Rat) : Rat :=
  p * q + p * (1 - q) * q + (1 - p) * q * q

def Bo3SideboardWinRate {n : Nat} (sb : SideboardStrategy n) (i j : Fin n) : Rat :=
  bo3SideboardWinProb (sb.pre i j) (sb.post i j)

/-! ## 6. SIDEBOARD_VALUE -/

/-- Without sideboarding at 40% (2/5), the Bo3 rate is 44/125 = 35.2%. -/
theorem bo3_no_sideboard_40 :
    bo3WinProb (2 / 5) = 44 / 125 := by native_decide

/-- With sideboarding: pre=40%, post=50%, the Bo3 rate is 9/20 = 45%. -/
theorem SIDEBOARD_VALUE :
    bo3SideboardWinProb (2 / 5) (1 / 2) = 9 / 20 := by native_decide

/-- Sideboarding from 40%→50% improves Bo3 win rate by 49/500 ≈ 9.8%. -/
theorem SIDEBOARD_IMPROVEMENT :
    bo3SideboardWinProb (2 / 5) (1 / 2) - bo3WinProb (2 / 5) = 49 / 500 := by native_decide

/-- The improvement is strictly positive. -/
theorem SIDEBOARD_POSITIVE :
    bo3SideboardWinProb (2 / 5) (1 / 2) > bo3WinProb (2 / 5) := by native_decide

/-! ## 7. Swiss Tournament — Binomial Distribution of Records -/

/-- Binomial coefficient. -/
def binom : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-- Basic binomial identities. -/
theorem binom_zero_right (n : Nat) : binom n 0 = 1 := by
  cases n <;> simp [binom]

theorem binom_8_8 : binom 8 8 = 1 := by native_decide
theorem binom_8_1 : binom 8 1 = 8 := by native_decide

/-- Pascal's identity verified concretely. -/
theorem pascal_8_3 : binom 8 3 = binom 7 2 + binom 7 3 := by native_decide

/-- Swiss tournament structure. -/
structure SwissTournament where
  rounds   : Nat
  players  : Nat
  isPowerOfTwo : players = 2 ^ rounds

/-- 256-player Swiss has 8 rounds. -/
def swiss256 : SwissTournament := ⟨8, 256, by native_decide⟩

/-- Full distribution after 8 rounds: row of Pascal's triangle. -/
theorem swiss_distribution_8 :
    (List.range 9).map (binom 8) = [1, 8, 28, 56, 70, 56, 28, 8, 1] := by native_decide

/-- Sum of all records = total players (binomial theorem: (1+1)^8 = 256). -/
theorem swiss_sum_256 :
    ((List.range 9).map (binom 8)).foldl (· + ·) 0 = 256 := by native_decide

/-! ## 8. BUBBLE_MATH — 8-round Swiss with 256 players -/

/-- In an 8-round Swiss with 256 players:
    - 8-0: binom(8,8) = 1 player
    - 7-1: binom(8,7) = 8 players
    - 6-2: binom(8,6) = 28 players
    Standard TCG top-cut is top 32, so 1 + 8 + 28 = 37 players
    are at 6-2 or better. Only 37 - 32 = 5 of the 6-2s miss on breakers. -/

theorem BUBBLE_MATH_8_0 : binom 8 8 = 1 := by native_decide
theorem BUBBLE_MATH_7_1 : binom 8 7 = 8 := by native_decide
theorem BUBBLE_MATH_6_2 : binom 8 6 = 28 := by native_decide

/-- Total X-2 or better = 37. -/
theorem BUBBLE_MATH_TOP :
    binom 8 8 + binom 8 7 + binom 8 6 = 37 := by native_decide

/-- With top-32 cut, exactly 5 of the 28 X-2 players miss on breakers. -/
theorem BUBBLE_MATH_MISS :
    binom 8 8 + binom 8 7 + binom 8 6 - 32 = 5 := by native_decide

/-- 23 of 28 X-2 players make top cut. -/
theorem BUBBLE_MATH_MAKE :
    32 - binom 8 8 - binom 8 7 = 23 := by native_decide

/-- Symmetry: binom(8,6) = binom(8,2). -/
theorem binom_symmetry_8 : binom 8 6 = binom 8 2 := by native_decide

/-! ## 9. ELO Update — Proper Scoring Rule -/

/-- ELO update: newRating = oldRating + K · (S - E)
    where S is actual score (1 for win, 0 for loss), E is expected score. -/
def eloUpdate (rating K S E : Rat) : Rat :=
  rating + K * (S - E)

/-- When actual score equals expected score, ELO doesn't change. -/
theorem ELO_ZERO_CHANGE :
    eloUpdate 1500 32 (1/2) (1/2) = 1500 := by native_decide

/-- Expected ELO change when playing at true skill:
    E · K · (1 - E) + (1 - E) · K · (0 - E)
    This should be 0 for any E (proper scoring rule). -/
def expectedEloChange (K E : Rat) : Rat :=
  E * (K * (1 - E)) + (1 - E) * (K * (0 - E))

/-- Verified at multiple expected scores. -/
theorem ELO_PROPER_SCORING_50 : expectedEloChange 32 (1/2) = 0 := by native_decide
theorem ELO_PROPER_SCORING_60 : expectedEloChange 32 (3/5) = 0 := by native_decide
theorem ELO_PROPER_SCORING_75 : expectedEloChange 32 (3/4) = 0 := by native_decide
theorem ELO_PROPER_SCORING_30 : expectedEloChange 32 (3/10) = 0 := by native_decide
theorem ELO_PROPER_SCORING_90 : expectedEloChange 32 (9/10) = 0 := by native_decide

/-- Verified at all grid points for multiple K values. -/
def eloGrid : List Rat :=
  [1/10, 2/10, 3/10, 4/10, 5/10, 6/10, 7/10, 8/10, 9/10]

theorem ELO_PROPER_SCORING_ALL :
    ∀ E ∈ eloGrid, expectedEloChange 32 E = 0 := by native_decide

def kValues : List Rat := [16, 32, 64]

theorem ELO_PROPER_K_INDEPENDENT :
    ∀ K ∈ kValues, ∀ E ∈ eloGrid, expectedEloChange K E = 0 := by native_decide

/-- For equal players (E = 1/2), win gives +K/2 and loss gives -K/2. -/
theorem ELO_WIN_DELTA : eloUpdate 1500 32 1 (1/2) = 1516 := by native_decide
theorem ELO_LOSS_DELTA : eloUpdate 1500 32 0 (1/2) = 1484 := by native_decide

/-! ## 10. VARIANCE_REDUCTION — Bo3 has lower variance than Bo1 -/

/-- Variance of a Bernoulli(p) variable: p(1-p). -/
def bernoulliVar (p : Rat) : Rat := p * (1 - p)

/-- Bo3 outcome variance: bernoulliVar(bo3WinProb(p)). -/
def bo3Var (p : Rat) : Rat := bernoulliVar (bo3WinProb p)

/-- At p = 1/2, both variances are equal. -/
theorem VARIANCE_EQUAL_AT_HALF :
    bo3Var (1/2) = bernoulliVar (1/2) := by native_decide

/-- For any non-50% matchup, Bo3 has strictly lower variance.
    Verified on a grid from 5% to 95% in steps of 5%, excluding 50%. -/
def nonHalfRates : List Rat :=
  [1/20, 2/20, 3/20, 4/20, 5/20, 6/20, 7/20, 8/20, 9/20,
   11/20, 12/20, 13/20, 14/20, 15/20, 16/20, 17/20, 18/20, 19/20]

theorem VARIANCE_REDUCTION :
    ∀ p ∈ nonHalfRates, bo3Var p < bernoulliVar p := by native_decide

/-- Finer verification: every percentage point from 1% to 99% except 50%. -/
def nonHalfPercents : List Rat :=
  [1/100, 2/100, 3/100, 4/100, 5/100, 6/100, 7/100, 8/100, 9/100,
   10/100, 11/100, 12/100, 13/100, 14/100, 15/100, 16/100, 17/100, 18/100, 19/100,
   20/100, 21/100, 22/100, 23/100, 24/100, 25/100, 26/100, 27/100, 28/100, 29/100,
   30/100, 31/100, 32/100, 33/100, 34/100, 35/100, 36/100, 37/100, 38/100, 39/100,
   40/100, 41/100, 42/100, 43/100, 44/100, 45/100, 46/100, 47/100, 48/100, 49/100,
   51/100, 52/100, 53/100, 54/100, 55/100, 56/100, 57/100, 58/100, 59/100,
   60/100, 61/100, 62/100, 63/100, 64/100, 65/100, 66/100, 67/100, 68/100, 69/100,
   70/100, 71/100, 72/100, 73/100, 74/100, 75/100, 76/100, 77/100, 78/100, 79/100,
   80/100, 81/100, 82/100, 83/100, 84/100, 85/100, 86/100, 87/100, 88/100, 89/100,
   90/100, 91/100, 92/100, 93/100, 94/100, 95/100, 96/100, 97/100, 98/100, 99/100]

theorem VARIANCE_REDUCTION_FINE :
    ∀ p ∈ nonHalfPercents, bo3Var p < bernoulliVar p := by native_decide

/-- Concrete example: at 60% Bo1, variance drops significantly. -/
theorem VARIANCE_60_BO1 : bernoulliVar (3/5) = 6/25 := by native_decide
theorem VARIANCE_60_BO3 : bo3Var (3/5) = 3564/15625 := by native_decide
theorem VARIANCE_60_REDUCTION : bo3Var (3/5) < bernoulliVar (3/5) := by native_decide

/-! ## 11. Real Trainer Hill metagame applications -/

def natToRat (n : Nat) : Rat := ((n : Int) : Rat)

def perThousandToRat (n : Nat) : Rat := natToRat n / 1000

def grimmVsDragapultBo1 : Rat :=
  perThousandToRat (PokemonLean.RealMetagame.matchupWR
    .GrimssnarlFroslass .DragapultDusknoir)

def ragingBoltVsMegaAbsolBo1 : Rat :=
  perThousandToRat (PokemonLean.RealMetagame.matchupWR
    .RagingBoltOgerpon .MegaAbsolBox)

def gardevoirVsDragapultBo1 : Rat :=
  perThousandToRat (PokemonLean.RealMetagame.matchupWR
    .Gardevoir .DragapultDusknoir)

theorem BO3_GRIMMSNARL_VS_DRAGAPULT_RATE :
    bo3WinProb grimmVsDragapultBo1 = 1186042 / 1953125 := by native_decide

theorem BO3_GRIMMSNARL_VS_DRAGAPULT_AMPLIFIES :
    bo3WinProb grimmVsDragapultBo1 > grimmVsDragapultBo1 ∧
    bo3WinProb grimmVsDragapultBo1 > 3 / 5 := by native_decide

theorem BO3_RAGING_BOLT_VS_MEGA_ABSOL_RATE :
    bo3WinProb ragingBoltVsMegaAbsolBo1 = 374572283 / 500000000 := by native_decide

theorem BO3_RAGING_BOLT_VS_MEGA_ABSOL_AMPLIFIES :
    bo3WinProb ragingBoltVsMegaAbsolBo1 > ragingBoltVsMegaAbsolBo1 ∧
    bo3WinProb ragingBoltVsMegaAbsolBo1 > 7 / 10 := by native_decide

theorem BO3_GARDEVOIR_VS_DRAGAPULT_RATE :
    bo3WinProb gardevoirVsDragapultBo1 = 343201617 / 500000000 := by native_decide

theorem BO3_GARDEVOIR_VS_DRAGAPULT_AMPLIFIES :
    bo3WinProb gardevoirVsDragapultBo1 > gardevoirVsDragapultBo1 ∧
    bo3WinProb gardevoirVsDragapultBo1 > 17 / 25 := by native_decide

def top14ShareTotal : Nat :=
  (PokemonLean.RealMetagame.Deck.all.map PokemonLean.RealMetagame.metaShare).foldl (· + ·) 0

def swissMatchupProbTop14 (d : PokemonLean.RealMetagame.Deck) : Rat :=
  natToRat (PokemonLean.RealMetagame.metaShare d) / natToRat top14ShareTotal

def expectedSwissMatchupsIn8 (d : PokemonLean.RealMetagame.Deck) : Rat :=
  8 * swissMatchupProbTop14 d

theorem SWISS_TOP14_SHARE_TOTAL : top14ShareTotal = 695 := by native_decide

theorem SWISS_TOP14_MATCHUP_DISTRIBUTION :
    (PokemonLean.RealMetagame.Deck.all.map swissMatchupProbTop14).foldl (· + ·) 0 = 1 := by
  native_decide

theorem SWISS_TOP14_EXPECTED_MATCHUPS_SUM :
    (PokemonLean.RealMetagame.Deck.all.map expectedSwissMatchupsIn8).foldl (· + ·) 0 = 8 := by
  native_decide

theorem SWISS_TOP14_EXPECTED_DRAGAPULT_IN_8 :
    expectedSwissMatchupsIn8 PokemonLean.RealMetagame.Deck.DragapultDusknoir = 248 / 139 := by
  native_decide

def gardevoirDragapultReadValue : Rat :=
  perThousandToRat (PokemonLean.RealMetagame.metaShare .DragapultDusknoir) * gardevoirVsDragapultBo1

theorem GARDEVOIR_METAGAME_READ_VALUE :
    gardevoirDragapultReadValue = 97185 / 1000000 := by native_decide

def top6Decks : List PokemonLean.RealMetagame.Deck :=
  [.DragapultDusknoir, .GholdengoLunatone, .GrimssnarlFroslass,
   .MegaAbsolBox, .Gardevoir, .CharizardNoctowl]

def weightedWinRateNumerator (d : PokemonLean.RealMetagame.Deck) : Nat :=
  (PokemonLean.RealMetagame.Deck.all.map
    (fun opp => PokemonLean.RealMetagame.metaShare opp * PokemonLean.RealMetagame.matchupWR d opp)).foldl
    (· + ·) 0

def expectedWinRateVsField (d : PokemonLean.RealMetagame.Deck) : Rat :=
  natToRat (weightedWinRateNumerator d) / natToRat (top14ShareTotal * 1000)

theorem EXPECTED_WR_DRAGAPULT_VS_FIELD :
    expectedWinRateVsField .DragapultDusknoir = 324243 / 695000 := by native_decide

theorem EXPECTED_WR_GHOLDENGO_VS_FIELD :
    expectedWinRateVsField .GholdengoLunatone = 332140 / 695000 := by native_decide

theorem EXPECTED_WR_GRIMMSNARL_VS_FIELD :
    expectedWinRateVsField .GrimssnarlFroslass = 366061 / 695000 := by native_decide

theorem EXPECTED_WR_MEGA_ABSOL_VS_FIELD :
    expectedWinRateVsField .MegaAbsolBox = 359377 / 695000 := by native_decide

theorem EXPECTED_WR_GARDEVOIR_VS_FIELD :
    expectedWinRateVsField .Gardevoir = 346552 / 695000 := by native_decide

theorem EXPECTED_WR_CHARIZARD_NOCTOWL_VS_FIELD :
    expectedWinRateVsField .CharizardNoctowl = 317721 / 695000 := by native_decide

theorem GRIMMSNARL_HIGHEST_EXPECTED_WR_VS_FIELD :
    ∀ d ∈ top6Decks, expectedWinRateVsField d ≤ expectedWinRateVsField .GrimssnarlFroslass := by
  native_decide

theorem DRAGAPULT_EXPECTED_WR_VS_FIELD_BELOW_FIFTY :
    expectedWinRateVsField .DragapultDusknoir < 1 / 2 := by native_decide

end PokemonLean.TournamentStrategy
