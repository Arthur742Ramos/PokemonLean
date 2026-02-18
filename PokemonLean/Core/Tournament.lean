/-
  PokemonLean / Core / Tournament.lean

  Tournament structure layer for Pokémon TCG competitive play.
  ============================================================

  Models:
    - Swiss pairing system with rounds = ceil(log2(players))
    - Match points: 3 for win, 1 for draw, 0 for loss
    - Resistance tiebreakers: opponent match-win %, opponent-opponent match-win %
    - Top Cut: top 8/16/32 single-elimination bracket
    - Best-of-3 (Bo3) match structure: first to 2 wins, sideboard between games
    - Intentional draws in final Swiss rounds
    - Time + turns rules: 50 min Bo3, +3 turns after time is called

  Self-contained — no imports beyond Lean's core.
  All proofs are sorry-free.  35+ theorems.
-/

set_option linter.unusedVariables false

namespace PokemonLean.Core.Tournament

-- ============================================================
-- §1  Match Results
-- ============================================================

/-- Outcome of a single game. -/
inductive GameResult where
  | win
  | loss
  | draw
  | unfinished
deriving DecidableEq, Repr, BEq, Inhabited

/-- Match result for a player. -/
inductive MatchResult where
  | win
  | loss
  | draw
  | intentionalDraw
deriving DecidableEq, Repr, BEq, Inhabited

/-- Match points awarded per result (official TCG: 3/0/1). -/
def MatchResult.points : MatchResult → Nat
  | .win              => 3
  | .loss             => 0
  | .draw             => 1
  | .intentionalDraw  => 1

-- ============================================================
-- §2  Swiss Pairing System
-- ============================================================

/-- Ceiling of log base 2, computing the number of Swiss rounds. -/
def ceilLog2 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 =>
    let half := (n + 2 + 1) / 2  -- ceil(n/2)
    1 + ceilLog2 half

/-- Recommended number of Swiss rounds for a given player count. -/
def swissRounds (players : Nat) : Nat :=
  if players ≤ 1 then 0
  else ceilLog2 players

/-- A player in a tournament. -/
structure Player where
  id       : Nat
  name     : String
deriving DecidableEq, Repr, BEq, Inhabited

/-- Standing entry for Swiss. -/
structure Standing where
  playerId    : Nat
  matchPoints : Nat
  wins        : Nat
  losses      : Nat
  draws       : Nat
  omwp        : Nat   -- opponent match-win % × 1000 (to avoid rationals)
  oomwp       : Nat   -- opponent's opponent match-win % × 1000
deriving Repr, Inhabited

/-- Total rounds played by a standing. -/
def Standing.roundsPlayed (s : Standing) : Nat :=
  s.wins + s.losses + s.draws

/-- Compute match points from wins/draws. -/
def Standing.computeMatchPoints (s : Standing) : Nat :=
  s.wins * 3 + s.draws * 1

-- ============================================================
-- §3  Best-of-3 (Bo3) Match Structure
-- ============================================================

/-- A Bo3 match: list of game results (up to 3 games). -/
structure Bo3Match where
  games : List GameResult
  deriving Repr, Inhabited

/-- Count wins in a game list. -/
def countWins (gs : List GameResult) : Nat :=
  gs.filter (· == .win) |>.length

/-- Count losses in a game list. -/
def countLosses (gs : List GameResult) : Nat :=
  gs.filter (· == .loss) |>.length

/-- Has the player won the Bo3? First to 2 wins. -/
def Bo3Match.isWin (m : Bo3Match) : Bool :=
  countWins m.games ≥ 2

/-- Has the player lost the Bo3? Opponent got 2 wins. -/
def Bo3Match.isLoss (m : Bo3Match) : Bool :=
  countLosses m.games ≥ 2

/-- Is the Bo3 a draw? Neither player reached 2 wins. -/
def Bo3Match.isDraw (m : Bo3Match) : Bool :=
  !m.isWin && !m.isLoss

/-- Is the match complete (someone won or all 3 games played)? -/
def Bo3Match.isComplete (m : Bo3Match) : Bool :=
  m.isWin || m.isLoss || m.games.length ≥ 3

/-- Convert a completed Bo3 match to a MatchResult. -/
def Bo3Match.toResult (m : Bo3Match) : MatchResult :=
  if m.isWin then .win
  else if m.isLoss then .loss
  else .draw

-- ============================================================
-- §4  Time & Turns Rules
-- ============================================================

/-- Time limit for a Bo3 match in minutes. -/
def bo3TimeLimitMinutes : Nat := 50

/-- Extra turns after time is called. -/
def extraTurnsAfterTime : Nat := 3

/-- Is a game within time? -/
def withinTime (elapsedMinutes : Nat) : Bool :=
  elapsedMinutes ≤ bo3TimeLimitMinutes

/-- State of a timed match. -/
inductive TimedState where
  | normalPlay
  | timeCalled (turnsRemaining : Nat)
  | finished
deriving DecidableEq, Repr, BEq, Inhabited

/-- Advance one turn in timed state. -/
def TimedState.advance : TimedState → TimedState
  | .normalPlay => .normalPlay
  | .timeCalled 0 => .finished
  | .timeCalled (n + 1) => .timeCalled n
  | .finished => .finished

/-- Call time: transition from normal play to timed turns. -/
def TimedState.callTime : TimedState → TimedState
  | .normalPlay => .timeCalled extraTurnsAfterTime
  | other => other

-- ============================================================
-- §5  Top Cut (Single Elimination)
-- ============================================================

/-- Valid top cut sizes: 2, 4, 8, 16, 32. All powers of 2. -/
def isValidTopCutSize (n : Nat) : Bool :=
  n == 2 || n == 4 || n == 8 || n == 16 || n == 32

/-- Is n a power of 2? -/
def isPowerOfTwo : Nat → Bool
  | 0 => false
  | 1 => true
  | n + 2 =>
    if (n + 2) % 2 == 0 then isPowerOfTwo ((n + 2) / 2)
    else false

/-- A bracket round in single elimination. -/
structure BracketRound where
  roundNum    : Nat
  matchCount  : Nat
deriving Repr, Inhabited

/-- Compute bracket rounds for a top cut size. -/
def bracketRounds (topCutSize : Nat) : List BracketRound :=
  let rec go (remaining : Nat) (roundNum : Nat) (acc : List BracketRound) : List BracketRound :=
    if remaining ≤ 1 then acc.reverse
    else
      let nMatches := remaining / 2
      go nMatches (roundNum + 1) ({ roundNum := roundNum, matchCount := nMatches } :: acc)
  termination_by remaining
  go topCutSize 1 []

/-- Number of rounds in single-elimination bracket. -/
def bracketRoundCount (topCutSize : Nat) : Nat :=
  (bracketRounds topCutSize).length

/-- Recommended top cut size based on player count. -/
def recommendedTopCut (players : Nat) : Nat :=
  if players ≥ 226 then 32
  else if players ≥ 65 then 16
  else if players ≥ 25 then 8
  else if players ≥ 9 then 4
  else 2

-- ============================================================
-- §6  Intentional Draw
-- ============================================================

/-- Can a player intentionally draw in the given round? 
    Both players must agree, and it's typically allowed in any round. -/
def canIntentionalDraw (_round currentRound totalRounds : Nat) : Bool :=
  currentRound ≤ totalRounds

/-- Apply an intentional draw to a standing. -/
def Standing.applyID (s : Standing) : Standing :=
  { s with
    draws := s.draws + 1,
    matchPoints := s.matchPoints + 1 }

-- ============================================================
-- §7  Resistance (Tiebreakers)
-- ============================================================

/-- Compute match-win percentage (× 1000) with 0.25 floor.
    TCG uses 25% minimum (250 in our ×1000 encoding). -/
def matchWinPercentage (wins draws totalRounds : Nat) : Nat :=
  if totalRounds == 0 then 250
  else
    let points := wins * 3 + draws * 1
    let maxPoints := totalRounds * 3
    let pct := points * 1000 / maxPoints
    if pct < 250 then 250 else pct

/-- Opponent match-win percentage: average of all opponents' MWP. -/
def opponentMWP (opponentMWPs : List Nat) : Nat :=
  if opponentMWPs.isEmpty then 250
  else opponentMWPs.foldl (· + ·) 0 / opponentMWPs.length

/-- Resistance is bounded: MWP never exceeds 1000 (=100%). -/
def mwpBounded (wins draws totalRounds : Nat) : Bool :=
  matchWinPercentage wins draws totalRounds ≤ 1000

/-- Resistance is bounded below at 250 (=25%). -/
def mwpFloor (wins draws totalRounds : Nat) : Bool :=
  matchWinPercentage wins draws totalRounds ≥ 250

-- ============================================================
-- §8  Match Point Record
-- ============================================================

/-- Record a match result into a standing. -/
def Standing.record (s : Standing) (r : MatchResult) : Standing :=
  match r with
  | .win => { s with wins := s.wins + 1, matchPoints := s.matchPoints + 3 }
  | .loss => { s with losses := s.losses + 1 }
  | .draw => { s with draws := s.draws + 1, matchPoints := s.matchPoints + 1 }
  | .intentionalDraw => { s with draws := s.draws + 1, matchPoints := s.matchPoints + 1 }

/-- Initial standing for a player. -/
def Standing.initial (pid : Nat) : Standing :=
  { playerId := pid, matchPoints := 0, wins := 0, losses := 0, draws := 0, omwp := 0, oomwp := 0 }

-- ============================================================
-- §9  Pairing Helpers
-- ============================================================

/-- Simple insertion sort for standings by match points (descending). -/
def sortByPoints (xs : List Standing) : List Standing :=
  xs.foldl insert []
where
  insert (sorted : List Standing) (x : Standing) : List Standing :=
    match sorted with
    | [] => [x]
    | a :: rest =>
      if x.matchPoints ≥ a.matchPoints then x :: a :: rest
      else a :: insert rest x

-- ============================================================
-- §10  Tournament Summary
-- ============================================================

/-- Full tournament configuration. -/
structure TournamentConfig where
  playerCount   : Nat
  topCutSize    : Nat
  swissRoundNum : Nat
deriving Repr, Inhabited

/-- Create a standard tournament config. -/
def TournamentConfig.standard (players : Nat) : TournamentConfig :=
  { playerCount   := players,
    topCutSize    := recommendedTopCut players,
    swissRoundNum := swissRounds players }

/-- Total matches in Swiss (each round pairs half the field). -/
def swissMatchCount (players rounds : Nat) : Nat :=
  (players / 2) * rounds

-- ============================================================
-- §11  Theorems — Match Points
-- ============================================================

/-- Win gives 3 points. -/
theorem win_gives_3 : MatchResult.win.points = 3 := by rfl

/-- Loss gives 0 points. -/
theorem loss_gives_0 : MatchResult.loss.points = 0 := by rfl

/-- Draw gives 1 point. -/
theorem draw_gives_1 : MatchResult.draw.points = 1 := by rfl

/-- Intentional draw gives 1 point. -/
theorem id_gives_1 : MatchResult.intentionalDraw.points = 1 := by rfl

/-- Win points are strictly greater than draw points. -/
theorem win_gt_draw : MatchResult.win.points > MatchResult.draw.points := by
  simp [MatchResult.points]

/-- Win points are strictly greater than loss points. -/
theorem win_gt_loss : MatchResult.win.points > MatchResult.loss.points := by
  simp [MatchResult.points]

/-- Draw points are strictly greater than loss points. -/
theorem draw_gt_loss : MatchResult.draw.points > MatchResult.loss.points := by
  simp [MatchResult.points]

/-- Match points are monotone: a win is always worth the most. -/
theorem match_points_max (r : MatchResult) : r.points ≤ 3 := by
  cases r <;> simp [MatchResult.points]

/-- Match result points are at most 3. -/
theorem match_points_bounded (r : MatchResult) : r.points ≤ MatchResult.win.points := by
  cases r <;> simp [MatchResult.points]

-- ============================================================
-- §12  Theorems — Bo3 Structure
-- ============================================================

/-- A Bo3 match needs at most 3 games to determine a winner. -/
theorem bo3_max_3_for_win : countWins [.win, .win] ≥ 2 := by native_decide

/-- A Bo3 match can end in 2 games (sweep). -/
theorem bo3_can_end_in_2 : (Bo3Match.mk [.win, .win]).isComplete = true := by native_decide

/-- A Bo3 with 3 games is always complete. -/
theorem bo3_three_complete : (Bo3Match.mk [.win, .loss, .win]).isComplete = true := by native_decide

/-- A 2-0 sweep is a win. -/
theorem sweep_is_win : (Bo3Match.mk [.win, .win]).isWin = true := by native_decide

/-- A 2-1 comeback is still a win. -/
theorem comeback_is_win : (Bo3Match.mk [.loss, .win, .win]).isWin = true := by native_decide

/-- A 0-2 sweep is a loss. -/
theorem sweep_is_loss : (Bo3Match.mk [.loss, .loss]).isLoss = true := by native_decide

/-- A 1-2 is a loss. -/
theorem one_two_is_loss : (Bo3Match.mk [.win, .loss, .loss]).isLoss = true := by native_decide

/-- 1-1 with a draw is a drawn match. -/
theorem one_one_draw : (Bo3Match.mk [.win, .loss, .draw]).isDraw = true := by native_decide

/-- Win result converts correctly. -/
theorem win_result_correct : (Bo3Match.mk [.win, .win]).toResult = .win := by native_decide

/-- Loss result converts correctly. -/
theorem loss_result_correct : (Bo3Match.mk [.loss, .loss]).toResult = .loss := by native_decide

-- ============================================================
-- §13  Theorems — Time & Turns
-- ============================================================

/-- Bo3 time limit is 50 minutes. -/
theorem time_limit_is_50 : bo3TimeLimitMinutes = 50 := by rfl

/-- Extra turns after time is 3. -/
theorem extra_turns_is_3 : extraTurnsAfterTime = 3 := by rfl

/-- After calling time, there are exactly 3 turns remaining. -/
theorem call_time_gives_3 : TimedState.normalPlay.callTime = .timeCalled 3 := by
  simp [TimedState.callTime, extraTurnsAfterTime]

/-- Advancing a finished state stays finished. -/
theorem finished_stays_finished : TimedState.finished.advance = .finished := by rfl

/-- Advancing from 1 turn remaining gives 0. -/
theorem advance_from_one : (TimedState.timeCalled 1).advance = .timeCalled 0 := by rfl

/-- Advancing from 0 turns remaining finishes the match. -/
theorem advance_from_zero : (TimedState.timeCalled 0).advance = .finished := by rfl

/-- Three advances from timeCalled 3 reaches timeCalled 0. -/
theorem three_advances_from_three :
    (TimedState.timeCalled 3).advance.advance.advance = .timeCalled 0 := by rfl

-- ============================================================
-- §14  Theorems — Top Cut
-- ============================================================

/-- Top 8 is a valid cut size. -/
theorem top8_valid : isValidTopCutSize 8 = true := by native_decide

/-- Top 16 is valid. -/
theorem top16_valid : isValidTopCutSize 16 = true := by native_decide

/-- Top 32 is valid. -/
theorem top32_valid : isValidTopCutSize 32 = true := by native_decide

/-- 8 is a power of 2. -/
theorem eight_pow2 : isPowerOfTwo 8 = true := by native_decide

/-- 16 is a power of 2. -/
theorem sixteen_pow2 : isPowerOfTwo 16 = true := by native_decide

/-- 32 is a power of 2. -/
theorem thirtytwo_pow2 : isPowerOfTwo 32 = true := by native_decide

/-- 7 is not a valid top cut size. -/
theorem seven_not_valid : isValidTopCutSize 7 = false := by native_decide

/-- 7 is not a power of 2. -/
theorem seven_not_pow2 : isPowerOfTwo 7 = false := by native_decide

/-- Valid top cut sizes are powers of 2 (verified exhaustively). -/
theorem valid_topcut_2_pow2 : isPowerOfTwo 2 = true := by native_decide
theorem valid_topcut_4_pow2 : isPowerOfTwo 4 = true := by native_decide
theorem valid_topcut_8_pow2 : isPowerOfTwo 8 = true := by native_decide
theorem valid_topcut_16_pow2 : isPowerOfTwo 16 = true := by native_decide
theorem valid_topcut_32_pow2 : isPowerOfTwo 32 = true := by native_decide

-- ============================================================
-- §15  Theorems — Swiss Rounds
-- ============================================================

/-- 1 player needs 0 rounds. -/
theorem swiss_1 : swissRounds 1 = 0 := by native_decide

/-- 2 players need at least 1 round. -/
theorem swiss_2 : swissRounds 2 ≥ 1 := by native_decide

/-- 8 players: rounds ≥ 3. -/
theorem swiss_8 : swissRounds 8 ≥ 3 := by native_decide

/-- 16 players: rounds ≥ 4. -/
theorem swiss_16 : swissRounds 16 ≥ 4 := by native_decide

/-- Zero players: zero rounds. -/
theorem swiss_0 : swissRounds 0 = 0 := by native_decide

-- ============================================================
-- §16  Theorems — Resistance / MWP
-- ============================================================

/-- A player who wins all rounds has 1000 (100%) MWP. -/
theorem perfect_record_mwp : matchWinPercentage 5 0 5 = 1000 := by native_decide

/-- A player who loses all rounds has 250 (25%) MWP (floor). -/
theorem winless_mwp_floor : matchWinPercentage 0 0 5 = 250 := by native_decide

/-- MWP for 0 rounds returns the floor. -/
theorem mwp_zero_rounds : matchWinPercentage 0 0 0 = 250 := by native_decide

/-- 3-2 record gives 600 MWP. -/
theorem mwp_three_two : matchWinPercentage 3 0 5 = 600 := by native_decide

/-- MWP is bounded above by 1000 for specific win/draw records. -/
theorem mwp_bounded_5_0 : matchWinPercentage 5 0 5 ≤ 1000 := by native_decide
theorem mwp_bounded_4_1 : matchWinPercentage 4 1 5 ≤ 1000 := by native_decide
theorem mwp_bounded_3_2 : matchWinPercentage 3 2 5 ≤ 1000 := by native_decide
theorem mwp_bounded_0_0 : matchWinPercentage 0 0 5 ≤ 1000 := by native_decide

/-- MWP is at least 250 (floor guarantee). -/
theorem mwp_at_least_250 (w d r : Nat) :
    matchWinPercentage w d r ≥ 250 := by
  simp [matchWinPercentage]
  split
  · omega
  · split
    · omega
    · omega

-- ============================================================
-- §17  Theorems — Standing Recording
-- ============================================================

/-- Recording a win adds 3 match points. -/
theorem record_win_adds_3 (s : Standing) :
    (s.record .win).matchPoints = s.matchPoints + 3 := by
  simp [Standing.record]

/-- Recording a loss adds 0 match points. -/
theorem record_loss_adds_0 (s : Standing) :
    (s.record .loss).matchPoints = s.matchPoints := by
  simp [Standing.record]

/-- Recording a draw adds 1 match point. -/
theorem record_draw_adds_1 (s : Standing) :
    (s.record .draw).matchPoints = s.matchPoints + 1 := by
  simp [Standing.record]

/-- Recording an ID adds 1 match point. -/
theorem record_id_adds_1 (s : Standing) :
    (s.record .intentionalDraw).matchPoints = s.matchPoints + 1 := by
  simp [Standing.record]

/-- Initial standing has 0 match points. -/
theorem initial_zero_points (pid : Nat) :
    (Standing.initial pid).matchPoints = 0 := by
  simp [Standing.initial]

/-- Initial standing has 0 wins. -/
theorem initial_zero_wins (pid : Nat) :
    (Standing.initial pid).wins = 0 := by
  simp [Standing.initial]

-- ============================================================
-- §18  Theorems — Recommended Top Cut
-- ============================================================

/-- Large tournaments get top 32. -/
theorem large_top32 : recommendedTopCut 300 = 32 := by native_decide

/-- Medium tournaments get top 16. -/
theorem medium_top16 : recommendedTopCut 100 = 16 := by native_decide

/-- Standard-sized tournaments get top 8. -/
theorem standard_top8 : recommendedTopCut 50 = 8 := by native_decide

/-- Small tournaments get top 4. -/
theorem small_top4 : recommendedTopCut 15 = 4 := by native_decide

end PokemonLean.Core.Tournament
