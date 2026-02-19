import PokemonLean.Basic
import Std.Tactic

namespace PokemonLean.TournamentRules

open PokemonLean

/-- Official best-of-3 matches have at most three games. -/
def maxGamesPerMatch : Nat := 3

/-- Two game wins are required to win a best-of-3 match. -/
def gamesNeededToWinMatch : Nat := 2

/-- Official regulation round timer, in minutes. -/
def regulationTimeLimitMinutes : Nat := 50

/-- Sudden death starts with three prize cards per player. -/
def suddenDeathPrizeCount : Nat := 3

@[simp] theorem maxGamesPerMatch_value : maxGamesPerMatch = 3 := rfl
@[simp] theorem gamesNeededToWinMatch_value : gamesNeededToWinMatch = 2 := rfl
@[simp] theorem regulationTimeLimitMinutes_value : regulationTimeLimitMinutes = 50 := rfl
@[simp] theorem suddenDeathPrizeCount_value : suddenDeathPrizeCount = 3 := rfl


/-- The match is still in regulation time. -/
def withinRegulationTime (elapsedMinutes : Nat) : Prop :=
  elapsedMinutes ≤ regulationTimeLimitMinutes

/-- Regulation time has elapsed. -/
def regulationComplete (elapsedMinutes : Nat) : Prop :=
  regulationTimeLimitMinutes ≤ elapsedMinutes

theorem withinRegulationTime_limit :
    withinRegulationTime regulationTimeLimitMinutes := by
  simp [withinRegulationTime]

theorem regulationComplete_limit :
    regulationComplete regulationTimeLimitMinutes := by
  simp [regulationComplete]

theorem withinRegulationTime_of_lt {elapsedMinutes : Nat}
    (h : elapsedMinutes < regulationTimeLimitMinutes) :
    withinRegulationTime elapsedMinutes := by
  exact Nat.le_of_lt h

theorem regulationComplete_of_ge {elapsedMinutes : Nat}
    (h : regulationTimeLimitMinutes ≤ elapsedMinutes) :
    regulationComplete elapsedMinutes := h

theorem regulation_exact_of_within_and_complete {elapsedMinutes : Nat}
    (h₁ : withinRegulationTime elapsedMinutes) (h₂ : regulationComplete elapsedMinutes) :
    elapsedMinutes = regulationTimeLimitMinutes := by
  exact Nat.le_antisymm h₁ h₂

/-- Best-of-3 scoreline tracking. -/
structure MatchScore where
  playerOneWins : Nat
  playerTwoWins : Nat
  draws : Nat
  deriving Repr, BEq, DecidableEq

/-- Total games played in a match. -/
def totalGames (score : MatchScore) : Nat :=
  score.playerOneWins + score.playerTwoWins + score.draws

/-- Number of game wins for a specific player. -/
def gameWins (score : MatchScore) (player : PlayerId) : Nat :=
  match player with
  | .playerOne => score.playerOneWins
  | .playerTwo => score.playerTwoWins

/-- A scoreline is legal for best-of-3 if at most 3 games were played. -/
def bestOfThreeLegal (score : MatchScore) : Prop :=
  totalGames score ≤ maxGamesPerMatch

/-- Match win requirement: at least 2 game wins. -/
abbrev hasMatchWin (score : MatchScore) (player : PlayerId) : Prop :=
  gameWins score player ≥ gamesNeededToWinMatch

/-- Full match win condition: 2 game wins within a legal best-of-3 scoreline. -/
def matchWinCondition (score : MatchScore) (player : PlayerId) : Prop :=
  hasMatchWin score player ∧ bestOfThreeLegal score

/-- The game-win tally is tied. -/
def tiedGames (score : MatchScore) : Prop :=
  score.playerOneWins = score.playerTwoWins

instance (score : MatchScore) (player : PlayerId) : Decidable (hasMatchWin score player) := by
  unfold hasMatchWin gameWins
  cases player <;> infer_instance

/-- Winner from the scoreline, if any. -/
def matchWinner (score : MatchScore) : Option PlayerId :=
  if hasMatchWin score .playerOne then
    some .playerOne
  else if hasMatchWin score .playerTwo then
    some .playerTwo
  else
    none

@[simp] theorem totalGames_mk (w1 w2 d : Nat) :
    totalGames { playerOneWins := w1, playerTwoWins := w2, draws := d } = w1 + w2 + d := rfl

@[simp] theorem gameWins_playerOne (score : MatchScore) :
    gameWins score .playerOne = score.playerOneWins := rfl

@[simp] theorem gameWins_playerTwo (score : MatchScore) :
    gameWins score .playerTwo = score.playerTwoWins := rfl

theorem totalGames_nonneg (score : MatchScore) : 0 ≤ totalGames score := by
  exact Nat.zero_le _

theorem bestOfThreeLegal_iff (score : MatchScore) :
    bestOfThreeLegal score ↔ totalGames score ≤ maxGamesPerMatch := Iff.rfl

theorem hasMatchWin_playerOne_iff (score : MatchScore) :
    hasMatchWin score .playerOne ↔ score.playerOneWins ≥ gamesNeededToWinMatch := by
  simp [hasMatchWin, gameWins]

theorem hasMatchWin_playerTwo_iff (score : MatchScore) :
    hasMatchWin score .playerTwo ↔ score.playerTwoWins ≥ gamesNeededToWinMatch := by
  simp [hasMatchWin, gameWins]

theorem matchWinCondition_playerOne_iff (score : MatchScore) :
    matchWinCondition score .playerOne ↔
      score.playerOneWins ≥ gamesNeededToWinMatch ∧ totalGames score ≤ maxGamesPerMatch := by
  simp [matchWinCondition, hasMatchWin, gameWins, bestOfThreeLegal]

theorem matchWinCondition_playerTwo_iff (score : MatchScore) :
    matchWinCondition score .playerTwo ↔
      score.playerTwoWins ≥ gamesNeededToWinMatch ∧ totalGames score ≤ maxGamesPerMatch := by
  simp [matchWinCondition, hasMatchWin, gameWins, bestOfThreeLegal]

theorem matchWinner_playerOne (score : MatchScore)
    (h : hasMatchWin score .playerOne) :
    matchWinner score = some .playerOne := by
  have h' : 2 ≤ score.playerOneWins := by
    simpa [hasMatchWin, gameWins, gamesNeededToWinMatch] using h
  simp [matchWinner, hasMatchWin, gameWins, gamesNeededToWinMatch, h']

theorem matchWinner_playerTwo (score : MatchScore)
    (h₁ : ¬ hasMatchWin score .playerOne) (h₂ : hasMatchWin score .playerTwo) :
    matchWinner score = some .playerTwo := by
  have h₁' : ¬ 2 ≤ score.playerOneWins := by
    simpa [hasMatchWin, gameWins, gamesNeededToWinMatch] using h₁
  have h₂' : 2 ≤ score.playerTwoWins := by
    simpa [hasMatchWin, gameWins, gamesNeededToWinMatch] using h₂
  simp [matchWinner, hasMatchWin, gameWins, gamesNeededToWinMatch, h₁', h₂']

theorem matchWinner_none (score : MatchScore)
    (h₁ : ¬ hasMatchWin score .playerOne) (h₂ : ¬ hasMatchWin score .playerTwo) :
    matchWinner score = none := by
  have h₁' : ¬ 2 ≤ score.playerOneWins := by
    simpa [hasMatchWin, gameWins, gamesNeededToWinMatch] using h₁
  have h₂' : ¬ 2 ≤ score.playerTwoWins := by
    simpa [hasMatchWin, gameWins, gamesNeededToWinMatch] using h₂
  simp [matchWinner, hasMatchWin, gameWins, gamesNeededToWinMatch, h₁', h₂']

theorem tiedGames_zero (draws : Nat) :
    tiedGames { playerOneWins := 0, playerTwoWins := 0, draws := draws } := by
  simp [tiedGames]

theorem tiedGames_symm (score : MatchScore) :
    tiedGames score ↔ score.playerTwoWins = score.playerOneWins := by
  constructor
  · intro h
    simpa [tiedGames] using Eq.symm h
  · intro h
    simpa [tiedGames] using Eq.symm h

theorem bestOfThreeLegal_zero :
    bestOfThreeLegal { playerOneWins := 0, playerTwoWins := 0, draws := 0 } := by
  simp [bestOfThreeLegal, totalGames, maxGamesPerMatch]

theorem noMatchWin_of_lt_two (score : MatchScore) (player : PlayerId)
    (h : gameWins score player < gamesNeededToWinMatch) :
    ¬ hasMatchWin score player := by
  intro hWin
  exact Nat.not_le_of_lt h hWin

/-- Sudden death setup requires each player to start with exactly 3 prizes. -/
def suddenDeathSetup (playerOnePrizes playerTwoPrizes : Nat) : Prop :=
  playerOnePrizes = suddenDeathPrizeCount ∧ playerTwoPrizes = suddenDeathPrizeCount

theorem suddenDeathSetup_iff (playerOnePrizes playerTwoPrizes : Nat) :
    suddenDeathSetup playerOnePrizes playerTwoPrizes ↔
      playerOnePrizes = suddenDeathPrizeCount ∧ playerTwoPrizes = suddenDeathPrizeCount := Iff.rfl

theorem suddenDeathSetup_default :
    suddenDeathSetup suddenDeathPrizeCount suddenDeathPrizeCount := by
  simp [suddenDeathSetup]

theorem suddenDeathSetup_symm (playerOnePrizes playerTwoPrizes : Nat) :
    suddenDeathSetup playerOnePrizes playerTwoPrizes →
      suddenDeathSetup playerTwoPrizes playerOnePrizes := by
  rintro ⟨h₁, h₂⟩
  exact ⟨h₂, h₁⟩

theorem suddenDeathSetup_left (playerOnePrizes playerTwoPrizes : Nat)
    (h : suddenDeathSetup playerOnePrizes playerTwoPrizes) :
    playerOnePrizes = suddenDeathPrizeCount := h.1

theorem suddenDeathSetup_right (playerOnePrizes playerTwoPrizes : Nat)
    (h : suddenDeathSetup playerOnePrizes playerTwoPrizes) :
    playerTwoPrizes = suddenDeathPrizeCount := h.2

/-- Sudden death is required if time is complete, game wins are tied, and no match winner exists. -/
def requiresSuddenDeath (elapsedMinutes : Nat) (score : MatchScore) : Prop :=
  regulationComplete elapsedMinutes ∧ tiedGames score ∧ matchWinner score = none

theorem requiresSuddenDeath_iff (elapsedMinutes : Nat) (score : MatchScore) :
    requiresSuddenDeath elapsedMinutes score ↔
      regulationComplete elapsedMinutes ∧ tiedGames score ∧ matchWinner score = none := Iff.rfl

theorem requiresSuddenDeath_of (elapsedMinutes : Nat) (score : MatchScore)
    (hTime : regulationComplete elapsedMinutes) (hTie : tiedGames score)
    (hWinner : matchWinner score = none) :
    requiresSuddenDeath elapsedMinutes score := by
  exact ⟨hTime, hTie, hWinner⟩

theorem requiresSuddenDeath_implies_complete (elapsedMinutes : Nat) (score : MatchScore) :
    requiresSuddenDeath elapsedMinutes score → regulationComplete elapsedMinutes := by
  intro h
  exact h.1

theorem requiresSuddenDeath_implies_tied (elapsedMinutes : Nat) (score : MatchScore) :
    requiresSuddenDeath elapsedMinutes score → tiedGames score := by
  intro h
  exact h.2.1

theorem requiresSuddenDeath_implies_no_winner (elapsedMinutes : Nat) (score : MatchScore) :
    requiresSuddenDeath elapsedMinutes score → matchWinner score = none := by
  intro h
  exact h.2.2

/-- Opponent state helper used for game-win checks. -/
def opponentState (state : GameState) (player : PlayerId) : PlayerState :=
  getPlayerState state (otherPlayer player)

/-- Win by taking all opponent prize cards. -/
def gameWonByPrizes (state : GameState) (player : PlayerId) : Prop :=
  (opponentState state player).prizes.length = 0

/-- Win by opponent decking out. -/
def gameWonByDeckOut (state : GameState) (player : PlayerId) : Prop :=
  (opponentState state player).deck = []

/-- Win by opponent having no active Pokemon and no bench Pokemon. -/
def gameWonByNoBenchPokemon (state : GameState) (player : PlayerId) : Prop :=
  (opponentState state player).active = none ∧ (opponentState state player).bench = []

/-- Official game win reasons used in tournament policy. -/
inductive GameWinReason
  | prizes
  | deckOut
  | noBenchPokemon
  deriving Repr, BEq, DecidableEq

/-- Predicate for satisfying a specific game win reason. -/
def satisfiesGameWinReason (state : GameState) (player : PlayerId) : GameWinReason → Prop
  | .prizes => gameWonByPrizes state player
  | .deckOut => gameWonByDeckOut state player
  | .noBenchPokemon => gameWonByNoBenchPokemon state player

/-- Overall game win: one of the official game win reasons holds. -/
def hasGameWin (state : GameState) (player : PlayerId) : Prop :=
  ∃ reason : GameWinReason, satisfiesGameWinReason state player reason

theorem gameWonByPrizes_iff (state : GameState) (player : PlayerId) :
    gameWonByPrizes state player ↔ (opponentState state player).prizes = [] := by
  constructor
  · intro h
    exact List.eq_nil_of_length_eq_zero h
  · intro h
    simpa [gameWonByPrizes, h]

theorem gameWonByDeckOut_iff (state : GameState) (player : PlayerId) :
    gameWonByDeckOut state player ↔ (opponentState state player).deck = [] := Iff.rfl

theorem gameWonByNoBenchPokemon_iff (state : GameState) (player : PlayerId) :
    gameWonByNoBenchPokemon state player ↔
      (opponentState state player).active = none ∧ (opponentState state player).bench = [] := Iff.rfl

theorem satisfiesGameWinReason_prizes (state : GameState) (player : PlayerId) :
    satisfiesGameWinReason state player .prizes ↔ gameWonByPrizes state player := Iff.rfl

theorem satisfiesGameWinReason_deckOut (state : GameState) (player : PlayerId) :
    satisfiesGameWinReason state player .deckOut ↔ gameWonByDeckOut state player := Iff.rfl

theorem satisfiesGameWinReason_noBenchPokemon (state : GameState) (player : PlayerId) :
    satisfiesGameWinReason state player .noBenchPokemon ↔ gameWonByNoBenchPokemon state player := Iff.rfl

theorem hasGameWin_of_prizes (state : GameState) (player : PlayerId)
    (h : gameWonByPrizes state player) : hasGameWin state player := by
  exact ⟨.prizes, h⟩

theorem hasGameWin_of_deckOut (state : GameState) (player : PlayerId)
    (h : gameWonByDeckOut state player) : hasGameWin state player := by
  exact ⟨.deckOut, h⟩

theorem hasGameWin_of_noBenchPokemon (state : GameState) (player : PlayerId)
    (h : gameWonByNoBenchPokemon state player) : hasGameWin state player := by
  exact ⟨.noBenchPokemon, h⟩

theorem hasGameWin_iff (state : GameState) (player : PlayerId) :
    hasGameWin state player ↔
      gameWonByPrizes state player ∨
      gameWonByDeckOut state player ∨
      gameWonByNoBenchPokemon state player := by
  constructor
  · rintro ⟨reason, hReason⟩
    cases reason with
    | prizes =>
        exact Or.inl hReason
    | deckOut =>
        exact Or.inr (Or.inl hReason)
    | noBenchPokemon =>
        exact Or.inr (Or.inr hReason)
  · intro h
    rcases h with hPrizes | hRest
    · exact ⟨.prizes, hPrizes⟩
    · rcases hRest with hDeckOut | hNoBench
      · exact ⟨.deckOut, hDeckOut⟩
      · exact ⟨.noBenchPokemon, hNoBench⟩

/-- Match record used in standings and tie-break calculations. -/
structure MatchRecord where
  wins : Nat
  losses : Nat
  draws : Nat
  deriving Repr, BEq, DecidableEq

/-- Number of played matches in a record. -/
def matchesPlayed (record : MatchRecord) : Nat :=
  record.wins + record.losses + record.draws

/-- Match points using 3/1/0 scoring. -/
def matchPoints (record : MatchRecord) : Nat :=
  3 * record.wins + record.draws

/-- Match-win percentage as an integer percentage in `[0, 100]`. -/
def matchWinPercentage (record : MatchRecord) : Nat :=
  if matchesPlayed record = 0 then 0
  else (matchPoints record * 100) / (3 * matchesPlayed record)

@[simp] theorem matchesPlayed_mk (w l d : Nat) :
    matchesPlayed { wins := w, losses := l, draws := d } = w + l + d := rfl

@[simp] theorem matchPoints_mk (w l d : Nat) :
    matchPoints { wins := w, losses := l, draws := d } = 3 * w + d := rfl

theorem matchesPlayed_nonneg (record : MatchRecord) : 0 ≤ matchesPlayed record := by
  exact Nat.zero_le _

theorem matchPoints_nonneg (record : MatchRecord) : 0 ≤ matchPoints record := by
  exact Nat.zero_le _

theorem matchPoints_le_three_mul_matchesPlayed (record : MatchRecord) :
    matchPoints record ≤ 3 * matchesPlayed record := by
  unfold matchPoints matchesPlayed
  omega

theorem matchWinPercentage_zero_when_no_matches (record : MatchRecord)
    (h : matchesPlayed record = 0) :
    matchWinPercentage record = 0 := by
  simp [matchWinPercentage, h]

theorem matchWinPercentage_le_100 (record : MatchRecord) :
    matchWinPercentage record ≤ 100 := by
  unfold matchWinPercentage
  split
  · decide
  · apply Nat.div_le_of_le_mul
    have hPoints : matchPoints record ≤ 3 * matchesPlayed record :=
      matchPoints_le_three_mul_matchesPlayed record
    have hMul : matchPoints record * 100 ≤ (3 * matchesPlayed record) * 100 :=
      Nat.mul_le_mul_right 100 hPoints
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hMul

/-- OMW%: average match-win percentage among opponents. -/
def opponentMatchWinPercentage (opponents : List MatchRecord) : Nat :=
  if opponents.length = 0 then 0
  else (opponents.map matchWinPercentage).sum / opponents.length

theorem opponentMatchWinPercentage_nil :
    opponentMatchWinPercentage [] = 0 := by
  simp [opponentMatchWinPercentage]

theorem sum_matchWinPercentage_le (opponents : List MatchRecord) :
    (opponents.map matchWinPercentage).sum ≤ opponents.length * 100 := by
  induction opponents with
  | nil =>
      simp
  | cons opponent rest ih =>
      calc
        (List.map matchWinPercentage (opponent :: rest)).sum
            = matchWinPercentage opponent + (List.map matchWinPercentage rest).sum := by
              simp
        _ ≤ 100 + rest.length * 100 := by
              exact Nat.add_le_add (matchWinPercentage_le_100 opponent) ih
        _ = (rest.length + 1) * 100 := by
              omega
        _ = (opponent :: rest).length * 100 := by
              simp

theorem opponentMatchWinPercentage_le_100 (opponents : List MatchRecord) :
    opponentMatchWinPercentage opponents ≤ 100 := by
  unfold opponentMatchWinPercentage
  split
  · decide
  · apply Nat.div_le_of_le_mul
    have hSum : (opponents.map matchWinPercentage).sum ≤ opponents.length * 100 :=
      sum_matchWinPercentage_le opponents
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hSum

/-- OOMW%: average OMW% of opponents. -/
def opponentOpponentMatchWinPercentage (opponents : List (List MatchRecord)) : Nat :=
  if opponents.length = 0 then 0
  else (opponents.map opponentMatchWinPercentage).sum / opponents.length

theorem opponentOpponentMatchWinPercentage_nil :
    opponentOpponentMatchWinPercentage [] = 0 := by
  simp [opponentOpponentMatchWinPercentage]

theorem sum_opponentMatchWinPercentage_le (opponents : List (List MatchRecord)) :
    (opponents.map opponentMatchWinPercentage).sum ≤ opponents.length * 100 := by
  induction opponents with
  | nil =>
      simp
  | cons opponent rest ih =>
      calc
        (List.map opponentMatchWinPercentage (opponent :: rest)).sum
            = opponentMatchWinPercentage opponent + (List.map opponentMatchWinPercentage rest).sum := by
              simp
        _ ≤ 100 + rest.length * 100 := by
              exact Nat.add_le_add (opponentMatchWinPercentage_le_100 opponent) ih
        _ = (rest.length + 1) * 100 := by
              omega
        _ = (opponent :: rest).length * 100 := by
              simp

theorem opponentOpponentMatchWinPercentage_le_100 (opponents : List (List MatchRecord)) :
    opponentOpponentMatchWinPercentage opponents ≤ 100 := by
  unfold opponentOpponentMatchWinPercentage
  split
  · decide
  · apply Nat.div_le_of_le_mul
    have hSum : (opponents.map opponentMatchWinPercentage).sum ≤ opponents.length * 100 :=
      sum_opponentMatchWinPercentage_le opponents
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hSum

/-- Match conclusion for Swiss/tournament bookkeeping. -/
inductive MatchConclusion
  | matchWin (player : PlayerId)
  | draw
  | intentionalDraw
  deriving Repr, BEq, DecidableEq

/-- Predicate identifying intentional draws. -/
def isIntentionalDraw : MatchConclusion → Prop
  | .intentionalDraw => True
  | _ => False

/-- Match points awarded for a conclusion from one player's perspective. -/
def matchPointsFromConclusion (conclusion : MatchConclusion) (player : PlayerId) : Nat :=
  match conclusion with
  | .matchWin winner => if winner = player then 3 else 0
  | .draw => 1
  | .intentionalDraw => 1

@[simp] theorem isIntentionalDraw_intentionalDraw :
    isIntentionalDraw .intentionalDraw := by
  simp [isIntentionalDraw]

@[simp] theorem isIntentionalDraw_matchWin (player : PlayerId) :
    ¬ isIntentionalDraw (.matchWin player) := by
  simp [isIntentionalDraw]

@[simp] theorem isIntentionalDraw_draw :
    ¬ isIntentionalDraw .draw := by
  simp [isIntentionalDraw]

@[simp] theorem matchPointsFromConclusion_matchWin_self (player : PlayerId) :
    matchPointsFromConclusion (.matchWin player) player = 3 := by
  simp [matchPointsFromConclusion]

@[simp] theorem matchPointsFromConclusion_matchWin_other (winner player : PlayerId)
    (h : winner ≠ player) :
    matchPointsFromConclusion (.matchWin winner) player = 0 := by
  simp [matchPointsFromConclusion, h]

@[simp] theorem matchPointsFromConclusion_draw (player : PlayerId) :
    matchPointsFromConclusion .draw player = 1 := by
  simp [matchPointsFromConclusion]

@[simp] theorem matchPointsFromConclusion_intentionalDraw (player : PlayerId) :
    matchPointsFromConclusion .intentionalDraw player = 1 := by
  simp [matchPointsFromConclusion]

/-- Intentional draw is legal only during regulation and only if no winner is currently determined. -/
def intentionalDrawAllowed (elapsedMinutes : Nat) (score : MatchScore) : Prop :=
  withinRegulationTime elapsedMinutes ∧ matchWinner score = none

theorem intentionalDrawAllowed_iff (elapsedMinutes : Nat) (score : MatchScore) :
    intentionalDrawAllowed elapsedMinutes score ↔
      withinRegulationTime elapsedMinutes ∧ matchWinner score = none := Iff.rfl

theorem intentionalDrawAllowed_of_within_and_no_winner (elapsedMinutes : Nat) (score : MatchScore)
    (hTime : withinRegulationTime elapsedMinutes) (hWinner : matchWinner score = none) :
    intentionalDrawAllowed elapsedMinutes score := by
  exact ⟨hTime, hWinner⟩

theorem intentionalDrawAllowed_implies_within (elapsedMinutes : Nat) (score : MatchScore) :
    intentionalDrawAllowed elapsedMinutes score → withinRegulationTime elapsedMinutes := by
  intro h
  exact h.1

theorem intentionalDrawAllowed_implies_no_winner (elapsedMinutes : Nat) (score : MatchScore) :
    intentionalDrawAllowed elapsedMinutes score → matchWinner score = none := by
  intro h
  exact h.2

theorem not_withinRegulationTime_of_gt_limit {elapsedMinutes : Nat}
    (h : regulationTimeLimitMinutes < elapsedMinutes) :
    ¬ withinRegulationTime elapsedMinutes := by
  intro hWithin
  exact Nat.not_lt.mpr hWithin h

theorem intentionalDraw_not_allowed_of_gt_limit {elapsedMinutes : Nat} (score : MatchScore)
    (h : regulationTimeLimitMinutes < elapsedMinutes) :
    ¬ intentionalDrawAllowed elapsedMinutes score := by
  intro hAllowed
  exact (not_withinRegulationTime_of_gt_limit h) hAllowed.1

/-- Tie-break tuple `(MW%, OMW%, OOMW%)`. -/
def tieBreakTuple (record : MatchRecord) (opponents : List MatchRecord)
    (opponentOpponents : List (List MatchRecord)) : Nat × Nat × Nat :=
  (matchWinPercentage record, opponentMatchWinPercentage opponents,
    opponentOpponentMatchWinPercentage opponentOpponents)

@[simp] theorem tieBreakTuple_fst (record : MatchRecord) (opponents : List MatchRecord)
    (opponentOpponents : List (List MatchRecord)) :
    (tieBreakTuple record opponents opponentOpponents).1 = matchWinPercentage record := rfl

@[simp] theorem tieBreakTuple_snd (record : MatchRecord) (opponents : List MatchRecord)
    (opponentOpponents : List (List MatchRecord)) :
    (tieBreakTuple record opponents opponentOpponents).2.1 = opponentMatchWinPercentage opponents := rfl

@[simp] theorem tieBreakTuple_trd (record : MatchRecord) (opponents : List MatchRecord)
    (opponentOpponents : List (List MatchRecord)) :
    (tieBreakTuple record opponents opponentOpponents).2.2 =
      opponentOpponentMatchWinPercentage opponentOpponents := rfl

theorem tieBreakTuple_bounds (record : MatchRecord) (opponents : List MatchRecord)
    (opponentOpponents : List (List MatchRecord)) :
    (tieBreakTuple record opponents opponentOpponents).1 ≤ 100 ∧
      (tieBreakTuple record opponents opponentOpponents).2.1 ≤ 100 ∧
      (tieBreakTuple record opponents opponentOpponents).2.2 ≤ 100 := by
  exact ⟨
    matchWinPercentage_le_100 record,
    opponentMatchWinPercentage_le_100 opponents,
    opponentOpponentMatchWinPercentage_le_100 opponentOpponents
  ⟩

end PokemonLean.TournamentRules
