import PokemonLean.Basic
import PokemonLean.Decks

namespace PokemonLean.Tournament

open PokemonLean
open PokemonLean.Decks

structure PlayerProfile where
  name : String
  rating : Nat
  deck : List Card
  deriving Repr

structure MatchResult where
  playerOne : PlayerProfile
  playerTwo : PlayerProfile
  winner : PlayerId
  turns : Nat
  deriving Repr

def winnerProfile (result : MatchResult) : PlayerProfile :=
  match result.winner with
  | .playerOne => result.playerOne
  | .playerTwo => result.playerTwo

def loserProfile (result : MatchResult) : PlayerProfile :=
  match result.winner with
  | .playerOne => result.playerTwo
  | .playerTwo => result.playerOne

def matchLegal (result : MatchResult) : Prop :=
  DeckValidity standardRules result.playerOne.deck ∧
  DeckValidity standardRules result.playerTwo.deck

def scoreWin : Nat := 3
def scoreLoss : Nat := 0
def scoreDraw : Nat := 1

def scoreResult (winner : Option PlayerId) : Nat × Nat :=
  match winner with
  | none => (scoreDraw, scoreDraw)
  | some .playerOne => (scoreWin, scoreLoss)
  | some .playerTwo => (scoreLoss, scoreWin)

structure Standing where
  player : PlayerProfile
  points : Nat
  games : Nat
  wins : Nat
  losses : Nat
  draws : Nat
  deriving Repr

def emptyStanding (player : PlayerProfile) : Standing :=
  { player := player, points := 0, games := 0, wins := 0, losses := 0, draws := 0 }

def applyResultToStanding (standing : Standing) (winner : Option PlayerId) (isPlayerOne : Bool) : Standing :=
  let (p1, p2) := scoreResult winner
  if isPlayerOne then
    let points := standing.points + p1
    let wins := standing.wins + (if winner = some .playerOne then 1 else 0)
    let losses := standing.losses + (if winner = some .playerTwo then 1 else 0)
    let draws := standing.draws + (if winner = none then 1 else 0)
    { standing with points := points, games := standing.games + 1, wins := wins, losses := losses, draws := draws }
  else
    let points := standing.points + p2
    let wins := standing.wins + (if winner = some .playerTwo then 1 else 0)
    let losses := standing.losses + (if winner = some .playerOne then 1 else 0)
    let draws := standing.draws + (if winner = none then 1 else 0)
    { standing with points := points, games := standing.games + 1, wins := wins, losses := losses, draws := draws }

def recordMatch (stand1 stand2 : Standing) (winner : Option PlayerId) : Standing × Standing :=
  let s1 := applyResultToStanding stand1 winner true
  let s2 := applyResultToStanding stand2 winner false
  (s1, s2)

def scoreDelta (before after : Standing) : Nat :=
  after.points - before.points

theorem scoreDelta_nonneg (before after : Standing) :
    0 ≤ scoreDelta before after := by
  simp [scoreDelta]

structure SwissRound where
  results : List MatchResult
  deriving Repr

def roundPoints (round : SwissRound) (player : PlayerProfile) : Nat :=
  round.results.foldl (fun acc matchResult =>
    if matchResult.playerOne.name = player.name then
      acc + (scoreResult (some matchResult.winner)).1
    else if matchResult.playerTwo.name = player.name then
      acc + (scoreResult (some matchResult.winner)).2
    else acc) 0

def totalPoints (rounds : List SwissRound) (player : PlayerProfile) : Nat :=
  (rounds.map (fun r => roundPoints r player)).sum

theorem totalPoints_nil (player : PlayerProfile) :
    totalPoints [] player = 0 := by
  simp [totalPoints]

theorem totalPoints_cons (round : SwissRound) (rounds : List SwissRound) (player : PlayerProfile) :
    totalPoints (round :: rounds) player = roundPoints round player + totalPoints rounds player := by
  simp [totalPoints]

theorem totalPoints_nonneg (rounds : List SwissRound) (player : PlayerProfile) :
    0 ≤ totalPoints rounds player := by
  simp [totalPoints]

theorem totalPoints_append (rounds1 rounds2 : List SwissRound) (player : PlayerProfile) :
    totalPoints (rounds1 ++ rounds2) player = totalPoints rounds1 player + totalPoints rounds2 player := by
  simp [totalPoints, List.map_append]
  induction rounds1 with
  | nil => simp
  | cons r rs ih => simp [List.sum_cons, ih, Nat.add_assoc]

def topCutEligible (rounds : List SwissRound) (player : PlayerProfile) (threshold : Nat) : Prop :=
  totalPoints rounds player ≥ threshold

theorem topCutEligible_mono (rounds : List SwissRound) (player : PlayerProfile)
    (threshold threshold' : Nat) (h : threshold ≤ threshold') :
    topCutEligible rounds player threshold' → topCutEligible rounds player threshold := by
  intro hEligible
  -- `threshold ≤ threshold' ≤ totalPoints rounds player`
  exact Nat.le_trans h hEligible

theorem topCutEligible_zero (rounds : List SwissRound) (player : PlayerProfile) :
    topCutEligible rounds player 0 := by
  simp [topCutEligible]

theorem topCutEligible_of_append_left (rounds1 rounds2 : List SwissRound)
    (player : PlayerProfile) (threshold : Nat) :
    topCutEligible rounds1 player threshold → topCutEligible (rounds1 ++ rounds2) player threshold := by
  intro hEligible
  have hSum : totalPoints (rounds1 ++ rounds2) player =
      totalPoints rounds1 player + totalPoints rounds2 player :=
    totalPoints_append rounds1 rounds2 player
  have hLe : totalPoints rounds1 player ≤ totalPoints (rounds1 ++ rounds2) player := by
    rw [hSum]
    exact Nat.le_add_right _ _
  exact Nat.le_trans hEligible hLe

theorem topCutEligible_of_append_right (rounds1 rounds2 : List SwissRound)
    (player : PlayerProfile) (threshold : Nat) :
    topCutEligible rounds2 player threshold → topCutEligible (rounds1 ++ rounds2) player threshold := by
  intro hEligible
  have hSum : totalPoints (rounds1 ++ rounds2) player =
      totalPoints rounds1 player + totalPoints rounds2 player :=
    totalPoints_append rounds1 rounds2 player
  have hLe : totalPoints rounds2 player ≤ totalPoints (rounds1 ++ rounds2) player := by
    rw [hSum]
    exact Nat.le_add_left _ _
  exact Nat.le_trans hEligible hLe

def ratingDelta (winner loser : PlayerProfile) : Int :=
  Int.ofNat (winner.rating + 10) - Int.ofNat (loser.rating + 10)

theorem ratingDelta_self (player : PlayerProfile) :
    ratingDelta player player = 0 := by
  simp [ratingDelta]

theorem ratingDelta_add_swap_zero (p1 p2 : PlayerProfile) :
    ratingDelta p1 p2 + ratingDelta p2 p1 = 0 := by
  unfold ratingDelta
  let a : Int := Int.ofNat (p1.rating + 10)
  let b : Int := Int.ofNat (p2.rating + 10)
  have hab : (a - b) + (b - a) = 0 := by
    -- normalize to a cancellative form
    calc
      (a - b) + (b - a) = (a + -b) + (b + -a) := by
        simp [Int.sub_eq_add_neg, Int.add_assoc]
      _ = a + (-a + (b + -b)) := by
        simp [Int.add_assoc, Int.add_left_comm, Int.add_comm]
      _ = b + -b := by
        simpa using (Int.add_neg_cancel_left a (b + -b))
      _ = 0 := by
        simp [Int.add_right_neg]
  simpa [a, b] using hab

theorem ratingDelta_add_swap (p1 p2 : PlayerProfile) :
    ratingDelta p1 p2 + ratingDelta p2 p1 =
      (Int.ofNat (p1.rating + 10) - Int.ofNat (p1.rating + 10)) +
      (Int.ofNat (p2.rating + 10) - Int.ofNat (p2.rating + 10)) := by
  -- both sides are 0
  have hL : ratingDelta p1 p2 + ratingDelta p2 p1 = 0 := ratingDelta_add_swap_zero p1 p2
  have hR :
      (Int.ofNat (p1.rating + 10) - Int.ofNat (p1.rating + 10)) +
        (Int.ofNat (p2.rating + 10) - Int.ofNat (p2.rating + 10)) = 0 := by
    simp
  exact hL.trans hR.symm

def expectedScore (ratingA ratingB : Nat) : Nat :=
  if ratingA + ratingB = 0 then 50 else ratingA * 100 / (ratingA + ratingB)

theorem expectedScore_bounds (ratingA ratingB : Nat) :
    expectedScore ratingA ratingB ≤ 100 := by
  unfold expectedScore
  split
  · decide
  · -- show: ratingA * 100 / (ratingA + ratingB) ≤ 100
    apply Nat.div_le_of_le_mul
    have hle : ratingA ≤ ratingA + ratingB := Nat.le_add_right _ _
    -- multiply both sides by 100
    have hm : ratingA * 100 ≤ (ratingA + ratingB) * 100 := Nat.mul_le_mul_right 100 hle
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hm

def updateRating (rating : Nat) (delta : Int) : Nat :=
  if delta ≥ 0 then rating + Int.toNat delta else rating - Int.toNat (-delta)

theorem updateRating_nonneg (rating : Nat) (delta : Int) :
    0 ≤ updateRating rating delta := by
  -- `updateRating` returns a `Nat`, so it is always nonnegative.
  exact Nat.zero_le _

end PokemonLean.Tournament
