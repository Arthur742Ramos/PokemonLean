import PokemonLean.Core.Types
import PokemonLean.Probability

open Lean

namespace PokemonLean.DeckConsistency

abbrev Rat := Lean.Rat

/-- Standard opening-hand constants in Pokemon TCG. -/
def standardDeckSize : Nat := 60
def openingHandSize : Nat := 7

/-- Pascal-recursive binomial coefficient. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- Binomial coefficient promoted to `Rat`. -/
def chooseRat (n k : Nat) : Rat :=
  (Int.ofNat (choose n k) : Rat)

/-- Hypergeometric mass function `P(X = k)`. -/
def hypergeometric : Nat → Nat → Nat → Nat → Rat
  | N, K, n, k =>
      (chooseRat K k * chooseRat (N - K) (n - k)) / chooseRat N n

/-- Sum of masses from `k = 0` to `k = n`. -/
def hypergeometricMass (N K n : Nat) : Rat :=
  (List.range (n + 1)).foldl (fun acc k => acc + hypergeometric N K n k) 0

theorem HYPERGEOMETRIC_VALID :
    hypergeometricMass 5 2 2 = (1 : Rat) ∧
    hypergeometricMass 6 3 3 = (1 : Rat) := by
  native_decide

/-- Probability of drawing at least one target copy in `n` draws from `N`. -/
def probAtLeastOne : Nat → Nat → Nat → Rat
  | N, K, n =>
      1 - (chooseRat (N - K) n / chooseRat N n)

theorem FOUR_COPIES_RULE :
    probAtLeastOne 60 4 7 = (38962 : Rat) / (97527 : Rat) ∧
    (39 : Rat) / (100 : Rat) < probAtLeastOne 60 4 7 ∧
    probAtLeastOne 60 4 7 < (2 : Rat) / (5 : Rat) := by
  native_decide

theorem MORE_COPIES_BETTER :
    ∀ k : Fin 60,
      probAtLeastOne 60 k.1 7 <= probAtLeastOne 60 (k.1 + 1) 7 := by
  native_decide

/-- Probability of whiffing all basics in opening 7 for `B` basics. -/
def mulliganProbability (B : Nat) : Rat :=
  chooseRat (60 - B) 7 / chooseRat 60 7

theorem MULLIGAN_PROBABILITY :
    (∀ B : Nat, mulliganProbability B = chooseRat (60 - B) 7 / chooseRat 60 7) ∧
    mulliganProbability 12 = (92966 : Rat) / (487635 : Rat) := by
  constructor
  · intro B
    rfl
  · native_decide

/-- Probability of seeing at least one supporter in the opening 7. -/
def supporterTurn1Probability (S : Nat) : Rat :=
  probAtLeastOne 60 S 7

theorem SUPPORTER_TURN1 :
    (∀ S : Nat, supporterTurn1Probability S = probAtLeastOne 60 S 7) ∧
    supporterTurn1Probability 12 = (394669 : Rat) / (487635 : Rat) := by
  constructor
  · intro S
    rfl
  · native_decide

/-- Brick probability when a deck runs `consistencyCopies` interchangeable consistency cards. -/
def brickProbability (consistencyCopies : Nat) : Rat :=
  chooseRat (60 - consistencyCopies) 7 / chooseRat 60 7

/-- Probability of seeing at least one strategy card in opening 7. -/
def strategyDrawProbability (strategyCopies : Nat) : Rat :=
  probAtLeastOne 60 strategyCopies 7

/-- Adding consistency cards consumes strategy slots in a fixed 60-card deck. -/
def strategySlotsAfter (strategyBase addedConsistency : Nat) : Nat :=
  strategyBase - addedConsistency

theorem CONSISTENCY_TRADEOFF :
    ∀ k : Fin 10,
      brickProbability (12 + k.1) >= brickProbability (12 + (k.1 + 1)) ∧
      strategyDrawProbability (strategySlotsAfter 24 k.1) >=
        strategyDrawProbability (strategySlotsAfter 24 (k.1 + 1)) := by
  native_decide

/-- Score of a playable opening hand (`>=1` basic and `>=1` supporter). -/
def deckConsistencyScore : List Nat → Rat
  | [basics, supporters] =>
      let total := chooseRat 60 7
      let noBasic := chooseRat (60 - basics) 7 / total
      let noSupporter := chooseRat (60 - supporters) 7 / total
      let neither := chooseRat (60 - basics - supporters) 7 / total
      1 - noBasic - noSupporter + neither
  | _ => 0

theorem OPTIMAL_BASIC_COUNT :
    deckConsistencyScore [8, 16] = (3089576 : Rat) / (5363985 : Rat) ∧
    deckConsistencyScore [10, 14] = (182686 : Rat) / (292581 : Rat) ∧
    deckConsistencyScore [12, 12] = (3589 : Rat) / (5605 : Rat) ∧
    deckConsistencyScore [14, 10] = deckConsistencyScore [10, 14] ∧
    deckConsistencyScore [16, 8] = deckConsistencyScore [8, 16] ∧
    deckConsistencyScore [8, 16] < deckConsistencyScore [10, 14] ∧
    deckConsistencyScore [10, 14] < deckConsistencyScore [12, 12] := by
  native_decide

/-- Probability all `K` copies of a card are among the six prize cards. -/
def prizeLockProbability (K : Nat) : Rat :=
  (chooseRat K K * chooseRat (60 - K) (60 - K - 6)) / chooseRat 60 6

theorem PRIZE_LOCK_PROBABILITY :
    (∀ K : Nat,
      prizeLockProbability K =
        (chooseRat K K * chooseRat (60 - K) (60 - K - 6)) / chooseRat 60 6) ∧
    prizeLockProbability 4 = (1 : Rat) / (32509 : Rat) := by
  constructor
  · intro K
    rfl
  · native_decide

end PokemonLean.DeckConsistency
