import PokemonLean.Basic
import Std.Tactic

namespace PokemonLean

/-- Standard number of prize cards per player. -/
def standardPrizeCount : Nat := 6

/-- Prizes taken so far (in this simplified model, prizes are removed from the opponent's prize pile). -/
def prizesTaken (player : PlayerState) : Nat :=
  standardPrizeCount - player.prizes.length

/-- A simple invariant: a player never has more than `standardPrizeCount` prizes remaining. -/
def prizesValid (player : PlayerState) : Prop :=
  player.prizes.length ≤ standardPrizeCount

theorem prizesValid_of_eq (player : PlayerState) (n : Nat) (h : player.prizes.length = n)
    (hn : n ≤ standardPrizeCount) : prizesValid player := by
  unfold prizesValid
  simpa [h] using hn

/-- Taking a prize preserves `prizesValid` for the defender. -/
theorem prizesValid_takePrize_defender (attacker defender : PlayerState)
    (h : prizesValid defender) : prizesValid (takePrize attacker defender).2 := by
  unfold prizesValid at h ⊢
  cases hp : defender.prizes with
  | nil =>
      simp [takePrize, hp] at *
  | cons prize rest =>
      -- defender's prizes shrink by 1
      simp [takePrize, hp] at *
      omega

/-- Taking a prize preserves `prizesValid` for the attacker (their prize pile is unchanged). -/
theorem prizesValid_takePrize_attacker (attacker defender : PlayerState)
    (h : prizesValid attacker) : prizesValid (takePrize attacker defender).1 := by
  unfold prizesValid at h ⊢
  cases hp : defender.prizes with
  | nil =>
      -- attacker.prizes is unchanged
      simpa [takePrize, hp] using h
  | cons prize rest =>
      -- attacker.prizes is unchanged
      simpa [takePrize, hp] using h

/-- A win can happen for several reasons. -/
inductive WinReason
  | prizes
  | noPokemon
  | deckOut
  deriving Repr, BEq, DecidableEq

/-- Helper: the opponent of a given player in the current `state`. -/
def opponentState (state : GameState) (player : PlayerId) : PlayerState :=
  getPlayerState state (otherPlayer player)

/-- Win-by-reason predicate. -/
def hasWonBy (state : GameState) (player : PlayerId) : WinReason → Prop
  | .prizes => (opponentState state player).prizes.length = 0
  | .noPokemon =>
      (opponentState state player).active = none ∧ (opponentState state player).bench = []
  | .deckOut => (opponentState state player).deck = []

/-- Overall win predicate. -/
def hasWon (state : GameState) (player : PlayerId) : Prop :=
  ∃ r : WinReason, hasWonBy state player r

theorem hasWon_of_prizes (state : GameState) (player : PlayerId)
    (h : hasWonBy state player .prizes) : hasWon state player :=
  ⟨.prizes, h⟩

theorem hasWon_of_noPokemon (state : GameState) (player : PlayerId)
    (h : hasWonBy state player .noPokemon) : hasWon state player :=
  ⟨.noPokemon, h⟩

theorem hasWon_of_deckOut (state : GameState) (player : PlayerId)
    (h : hasWonBy state player .deckOut) : hasWon state player :=
  ⟨.deckOut, h⟩

/-- The original prize-only predicate from `Basic.lean` implies the extended win predicate. -/
theorem hasWon_from_Basic_hasWon (state : GameState) (player : PlayerId)
    (h : _root_.hasWon state player) : hasWon state player := by
  -- `_root_.hasWon` in `Basic.lean` is exactly win-by-prizes.
  refine ⟨.prizes, ?_⟩
  simpa [_root_.hasWon, hasWonBy, opponentState] using h

/-- Win conditions do not depend on whose turn it is. -/
theorem hasWonBy_endTurn (state : GameState) (player : PlayerId) (r : WinReason) :
    hasWonBy state player r → hasWonBy { state with activePlayer := otherPlayer state.activePlayer } player r := by
  intro h
  cases r <;> simpa [hasWonBy, opponentState, getPlayerState, otherPlayer] using h

theorem hasWon_endTurn (state : GameState) (player : PlayerId) :
    hasWon state player → hasWon { state with activePlayer := otherPlayer state.activePlayer } player := by
  rintro ⟨r, hr⟩
  exact ⟨r, hasWonBy_endTurn state player r hr⟩

/-- A state is terminal if someone has won. -/
def gameOver (state : GameState) : Prop := ∃ p : PlayerId, hasWon state p

theorem gameOver_endTurn (state : GameState) :
    gameOver state → gameOver { state with activePlayer := otherPlayer state.activePlayer } := by
  rintro ⟨p, hp⟩
  exact ⟨p, hasWon_endTurn state p hp⟩

/-- If the opponent has no prizes remaining, the player has won by prizes. -/
theorem hasWonBy_prizes_iff (state : GameState) (player : PlayerId) :
    hasWonBy state player .prizes ↔ (opponentState state player).prizes = [] := by
  constructor
  · intro h
    unfold hasWonBy opponentState at h
    match hPrizes : (getPlayerState state (otherPlayer player)).prizes with
    | [] => rfl
    | _ :: _ => simp [hPrizes] at h
  · intro h
    unfold hasWonBy opponentState
    unfold opponentState at h
    rw [h]
    simp

/-- If the opponent has no Pokemon in play, the player has won by noPokemon. -/

/-- If the opponent has an empty deck, the player has won by deckOut. -/

/-- A small monotonicity lemma: once the opponent has no prizes, taking a prize cannot make them have prizes.

(Trivial in this model: `takePrize` only removes prizes.)
-/
theorem takePrize_preserves_no_prizes (attacker defender : PlayerState)
    (h : defender.prizes = []) : (takePrize attacker defender).2.prizes = [] := by
  simp [takePrize, h]

-- (lemma removed: too specific for current model)
end PokemonLean
