import PokemonLean.Semantics
import PokemonLean.SemanticsDeep
import PokemonLean.Core.Types
import PokemonLean.OfficialRules

namespace PokemonLean.Simulator

open PokemonLean.Semantics

/-- A game strategy picks an action from the current game state. -/
abbrev Strategy := GameState → PokemonLean.Semantics.Action

inductive GameResult where
  | player1Wins
  | player2Wins
  | draw
  deriving Repr, BEq, DecidableEq

def defaultLegalAction (_state : GameState) : PokemonLean.Semantics.Action := .endTurn

def chosenAction (state : GameState) (strategy : Strategy) : PokemonLean.Semantics.Action :=
  let proposed := strategy state
  if Legal state proposed then proposed else defaultLegalAction state

instance instDecidableHasWon (state : GameState) (player : PlayerId) :
    Decidable (_root_.hasWon state player) := by
  unfold _root_.hasWon
  infer_instance

def simulateStep (state : GameState) (strategy : Strategy) : GameState :=
  match step state (chosenAction state strategy) with
  | .ok nextState => nextState
  | .error _ => { state with activePlayer := otherPlayer state.activePlayer }

def strategyFor (state : GameState) (player1 player2 : Strategy) : Strategy :=
  if state.activePlayer = .playerOne then player1 else player2

def simulateState (state : GameState) (player1 player2 : Strategy) : Nat → GameState
  | 0 => state
  | fuel + 1 =>
      if _root_.hasWon state .playerOne then state
      else if _root_.hasWon state .playerTwo then state
      else
        simulateState (simulateStep state (strategyFor state player1 player2)) player1 player2 fuel

def resultOfState (state : GameState) : GameResult :=
  if _root_.hasWon state .playerOne then .player1Wins
  else if _root_.hasWon state .playerTwo then .player2Wins
  else .draw

def simulate (state : GameState) (player1 player2 : Strategy) (fuel : Nat) : GameResult :=
  resultOfState (simulateState state player1 player2 fuel)

theorem defaultLegalAction_legal (state : GameState) : Legal state (defaultLegalAction state) := by
  simpa [defaultLegalAction] using legal_endTurn state

theorem chosenAction_legal (state : GameState) (strategy : Strategy) :
    Legal state (chosenAction state strategy) := by
  unfold chosenAction
  by_cases hLegal : Legal state (strategy state)
  · simp [hLegal]
  · simp [hLegal, defaultLegalAction]
    exact legal_endTurn state

theorem illegal_strategy_uses_default_via_progress
    (state : GameState) (strategy : Strategy)
    (hValid : ValidState state) (hNotOver : ¬ PokemonLean.gameOver state)
    (hIllegal : ¬ Legal state (strategy state)) :
    chosenAction state strategy = defaultLegalAction state ∧
      Legal state (chosenAction state strategy) ∧
      (∃ action, Legal state action) := by
  refine ⟨?_, ?_, progress state hValid hNotOver⟩
  · simp [chosenAction, hIllegal]
  · simpa [chosenAction, hIllegal] using defaultLegalAction_legal state

theorem simulateStep_eq_step (state : GameState) (strategy : Strategy) :
    step state (chosenAction state strategy) = .ok (simulateStep state strategy) := by
  unfold simulateStep
  cases hStep : step state (chosenAction state strategy) with
  | ok nextState =>
      simp [hStep]
  | error err =>
      have hNoError : step state (chosenAction state strategy) ≠ .error err :=
        legal_no_error state (chosenAction state strategy) err (chosenAction_legal state strategy)
      exact False.elim (hNoError hStep)

theorem simulateStep_respects_legal (state : GameState) (strategy : Strategy) :
    ∃ action, Legal state action ∧ step state action = .ok (simulateStep state strategy) := by
  refine ⟨chosenAction state strategy, chosenAction_legal state strategy, ?_⟩
  exact simulateStep_eq_step state strategy

theorem reachableFrom_trans {start mid finish : GameState}
    (hStartMid : ReachableFrom start mid) (hMidFinish : ReachableFrom mid finish) :
    ReachableFrom start finish := by
  induction hMidFinish with
  | initial =>
      simpa using hStartMid
  | step hPrev action hLegal hStep ih =>
      exact ReachableFrom.step ih action hLegal hStep

theorem simulateState_reachable (state : GameState) (player1 player2 : Strategy) (fuel : Nat) :
    ReachableFrom state (simulateState state player1 player2 fuel) := by
  induction fuel generalizing state with
  | zero =>
      simp [simulateState, ReachableFrom.initial]
  | succ fuel ih =>
      by_cases hP1 : _root_.hasWon state .playerOne
      · simp [simulateState, hP1, ReachableFrom.initial]
      · by_cases hP2 : _root_.hasWon state .playerTwo
        · simp [simulateState, hP1, hP2, ReachableFrom.initial]
        ·
          let σ := strategyFor state player1 player2
          have hStepLegal :
              ∃ action, Legal state action ∧ step state action = .ok (simulateStep state σ) :=
            simulateStep_respects_legal state σ
          rcases hStepLegal with ⟨action, hLegal, hStep⟩
          have hReachStep : ReachableFrom state (simulateStep state σ) :=
            ReachableFrom.step ReachableFrom.initial action hLegal hStep
          have hReachTail :
              ReachableFrom (simulateStep state σ)
                (simulateState (simulateStep state σ) player1 player2 fuel) :=
            ih (simulateStep state σ)
          have hReachAll : ReachableFrom state
              (simulateState (simulateStep state σ) player1 player2 fuel) :=
            reachableFrom_trans hReachStep hReachTail
          simpa [simulateState, hP1, hP2, σ] using hReachAll

theorem simulation_validity (state : GameState) (player1 player2 : Strategy) (fuel : Nat) :
    ReachableFrom state (simulateState state player1 player2 fuel) :=
  simulateState_reachable state player1 player2 fuel

theorem simulateState_preserves_card_conservation
    (state : GameState) (player1 player2 : Strategy) (fuel : Nat) :
    totalCardCount (simulateState state player1 player2 fuel) = totalCardCount state := by
  have hReach := simulateState_reachable state player1 player2 fuel
  have hConservation :
      CardConservation state (simulateState state player1 player2 fuel) :=
    reachable_preserves_total_cards state (simulateState state player1 player2 fuel) hReach
  simpa [CardConservation] using hConservation

theorem simulateState_preserves_validity
    (state : GameState) (player1 player2 : Strategy) (fuel : Nat)
    (hValid : ValidState state) :
    ValidState (simulateState state player1 player2 fuel) := by
  exact reachable_valid state hValid (simulateState state player1 player2 fuel)
    (simulateState_reachable state player1 player2 fuel)

theorem simulation_preserves_invariants
    (state : GameState) (player1 player2 : Strategy) (fuel : Nat)
    (hValid : ValidState state) :
    totalCardCount (simulateState state player1 player2 fuel) = totalCardCount state ∧
      ValidState (simulateState state player1 player2 fuel) := by
  exact
    ⟨simulateState_preserves_card_conservation state player1 player2 fuel,
      simulateState_preserves_validity state player1 player2 fuel hValid⟩

theorem simulation_terminates (state : GameState) (player1 player2 : Strategy) (fuel : Nat) :
    (∃ result, simulate state player1 player2 fuel = result) ∧
      Acc DecreasingLegalStep state := by
  refine ⟨⟨simulate state player1 player2 fuel, rfl⟩, ?_⟩
  exact game_terminates state

theorem simulation_correctness_player1
    (state : GameState) (player1 player2 : Strategy) (fuel : Nat)
    (hWin : simulate state player1 player2 fuel = .player1Wins) :
    _root_.hasWon (simulateState state player1 player2 fuel) .playerOne := by
  by_cases hP1 : _root_.hasWon (simulateState state player1 player2 fuel) .playerOne
  · exact hP1
  · by_cases hP2 : _root_.hasWon (simulateState state player1 player2 fuel) .playerTwo
    ·
      simp [simulate, resultOfState, hP1, hP2] at hWin
    ·
      simp [simulate, resultOfState, hP1, hP2] at hWin

def aggressivePlayer1 : Strategy := fun _ => .attack 0
def conservativePlayer2 : Strategy := fun _ => .endTurn

def samplePlayerOneState : PlayerState :=
  { deck := []
  , hand := []
  , bench := []
  , active := some { card := sampleCharmander, damage := 0, status := none, energy := [.fire] }
  , discard := []
  , prizes := [samplePikachu] }

def samplePlayerTwoState : PlayerState :=
  { deck := []
  , hand := []
  , bench := []
  , active := some { card := samplePikachu, damage := 50, status := none, energy := [] }
  , discard := []
  , prizes := [sampleCharmander] }

def sampleGameState : GameState :=
  { playerOne := samplePlayerOneState
  , playerTwo := samplePlayerTwoState
  , activePlayer := .playerOne }

#eval simulate sampleGameState aggressivePlayer1 conservativePlayer2 3
#eval simulateState sampleGameState aggressivePlayer1 conservativePlayer2 3

end PokemonLean.Simulator
