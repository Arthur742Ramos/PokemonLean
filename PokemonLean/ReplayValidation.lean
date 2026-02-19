import PokemonLean.Semantics
import PokemonLean.SemanticsDeep
import PokemonLean.OfficialRules
import PokemonLean.Core.Types

namespace PokemonLean.ReplayValidation

open PokemonLean.Semantics

abbrev GameLog := List PokemonLean.Semantics.Action

instance hasWonDecidable (gs : GameState) (player : PlayerId) : Decidable (_root_.hasWon gs player) := by
  unfold _root_.hasWon
  infer_instance

def validateReplay : GameState → GameLog → Bool
  | _, [] => true
  | gs, action :: rest =>
      match step gs action with
      | .ok nextState => validateReplay nextState rest
      | .error _ => false

def ReplayValid : GameState → GameLog → Prop
  | _, [] => True
  | gs, action :: rest =>
      ∃ nextState,
        Legal gs action ∧
          step gs action = .ok nextState ∧
          ReplayValid nextState rest

theorem SOUNDNESS {gs : GameState} {log : GameLog} :
    validateReplay gs log = true → ReplayValid gs log := by
  induction log generalizing gs with
  | nil =>
      intro _
      simp [validateReplay, ReplayValid]
  | cons action rest ih =>
      intro hValidate
      cases hStep : step gs action with
      | error err =>
          simp [validateReplay, hStep] at hValidate
      | ok nextState =>
          have hTail : validateReplay nextState rest = true := by
            simpa [validateReplay, hStep] using hValidate
          exact ⟨nextState, ⟨nextState, hStep⟩, hStep, ih hTail⟩

theorem COMPLETENESS {gs : GameState} {log : GameLog} :
    ReplayValid gs log → validateReplay gs log = true := by
  induction log generalizing gs with
  | nil =>
      intro _
      simp [validateReplay, ReplayValid]
  | cons action rest ih =>
      intro hReplay
      rcases hReplay with ⟨nextState, _hLegal, hStep, hTail⟩
      simp [validateReplay, hStep]
      exact ih hTail

theorem validateReplay_eq_true_iff_replayValid (gs : GameState) (log : GameLog) :
    validateReplay gs log = true ↔ ReplayValid gs log := by
  constructor
  · exact SOUNDNESS
  · exact COMPLETENESS

def replayIntermediateStates : GameState → GameLog → List GameState
  | gs, [] => [gs]
  | gs, action :: rest =>
      match step gs action with
      | .ok nextState => gs :: replayIntermediateStates nextState rest
      | .error _ => [gs]

theorem REPLAY_INVARIANTS {gs : GameState} {log : GameLog} (hReplay : ReplayValid gs log) :
    ∀ s, s ∈ replayIntermediateStates gs log → totalCardCount s = totalCardCount gs := by
  induction log generalizing gs with
  | nil =>
      intro s hs
      simp [replayIntermediateStates] at hs
      simp [hs]
  | cons action rest ih =>
      rcases hReplay with ⟨nextState, _hLegal, hStep, hTail⟩
      intro s hs
      simp [replayIntermediateStates, hStep] at hs
      rcases hs with rfl | hsTail
      · rfl
      · have hTailCards : totalCardCount s = totalCardCount nextState :=
          ih hTail s hsTail
        have hStepCards : totalCardCount nextState = totalCardCount gs :=
          step_preserves_total_cards gs action nextState hStep
        exact hTailCards.trans hStepCards

def replayFinalState : GameState → GameLog → Option GameState
  | gs, [] => some gs
  | gs, action :: rest =>
      match step gs action with
      | .ok nextState => replayFinalState nextState rest
      | .error _ => none

theorem replayFinalState_isSome_eq_validateReplay (gs : GameState) (log : GameLog) :
    (replayFinalState gs log).isSome = validateReplay gs log := by
  induction log generalizing gs with
  | nil =>
      simp [replayFinalState, validateReplay]
  | cons action rest ih =>
      cases hStep : step gs action <;>
        simp [replayFinalState, validateReplay, hStep, ih]

theorem replayFinalState_some_iff_validateReplay_true (gs : GameState) (log : GameLog) :
    (∃ finalState, replayFinalState gs log = some finalState) ↔ validateReplay gs log = true := by
  constructor
  · intro hSome
    have hSomeProp : (replayFinalState gs log).isSome := Option.isSome_iff_exists.mpr hSome
    have hSomeBool : (replayFinalState gs log).isSome = true := by
      simpa using hSomeProp
    simpa [replayFinalState_isSome_eq_validateReplay gs log] using hSomeBool
  · intro hValidate
    have hSomeBool : (replayFinalState gs log).isSome = true := by
      simpa [replayFinalState_isSome_eq_validateReplay gs log] using hValidate
    have hSomeProp : (replayFinalState gs log).isSome := by
      simpa using hSomeBool
    exact Option.isSome_iff_exists.mp hSomeProp

def winnerFromState (gs : GameState) : Option PlayerId :=
  if _ : _root_.hasWon gs .playerOne then
    some .playerOne
  else if _ : _root_.hasWon gs .playerTwo then
    some .playerTwo
  else
    none

def replayWinner (gs : GameState) (log : GameLog) : Option PlayerId :=
  match replayFinalState gs log with
  | some finalState => winnerFromState finalState
  | none => none

theorem winnerFromState_detects (gs : GameState) :
    (∃ p, _root_.hasWon gs p) →
      ∃ p, winnerFromState gs = some p ∧ _root_.hasWon gs p := by
  intro hWinner
  rcases hWinner with ⟨p, hp⟩
  cases p with
  | playerOne =>
      exact ⟨.playerOne, by simp [winnerFromState, hp], hp⟩
  | playerTwo =>
      by_cases hOne : _root_.hasWon gs .playerOne
      · exact ⟨.playerOne, by simp [winnerFromState, hOne], hOne⟩
      · exact ⟨.playerTwo, by simp [winnerFromState, hOne, hp], hp⟩

theorem REPLAY_WIN_DETECTION {gs : GameState} {log : GameLog} {finalState : GameState}
    (hReplay : ReplayValid gs log)
    (hFinal : replayFinalState gs log = some finalState)
    (hWinner : ∃ p, _root_.hasWon finalState p) :
    ∃ p, replayWinner gs log = some p ∧ _root_.hasWon finalState p := by
  have _ : validateReplay gs log = true := COMPLETENESS hReplay
  rcases winnerFromState_detects finalState hWinner with ⟨p, hDetect, hHasWon⟩
  exact ⟨p, by simpa [replayWinner, hFinal] using hDetect, hHasWon⟩

def replayExamplePlayerOne : PlayerState :=
  { deck := [samplePikachu, samplePikachu]
  , hand := []
  , bench := []
  , active := some (toPokemonInPlay samplePikachu)
  , discard := []
  , prizes := List.replicate _root_.standardPrizeCount samplePikachu }

def replayExamplePlayerTwo : PlayerState :=
  { deck := [sampleCharmander]
  , hand := []
  , bench := []
  , active := some (toPokemonInPlay sampleCharmander)
  , discard := []
  , prizes := List.replicate _root_.standardPrizeCount sampleCharmander }

def replayExampleState : GameState :=
  { playerOne := replayExamplePlayerOne
  , playerTwo := replayExamplePlayerTwo
  , activePlayer := .playerOne }

def replayExampleLog : GameLog :=
  [ .drawCard
  , .attachEnergy .lightning
  , .attack 0
  , .drawCard
  , .attachEnergy .fire
  , .attack 0
  , .drawCard
  , .attachEnergy .lightning
  , .attack 0
  ]

#eval validateReplay replayExampleState replayExampleLog

theorem replayExample_validate_true :
    validateReplay replayExampleState replayExampleLog = true := by
  native_decide

theorem replayExample_valid : ReplayValid replayExampleState replayExampleLog :=
  SOUNDNESS replayExample_validate_true

end PokemonLean.ReplayValidation
