import PokemonLean.Semantics
import PokemonLean.Win
import Std.Tactic

namespace PokemonLean.Semantics

open PokemonLean

theorem progress (gs : GameState) :
    ValidState gs → ¬ PokemonLean.gameOver gs → ∃ a, Legal gs a := by
  intro _ _
  exact ⟨.endTurn, legal_endTurn gs⟩

theorem step_total (gs : GameState) (a : Action) :
    ∃ r : Except StepError GameState, step gs a = r := by
  exact ⟨step gs a, rfl⟩

theorem step_total_function (gs : GameState) (a : Action) :
    ∃ r : Except StepError GameState, step gs a = r ∧
      ∀ r' : Except StepError GameState, step gs a = r' → r' = r := by
  refine ⟨step gs a, rfl, ?_⟩
  intro r' hr'
  simp [hr']

theorem step_determinism_explicit (gs : GameState) (a : Action) (s1 s2 : GameState)
    (h1 : step gs a = .ok s1) (h2 : step gs a = .ok s2) : s1 = s2 := by
  exact step_deterministic gs a s1 s2 h1 h2

inductive TurnPhase
  | draw
  | main
  | attack
  | betweenTurns
  deriving Repr, BEq, DecidableEq

inductive MainPhaseAction : Action → Prop
  | playPokemonToBench (card : Card) : MainPhaseAction (.playPokemonToBench card)
  | playItem (card : Card) : MainPhaseAction (.playItem card)
  | playSupporter (card : Card) : MainPhaseAction (.playSupporter card)
  | playTool (card : Card) : MainPhaseAction (.playTool card)
  | playSupporterDraw (card : Card) (count : Nat) : MainPhaseAction (.playSupporterDraw card count)
  | playItemHeal (card : Card) (amount : Nat) : MainPhaseAction (.playItemHeal card amount)
  | evolveActive (card : Card) : MainPhaseAction (.evolveActive card)
  | useAbilityHeal (amount : Nat) : MainPhaseAction (.useAbilityHeal amount)
  | useAbilityDraw (count : Nat) : MainPhaseAction (.useAbilityDraw count)
  | attachEnergy (energyType : EnergyType) : MainPhaseAction (.attachEnergy energyType)
  | retreat : MainPhaseAction .retreat

inductive AttackPhaseAction : Action → Prop
  | attack (attackIndex : Nat) : AttackPhaseAction (.attack attackIndex)
  | endTurn : AttackPhaseAction .endTurn

inductive MainPhaseSeq : List Action → Prop
  | nil : MainPhaseSeq []
  | cons {a : Action} {rest : List Action}
      (hMain : MainPhaseAction a) (hRest : MainPhaseSeq rest) :
      MainPhaseSeq (a :: rest)

theorem mainPhaseSeq_mem {actions : List Action} :
    MainPhaseSeq actions → ∀ a, a ∈ actions → MainPhaseAction a := by
  intro hSeq
  induction hSeq with
  | nil =>
      intro a hMem
      cases hMem
  | cons hMain hRest ih =>
      intro a hMem
      simp at hMem
      rcases hMem with rfl | hTail
      · exact hMain
      · exact ih a hTail

structure CompleteTurn (start finish : GameState) where
  afterDraw : GameState
  afterMain : GameState
  mainActions : List Action
  finisher : Action
  drawStep : step start .drawCard = .ok afterDraw
  mainSeq : MainPhaseSeq mainActions
  mainRun : stepMany afterDraw mainActions = .ok afterMain
  finisherPhase : AttackPhaseAction finisher
  finisherStep : step afterMain finisher = .ok finish

theorem completeTurn_phase_order
    {start finish : GameState} (hTurn : CompleteTurn start finish) :
    Legal start .drawCard ∧
      (∀ a, a ∈ hTurn.mainActions → MainPhaseAction a) ∧
      AttackPhaseAction hTurn.finisher ∧
      Legal hTurn.afterMain hTurn.finisher := by
  refine ⟨?_, ?_, hTurn.finisherPhase, ?_⟩
  · exact ⟨hTurn.afterDraw, hTurn.drawStep⟩
  · intro a hMem
    exact mainPhaseSeq_mem hTurn.mainSeq a hMem
  · exact ⟨finish, hTurn.finisherStep⟩

theorem completeTurn_betweenTurns
    {start finish : GameState} (hTurn : CompleteTurn start finish) :
    finish.activePlayer = otherPlayer hTurn.afterMain.activePlayer := by
  rcases hTurn with ⟨afterDraw, afterMain, mainActions, finisher, drawStep, mainSeq, mainRun, finisherPhase, finisherStep⟩
  cases finisherPhase with
  | attack attackIndex =>
      simpa using step_activePlayer_attack afterMain attackIndex finish finisherStep
  | endTurn =>
      simpa using step_activePlayer_endTurn afterMain finish finisherStep

def totalPrizes (gs : GameState) : Nat :=
  gs.playerOne.prizes.length + gs.playerTwo.prizes.length

def totalDeckSize (gs : GameState) : Nat :=
  gs.playerOne.deck.length + gs.playerTwo.deck.length

def gameMeasure (gs : GameState) : Nat :=
  totalPrizes gs + totalDeckSize gs

theorem takePrize_totalPrizes_decrease (attacker defender : PlayerState)
    (hNonempty : defender.prizes ≠ []) :
    (takePrize attacker defender).1.prizes.length + (takePrize attacker defender).2.prizes.length <
      attacker.prizes.length + defender.prizes.length := by
  have hAtk : (takePrize attacker defender).1.prizes.length = attacker.prizes.length :=
    takePrize_attacker_prizes_length_eq attacker defender
  have hDef : (takePrize attacker defender).2.prizes.length + 1 = defender.prizes.length :=
    takePrize_prizes_length_succ attacker defender hNonempty
  omega

theorem step_drawCard_totalDeckSize_succ (gs gs' : GameState)
    (hStep : step gs .drawCard = .ok gs') :
    totalDeckSize gs' + 1 = totalDeckSize gs := by
  cases hPlayer : gs.activePlayer <;>
    simp [step, hPlayer, getPlayerState] at hStep
  · cases hDeck : gs.playerOne.deck with
    | nil =>
        simp [hDeck] at hStep
    | cons top rest =>
        simp [hDeck, setPlayerState] at hStep
        cases hStep
        simp [totalDeckSize, hPlayer, hDeck, getPlayerState, setPlayerState]
        omega
  · cases hDeck : gs.playerTwo.deck with
    | nil =>
        simp [hDeck] at hStep
    | cons top rest =>
        simp [hDeck, setPlayerState] at hStep
        cases hStep
        simp [totalDeckSize, hPlayer, hDeck, getPlayerState, setPlayerState]
        omega

theorem step_drawCard_measure_decreases (gs gs' : GameState)
    (hStep : step gs .drawCard = .ok gs') :
    gameMeasure gs' < gameMeasure gs := by
  have hDeckSucc : totalDeckSize gs' + 1 = totalDeckSize gs :=
    step_drawCard_totalDeckSize_succ gs gs' hStep
  have hDeckLt : totalDeckSize gs' < totalDeckSize gs := by
    omega
  have hPrizesPair := step_prizes_nonincreasing gs .drawCard gs' hStep
  have hPrizesLe : totalPrizes gs' ≤ totalPrizes gs := by
    unfold totalPrizes
    exact Nat.add_le_add hPrizesPair.1 hPrizesPair.2
  unfold gameMeasure
  omega

def DecreasingLegalStep (next current : GameState) : Prop :=
  ∃ a, Legal current a ∧ step current a = .ok next ∧ gameMeasure next < gameMeasure current

theorem drawCard_decreasingLegalStep (gs gs' : GameState)
    (hStep : step gs .drawCard = .ok gs') :
    DecreasingLegalStep gs' gs := by
  refine ⟨.drawCard, ?_, hStep, step_drawCard_measure_decreases gs gs' hStep⟩
  exact ⟨gs', hStep⟩

theorem decreasingLegalStep_wf : WellFounded DecreasingLegalStep := by
  refine Subrelation.wf (q := DecreasingLegalStep) (r := (measure gameMeasure).rel) ?_ (measure gameMeasure).wf
  intro next current hStep
  rcases hStep with ⟨a, hLegal, hStepEq, hMeasure⟩
  exact hMeasure

theorem game_terminates (gs : GameState) : Acc DecreasingLegalStep gs :=
  decreasingLegalStep_wf.apply gs

end PokemonLean.Semantics
