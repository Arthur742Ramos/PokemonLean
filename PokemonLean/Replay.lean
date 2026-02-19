-- Game Trace / Replay System
-- PokemonLean: Trace recording, replay, determinism, prize monotonicity, win detection

import PokemonLean.Basic
import PokemonLean.Semantics

namespace PokemonLean.Replay

-- ============================================================================
-- TRACE TYPES
-- ============================================================================

/-- A single step in a game trace: the action taken and the resulting state. -/
structure TraceStep where
  action : PokemonLean.Semantics.Action
  resultState : GameState
  deriving Repr, BEq, DecidableEq

/-- A game trace is a list of steps, with the initial state recorded separately. -/
structure Trace where
  initialState : GameState
  steps : List TraceStep
  deriving Repr, BEq, DecidableEq

/-- The length of a trace (number of steps). -/
def traceLength (t : Trace) : Nat := t.steps.length

@[simp] theorem traceLength_mk (init : GameState) (steps : List TraceStep) :
    traceLength { initialState := init, steps := steps } = steps.length := rfl

/-- Empty trace (no actions taken). -/
def emptyTrace (init : GameState) : Trace :=
  { initialState := init, steps := [] }

@[simp] theorem emptyTrace_length (init : GameState) :
    traceLength (emptyTrace init) = 0 := rfl

@[simp] theorem emptyTrace_initialState (init : GameState) :
    (emptyTrace init).initialState = init := rfl

@[simp] theorem emptyTrace_steps (init : GameState) :
    (emptyTrace init).steps = [] := rfl

-- ============================================================================
-- EXTRACTING ACTIONS AND STATES
-- ============================================================================

/-- Extract the list of actions from a trace. -/
def traceActions (t : Trace) : List PokemonLean.Semantics.Action :=
  t.steps.map (fun s => s.action)

/-- Extract the list of resulting states from a trace (not including initial). -/
def traceStates (t : Trace) : List GameState :=
  t.steps.map (fun s => s.resultState)

/-- The final state of a trace: the last resultState, or the initial state if empty. -/
def finalState (t : Trace) : GameState :=
  match t.steps.getLast? with
  | some s => s.resultState
  | none => t.initialState

theorem finalState_empty (init : GameState) :
    finalState (emptyTrace init) = init := by
  simp [finalState, emptyTrace]

theorem traceActions_length (t : Trace) :
    (traceActions t).length = traceLength t := by
  simp [traceActions, traceLength]

theorem traceStates_length (t : Trace) :
    (traceStates t).length = traceLength t := by
  simp [traceStates, traceLength]

-- ============================================================================
-- STATE AT INDEX
-- ============================================================================

/-- Get the state before the i-th step (0-indexed). -/
def stateBeforeStep (t : Trace) (i : Nat) : GameState :=
  match i with
  | 0 => t.initialState
  | n + 1 =>
    match t.steps[n]? with
    | some s => s.resultState
    | none => t.initialState


-- ============================================================================
-- VALID TRACE PREDICATE
-- ============================================================================

/-- A single step is valid if applying the action to the prior state via `step`
    produces the recorded result state. -/
def validStep (prior : GameState) (ts : TraceStep) : Prop :=
  PokemonLean.Semantics.step prior ts.action = .ok ts.resultState

/-- Helper: valid steps starting from a given state. -/
def validSteps : GameState → List TraceStep → Prop
  | _, [] => True
  | prior, ts :: rest => validStep prior ts ∧ validSteps ts.resultState rest

/-- A trace is valid if every step is a legal transition from the previous state. -/
def validTrace (t : Trace) : Prop :=
  validSteps t.initialState t.steps

theorem validTrace_empty (init : GameState) : validTrace (emptyTrace init) := by
  simp [validTrace, validSteps, emptyTrace]

theorem validTrace_singleton (init : GameState) (ts : TraceStep) (h : validStep init ts) :
    validTrace { initialState := init, steps := [ts] } := by
  exact ⟨h, trivial⟩

-- ============================================================================
-- REPLAY FUNCTION
-- ============================================================================

/-- Replay a list of actions from a given state, producing the resulting states. -/
def replayActions (init : GameState) :
    List PokemonLean.Semantics.Action → Option (List GameState)
  | [] => some []
  | a :: as =>
    match PokemonLean.Semantics.step init a with
    | .ok next =>
      match replayActions next as with
      | some rest => some (next :: rest)
      | none => none
    | .error _ => none


theorem replayActions_cons_ok (init : GameState) (a : PokemonLean.Semantics.Action)
    (as : List PokemonLean.Semantics.Action) (next : GameState) (rest : List GameState)
    (hStep : PokemonLean.Semantics.step init a = .ok next)
    (hRest : replayActions next as = some rest) :
    replayActions init (a :: as) = some (next :: rest) := by
  simp [replayActions, hStep, hRest]

theorem replayActions_cons_err (init : GameState) (a : PokemonLean.Semantics.Action)
    (as : List PokemonLean.Semantics.Action)
    (e : PokemonLean.Semantics.StepError)
    (hStep : PokemonLean.Semantics.step init a = .error e) :
    replayActions init (a :: as) = none := by
  simp [replayActions, hStep]

/-- Length of replayed states equals length of actions (when successful). -/
theorem replayActions_length (init : GameState)
    (actions : List PokemonLean.Semantics.Action)
    (states : List GameState)
    (h : replayActions init actions = some states) :
    states.length = actions.length := by
  induction actions generalizing init states with
  | nil =>
    simp [replayActions] at h; simp [h]
  | cons a as ih =>
    simp [replayActions] at h
    split at h
    · rename_i next hStep
      split at h
      · rename_i rest hRest
        simp at h; subst h
        simp [ih next rest hRest]
      · simp at h
    · simp at h

-- ============================================================================
-- TRACE CONSTRUCTION FROM REPLAY
-- ============================================================================

/-- Build a trace from an initial state and matching action/state lists. -/
def buildTrace (init : GameState) (actions : List PokemonLean.Semantics.Action)
    (states : List GameState) : Trace :=
  { initialState := init
  , steps := List.zipWith (fun a s => { action := a, resultState := s }) actions states }

theorem buildTrace_length (init : GameState) (actions : List PokemonLean.Semantics.Action)
    (states : List GameState) (h : actions.length = states.length) :
    traceLength (buildTrace init actions states) = actions.length := by
  simp [buildTrace, traceLength, List.length_zipWith, h]

-- ============================================================================
-- DETERMINISM
-- ============================================================================

/-- The step function is deterministic: same input gives same output. -/

/-- Replay is deterministic: same actions from same state produce same states. -/
theorem replayActions_deterministic (init : GameState)
    (actions : List PokemonLean.Semantics.Action)
    (states1 states2 : List GameState)
    (h1 : replayActions init actions = some states1)
    (h2 : replayActions init actions = some states2) :
    states1 = states2 := by
  rw [h1] at h2
  exact Option.some.inj h2

/-- Two valid traces with the same initial state and same actions produce the same steps. -/
theorem trace_deterministic (t1 t2 : Trace)
    (hInit : t1.initialState = t2.initialState)
    (hActions : traceActions t1 = traceActions t2)
    (hValid1 : validTrace t1) (hValid2 : validTrace t2) :
    t1.steps = t2.steps := by
  cases t1 with | mk init1 steps1 =>
  cases t2 with | mk init2 steps2 =>
  simp at hInit; subst hInit
  simp [traceActions] at hActions
  -- Prove steps are equal by induction
  have : ∀ (init : GameState) (s1 s2 : List TraceStep),
      validSteps init s1 → validSteps init s2 →
      s1.map TraceStep.action = s2.map TraceStep.action → s1 = s2 := by
    intro init s1
    induction s1 generalizing init with
    | nil =>
      intro s2 _ _ hMap; simp at hMap; exact hMap.symm
    | cons ts1 rest1 ih =>
      intro s2 hv1 hv2 hMap
      cases s2 with
      | nil => simp at hMap
      | cons ts2 rest2 =>
        simp at hMap
        obtain ⟨hActEq, hRestMap⟩ := hMap
        obtain ⟨hvs1, hvr1⟩ := hv1
        obtain ⟨hvs2, hvr2⟩ := hv2
        have hStateEq : ts1.resultState = ts2.resultState := by
          have h1 : PokemonLean.Semantics.step init ts1.action = .ok ts1.resultState := hvs1
          have h2 : PokemonLean.Semantics.step init ts2.action = .ok ts2.resultState := hvs2
          rw [hActEq] at h1
          exact step_deterministic init ts2.action ts1.resultState ts2.resultState h1 h2
        have hTsEq : ts1 = ts2 := by
          cases ts1 with | mk a1 r1 =>
          cases ts2 with | mk a2 r2 =>
          simp at hActEq hStateEq
          simp [hActEq, hStateEq]
        rw [hTsEq]; congr 1
        rw [hTsEq] at hvr1
        exact ih ts2.resultState rest2 hvr1 hvr2 hRestMap
  exact this init1 steps1 steps2 hValid1 hValid2 hActions

-- ============================================================================
-- PRIZE COUNT ALONG TRACE
-- ============================================================================

/-- Get a specific player's prize count from a game state. -/
def prizeCountOf (state : GameState) (player : PlayerId) : Nat :=
  (getPlayerState state player).prizes.length

/-- Extract prize counts along a trace for a given player. -/
def prizeCounts (t : Trace) (player : PlayerId) : List Nat :=
  prizeCountOf t.initialState player ::
    t.steps.map (fun s => prizeCountOf s.resultState player)

theorem prizeCounts_length (t : Trace) (player : PlayerId) :
    (prizeCounts t player).length = traceLength t + 1 := by
  simp [prizeCounts, traceLength]

theorem prizeCounts_head (t : Trace) (player : PlayerId) :
    (prizeCounts t player).head? = some (prizeCountOf t.initialState player) := by
  simp [prizeCounts]

/-- End turn does not change prize counts. -/
theorem endTurn_prizeCount (state : GameState) (player : PlayerId)
    (next : GameState) (h : PokemonLean.Semantics.step state .endTurn = .ok next) :
    prizeCountOf next player = prizeCountOf state player := by
  simp [PokemonLean.Semantics.step] at h; cases h
  cases player <;> cases state.activePlayer <;> simp [prizeCountOf, getPlayerState]

/-- Drawing a card does not change prize counts. -/
theorem drawCard_prizeCount (state : GameState) (player : PlayerId)
    (next : GameState) (h : PokemonLean.Semantics.step state .drawCard = .ok next) :
    prizeCountOf next player = prizeCountOf state player := by
  simp [PokemonLean.Semantics.step] at h
  split at h <;> simp_all
  cases h
  cases player <;> cases state.activePlayer <;> simp [prizeCountOf, getPlayerState, setPlayerState]

/-- Attach energy does not change prize counts. -/
theorem attachEnergy_prizeCount (state : GameState) (e : EnergyType) (player : PlayerId)
    (next : GameState) (h : PokemonLean.Semantics.step state (.attachEnergy e) = .ok next) :
    prizeCountOf next player = prizeCountOf state player := by
  simp [PokemonLean.Semantics.step] at h
  split at h
  · cases h
  · cases h
    cases player <;> cases state.activePlayer <;> simp [prizeCountOf, getPlayerState, setPlayerState]

/-- Playing a Pokémon to bench does not change prize counts. -/
theorem playPokemon_prizeCount (state : GameState) (card : Card) (player : PlayerId)
    (next : GameState)
    (h : PokemonLean.Semantics.step state (.playPokemonToBench card) = .ok next) :
    prizeCountOf next player = prizeCountOf state player := by
  simp [PokemonLean.Semantics.step] at h
  split at h
  · cases h
  · split at h
    · cases h
      cases player <;> cases state.activePlayer <;> simp [prizeCountOf, getPlayerState, setPlayerState]
    · cases h

-- ============================================================================
-- NON-ATTACK ACTIONS CLASSIFICATION
-- ============================================================================

/-- A non-attack, non-retreat action. -/
def isNonCombatAction : PokemonLean.Semantics.Action → Bool
  | .endTurn => true
  | .drawCard => true
  | .attachEnergy _ => true
  | .playPokemonToBench _ => true
  | .playItem _ => true
  | .playSupporter _ => true
  | .playTool _ => true
  | .playSupporterDraw _ _ => true
  | .playItemHeal _ _ => true
  | .evolveActive _ => true
  | .useAbilityHeal _ => true
  | .useAbilityDraw _ => true
  | .attack _ => false
  | .retreat => false

-- ============================================================================
-- TRACE LENGTH BOUNDS
-- ============================================================================

/-- A trace with n steps has exactly n actions. -/
theorem trace_actions_eq_steps (t : Trace) :
    (traceActions t).length = t.steps.length := by
  simp [traceActions]

/-- Empty trace has zero length. -/
theorem trace_length_zero_iff_empty (t : Trace) :
    traceLength t = 0 ↔ t.steps = [] := by
  simp [traceLength]

/-- Appending a step increases trace length by 1. -/
theorem trace_length_append_step (t : Trace) (ts : TraceStep) :
    traceLength { t with steps := t.steps ++ [ts] } = traceLength t + 1 := by
  simp [traceLength]

-- ============================================================================
-- WIN DETECTION IN TRACE
-- ============================================================================

/-- Check if any state in the trace is a win for a given player (by prizes = 0). -/
def hasWinInTrace (t : Trace) (player : PlayerId) : Prop :=
  ∃ s ∈ t.steps, (getPlayerState s.resultState (otherPlayer player)).prizes.length = 0

/-- Check if any state in the trace has a given player with no Pokémon. -/
def hasNoPokemonLoss (t : Trace) (loser : PlayerId) : Prop :=
  ∃ s ∈ t.steps,
    (getPlayerState s.resultState loser).active = none ∧
    (getPlayerState s.resultState loser).bench = []

theorem no_win_in_empty_trace (init : GameState) (player : PlayerId) :
    ¬hasWinInTrace (emptyTrace init) player := by
  simp [hasWinInTrace, emptyTrace]

theorem no_loss_in_empty_trace (init : GameState) (player : PlayerId) :
    ¬hasNoPokemonLoss (emptyTrace init) player := by
  simp [hasNoPokemonLoss, emptyTrace]

/-- If a trace has a win at some step, extending the trace preserves that win. -/
theorem win_preserved_by_extension (t : Trace) (player : PlayerId) (ts : TraceStep)
    (h : hasWinInTrace t player) :
    hasWinInTrace { t with steps := t.steps ++ [ts] } player := by
  obtain ⟨s, hs, hwin⟩ := h
  exact ⟨s, List.mem_append_left _ hs, hwin⟩

-- ============================================================================
-- TRACE CONSISTENCY
-- ============================================================================

/-- The final state of a trace with appended step is that step's result. -/
theorem finalState_of_append (init : GameState) (rest : List TraceStep) (ts : TraceStep) :
    finalState { initialState := init, steps := rest ++ [ts] } = ts.resultState := by
  simp [finalState]

/-- Dropping the first step of a valid trace yields a valid trace. -/
theorem valid_trace_tail (init : GameState) (ts : TraceStep) (rest : List TraceStep)
    (hv : validTrace { initialState := init, steps := ts :: rest }) :
    validTrace { initialState := ts.resultState, steps := rest } := by
  exact hv.2

/-- Prefix of a valid trace is valid. -/
theorem valid_trace_take (init : GameState) (steps : List TraceStep) (n : Nat)
    (hv : validTrace { initialState := init, steps := steps }) :
    validTrace { initialState := init, steps := steps.take n } := by
  induction steps generalizing init n with
  | nil => simp [validTrace, validSteps]
  | cons ts rest ih =>
    cases n with
    | zero => simp [validTrace, validSteps]
    | succ n =>
      simp [List.take]
      exact ⟨hv.1, ih ts.resultState n hv.2⟩

/-- The number of prize-count entries is one more than the trace length. -/
theorem trace_state_count (t : Trace) :
    (prizeCounts t .playerOne).length = traceLength t + 1 :=
  prizeCounts_length t .playerOne

-- ============================================================================
-- ADDITIONAL TRACE THEOREMS
-- ============================================================================

/-- Extracting actions from an empty trace gives empty list. -/

/-- Extracting states from an empty trace gives empty list. -/

/-- A single-step valid trace's final state is the result of applying the action. -/
theorem single_step_trace_state (init : GameState) (a : PokemonLean.Semantics.Action)
    (next : GameState) :
    finalState { initialState := init, steps := [{ action := a, resultState := next }] } =
      next := by
  simp [finalState]

/-- Loss preserved by extension. -/
theorem loss_preserved_by_extension (t : Trace) (loser : PlayerId) (ts : TraceStep)
    (h : hasNoPokemonLoss t loser) :
    hasNoPokemonLoss { t with steps := t.steps ++ [ts] } loser := by
  obtain ⟨s, hs, hwin⟩ := h
  exact ⟨s, List.mem_append_left _ hs, hwin⟩

/-- A valid trace can be extended if the next action is legal. -/
theorem valid_trace_extend_aux :
    ∀ (init : GameState) (steps : List TraceStep)
      (a : PokemonLean.Semantics.Action) (next : GameState),
    validSteps init steps →
    PokemonLean.Semantics.step
      (match steps.getLast? with | some s => s.resultState | none => init) a = .ok next →
    validSteps init (steps ++ [{ action := a, resultState := next }]) := by
  intro init steps
  induction steps generalizing init with
  | nil =>
    intro a next _ hStep
    simp at hStep
    exact ⟨hStep, trivial⟩
  | cons ts rest ih =>
    intro a next hv hStep
    obtain ⟨hvs, hvr⟩ := hv
    constructor
    · exact hvs
    · apply ih ts.resultState a next hvr
      -- Need to show the step hypothesis holds with rest's getLast?
      -- hStep : step (match (ts :: rest).getLast? ...) a = .ok next
      -- (ts :: rest).getLast? = if rest = [] then some ts else rest.getLast?
      -- We need: step (match rest.getLast? ...) a = .ok next
      -- where the fallback init is ts.resultState
      cases hRest : rest.getLast? with
      | none =>
        -- rest.getLast? = none means rest = []
        have hRestNil : rest = [] := List.getLast?_eq_none_iff.mp hRest
        subst hRestNil
        -- (ts :: []).getLast? = some ts
        simp at hStep
        exact hStep
      | some s =>
        -- rest.getLast? = some s, so (ts :: rest).getLast? = some s too
        have : (ts :: rest).getLast? = some s := by
          cases rest with
          | nil => simp at hRest
          | cons r rs => simp [hRest]
        rw [this] at hStep
        exact hStep

theorem valid_trace_extend (t : Trace) (a : PokemonLean.Semantics.Action) (next : GameState)
    (hValid : validTrace t)
    (hStep : PokemonLean.Semantics.step (finalState t) a = .ok next) :
    validTrace { initialState := t.initialState,
                 steps := t.steps ++ [{ action := a, resultState := next }] } := by
  exact valid_trace_extend_aux t.initialState t.steps a next hValid hStep

end PokemonLean.Replay
