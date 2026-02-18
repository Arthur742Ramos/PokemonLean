import PokemonLean.Basic

namespace PokemonLean.Switching

open PokemonLean

inductive SwitchError
  | noActive
  | invalidBenchIndex
  | emptyBench
  | retreatCostUnpaid
  deriving Repr, BEq, DecidableEq

def removeAt? {α : Type} : List α → Nat → Option (α × List α)
  | [], _ => none
  | x :: xs, 0 => some (x, xs)
  | x :: xs, Nat.succ n =>
      match removeAt? xs n with
      | none => none
      | some (y, ys) => some (y, x :: ys)

theorem removeAt?_length {α : Type} :
    ∀ (xs : List α) (idx : Nat) (x : α) (rest : List α),
      removeAt? xs idx = some (x, rest) → rest.length + 1 = xs.length := by
  intro xs idx x rest h
  induction xs generalizing idx x rest with
  | nil =>
      cases idx <;> simp [removeAt?] at h
  | cons head tail ih =>
      cases idx with
      | zero =>
          simp [removeAt?] at h
          rcases h with ⟨rfl, rfl⟩
          simp
      | succ idx =>
          simp [removeAt?] at h
          cases hRec : removeAt? tail idx with
          | none =>
              simp [hRec] at h
          | some pair =>
              rcases pair with ⟨y, ys⟩
              simp [hRec] at h
              rcases h with ⟨hxy, hrest⟩
              subst hxy
              subst hrest
              have hLen : ys.length + 1 = tail.length := ih idx y ys hRec
              -- goal: (head :: ys).length + 1 = (head :: tail).length
              simp [List.length_cons, hLen]

theorem removeAt?_mem {α : Type} :
    ∀ (xs : List α) (idx : Nat) (x : α) (rest : List α),
      removeAt? xs idx = some (x, rest) → x ∈ xs := by
  intro xs idx x rest h
  induction xs generalizing idx x rest with
  | nil =>
      cases idx <;> simp [removeAt?] at h
  | cons head tail ih =>
      cases idx with
      | zero =>
          simp [removeAt?] at h
          rcases h with ⟨rfl, rfl⟩
          simp
      | succ idx =>
          simp [removeAt?] at h
          cases hRec : removeAt? tail idx with
          | none =>
              simp [hRec] at h
          | some pair =>
              rcases pair with ⟨y, ys⟩
              simp [hRec] at h
              rcases h with ⟨hxy, _hrest⟩
              subst hxy
              have hMem : y ∈ tail := ih idx y ys hRec
              simp [hMem]

def switchWithBenchIndex (playerState : PlayerState) (index : Nat) : Option PlayerState :=
  match playerState.active with
  | none => none
  | some active =>
      match removeAt? playerState.bench index with
      | none => none
      | some (newActive, newBench) =>
          some { playerState with active := some newActive, bench := newBench ++ [active] }

def switchHead (playerState : PlayerState) : Option PlayerState :=
  switchWithBenchIndex playerState 0

def canSwitchWithBenchIndex (playerState : PlayerState) (index : Nat) : Prop :=
  ∃ active newActive newBench,
    playerState.active = some active ∧
    removeAt? playerState.bench index = some (newActive, newBench)

def canSwitchHead (playerState : PlayerState) : Prop :=
  canSwitchWithBenchIndex playerState 0

theorem switchWithBenchIndex_some_iff (playerState : PlayerState) (index : Nat) (newState : PlayerState) :
    switchWithBenchIndex playerState index = some newState ↔
      ∃ active newActive newBench,
        playerState.active = some active ∧
        removeAt? playerState.bench index = some (newActive, newBench) ∧
        newState = { playerState with active := some newActive, bench := newBench ++ [active] } := by
  constructor
  · intro h
    cases hActive : playerState.active with
    | none =>
      simp [switchWithBenchIndex, hActive] at h
    | some active =>
      simp [switchWithBenchIndex, hActive] at h
      cases hRemove : removeAt? playerState.bench index with
      | none =>
        simp [hRemove] at h
      | some pair =>
        cases pair with
        | mk newActive newBench =>
          simp [hRemove] at h
          cases h
          refine ⟨active, newActive, newBench, ?_, ?_, rfl⟩
          · simp
          · simp
  · rintro ⟨active, newActive, newBench, hActive, hRemove, rfl⟩
    simp [switchWithBenchIndex, hActive, hRemove]

theorem switchWithBenchIndex_bench_length (playerState : PlayerState) (index : Nat) (newState : PlayerState)
    (h : switchWithBenchIndex playerState index = some newState) :
    newState.bench.length = playerState.bench.length := by
  rcases (switchWithBenchIndex_some_iff playerState index newState).1 h with
    ⟨active, newActive, newBench, hActive, hRemove, rfl⟩
  have hLen := removeAt?_length playerState.bench index newActive newBench hRemove
  simp [List.length_append, hLen]

theorem switchWithBenchIndex_active_some (playerState : PlayerState) (index : Nat) (newState : PlayerState)
    (h : switchWithBenchIndex playerState index = some newState) :
    ∃ active, playerState.active = some active ∧ newState.active.isSome := by
  rcases (switchWithBenchIndex_some_iff playerState index newState).1 h with
    ⟨active, newActive, newBench, hActive, hRemove, rfl⟩
  exact ⟨active, hActive, by simp⟩

theorem switchWithBenchIndex_preserves_player_cards (playerState : PlayerState) (index : Nat)
    (newState : PlayerState) (h : switchWithBenchIndex playerState index = some newState) :
    playerCardCount newState = playerCardCount playerState := by
  rcases (switchWithBenchIndex_some_iff playerState index newState).1 h with
    ⟨active, newActive, newBench, hActive, hRemove, rfl⟩
  have hLen := removeAt?_length playerState.bench index newActive newBench hRemove
  -- playerCardCount only depends on bench length (each pokemon counts as 1)
  simp [playerCardCount, hActive]
  rw [bench_card_count, bench_card_count]
  have hBenchLen : (newBench ++ [active]).length = playerState.bench.length := by
    -- hLen : newBench.length + 1 = playerState.bench.length
    simpa [List.length_append] using hLen
  simpa [hBenchLen]

theorem switchWithBenchIndex_preserves_prizes (playerState : PlayerState) (index : Nat) (newState : PlayerState)
    (h : switchWithBenchIndex playerState index = some newState) :
    newState.prizes = playerState.prizes := by
  rcases (switchWithBenchIndex_some_iff playerState index newState).1 h with
    ⟨active, newActive, newBench, hActive, hRemove, rfl⟩
  simp

theorem payRetreatCost_card (pokemon paid : PokemonInPlay) (h : payRetreatCost pokemon = some paid) :
    paid.card = pokemon.card := by
  cases hConsume : consumeEnergyCost retreatCost pokemon.energy with
  | none =>
    simp [payRetreatCost, hConsume] at h
  | some remaining =>
    simp [payRetreatCost, hConsume] at h
    cases h
    rfl

theorem payRetreatCost_status (pokemon paid : PokemonInPlay) (h : payRetreatCost pokemon = some paid) :
    paid.status = pokemon.status := by
  cases hConsume : consumeEnergyCost retreatCost pokemon.energy with
  | none =>
    simp [payRetreatCost, hConsume] at h
  | some remaining =>
    simp [payRetreatCost, hConsume] at h
    cases h
    rfl

theorem payRetreatCost_damage (pokemon paid : PokemonInPlay) (h : payRetreatCost pokemon = some paid) :
    paid.damage = pokemon.damage := by
  cases hConsume : consumeEnergyCost retreatCost pokemon.energy with
  | none =>
    simp [payRetreatCost, hConsume] at h
  | some remaining =>
    simp [payRetreatCost, hConsume] at h
    cases h
    rfl

def retreatWithCost (playerState : PlayerState) : Option PlayerState :=
  match playerState.active with
  | none => none
  | some active =>
      match payRetreatCost active with
      | none => none
      | some paid =>
          match playerState.bench with
          | [] => none
          | newActive :: rest =>
              some { playerState with active := some newActive, bench := rest ++ [paid] }

def canRetreatWithCost (playerState : PlayerState) : Prop :=
  ∃ active paid newActive rest,
    playerState.active = some active ∧
    payRetreatCost active = some paid ∧
    playerState.bench = newActive :: rest

theorem retreatWithCost_some_iff (playerState : PlayerState) (newState : PlayerState) :
    retreatWithCost playerState = some newState ↔
      ∃ active paid newActive rest,
        playerState.active = some active ∧
        payRetreatCost active = some paid ∧
        playerState.bench = newActive :: rest ∧
        newState = { playerState with active := some newActive, bench := rest ++ [paid] } := by
  constructor
  · intro h
    cases hActive : playerState.active with
    | none =>
      simp [retreatWithCost, hActive] at h
    | some active =>
      simp [retreatWithCost, hActive] at h
      cases hPaid : payRetreatCost active with
      | none =>
        simp [hPaid] at h
      | some paid =>
        simp [hPaid] at h
        cases hBench : playerState.bench with
        | nil =>
          simp [hBench] at h
        | cons newActive rest =>
          simp [hBench] at h
          cases h
          refine ⟨active, paid, newActive, rest, ?_, ?_, ?_, rfl⟩
          · simp
          · simp [hPaid]
          · simp
  · rintro ⟨active, paid, newActive, rest, hActive, hPaid, hBench, rfl⟩
    simp [retreatWithCost, hActive, hPaid, hBench]

theorem retreatWithCost_bench_length (playerState : PlayerState) (newState : PlayerState)
    (h : retreatWithCost playerState = some newState) :
    newState.bench.length = playerState.bench.length := by
  rcases (retreatWithCost_some_iff playerState newState).1 h with
    ⟨active, paid, newActive, rest, hActive, hPaid, hBench, rfl⟩
  simp [hBench, List.length_append]

theorem retreatWithCost_preserves_player_cards (playerState : PlayerState) (newState : PlayerState)
    (h : retreatWithCost playerState = some newState) :
    playerCardCount newState = playerCardCount playerState := by
  rcases (retreatWithCost_some_iff playerState newState).1 h with
    ⟨active, paid, newActive, rest, hActive, hPaid, hBench, rfl⟩
  -- Expand card counts, and rewrite bench counts using `bench_card_count` *before* any simplification.
  unfold playerCardCount
  rw [bench_card_count (bench := rest ++ [paid])]
  rw [hBench]
  rw [bench_card_count (bench := newActive :: rest)]
  simp [hActive, List.length_append, Nat.add_assoc]

theorem retreatWithCost_energy_length (playerState : PlayerState) (newState : PlayerState)
    (h : retreatWithCost playerState = some newState) :
    ∃ active paid,
      playerState.active = some active ∧
      payRetreatCost active = some paid ∧
      paid.energy.length + 1 = active.energy.length := by
  rcases (retreatWithCost_some_iff playerState newState).1 h with
    ⟨active, paid, newActive, rest, hActive, hPaid, hBench, rfl⟩
  exact ⟨active, paid, hActive, hPaid, payRetreatCost_length active paid hPaid⟩

def switchActive (state : GameState) (index : Nat) : Option GameState :=
  let player := state.activePlayer
  match switchWithBenchIndex (getPlayerState state player) index with
  | none => none
  | some playerState => some (setPlayerState state player playerState)

def retreatActive (state : GameState) : Option GameState :=
  let player := state.activePlayer
  match retreatWithCost (getPlayerState state player) with
  | none => none
  | some playerState => some (setPlayerState state player playerState)

theorem switchActive_preserves_total_cards (state : GameState) (index : Nat) (state' : GameState)
    (h : switchActive state index = some state') :
    totalCardCount state' = totalCardCount state := by
  simp [switchActive] at h
  cases hSwitch : switchWithBenchIndex (getPlayerState state state.activePlayer) index with
  | none =>
      simp [hSwitch] at h
  | some playerState =>
      simp [hSwitch] at h
      cases h
      cases hPlayer : state.activePlayer <;>
        simp [totalCardCount, getPlayerState, setPlayerState, hPlayer] at hSwitch ⊢
      · have hCards := switchWithBenchIndex_preserves_player_cards state.playerOne index playerState hSwitch
        simp [hCards]
      · have hCards := switchWithBenchIndex_preserves_player_cards state.playerTwo index playerState hSwitch
        simp [hCards]

theorem switchActive_preserves_prizes (state : GameState) (index : Nat) (state' : GameState)
    (h : switchActive state index = some state') :
    state'.playerOne.prizes = state.playerOne.prizes ∧
      state'.playerTwo.prizes = state.playerTwo.prizes := by
  simp [switchActive] at h
  cases hSwitch : switchWithBenchIndex (getPlayerState state state.activePlayer) index with
  | none => simp [hSwitch] at h
  | some playerState =>
    simp [hSwitch] at h
    cases h
    cases hPlayer : state.activePlayer <;> simp [getPlayerState, setPlayerState, hPlayer] at hSwitch ⊢
    · have hPrizes := switchWithBenchIndex_preserves_prizes _ _ _ hSwitch
      simpa [hPlayer] using hPrizes
    · have hPrizes := switchWithBenchIndex_preserves_prizes _ _ _ hSwitch
      simpa [hPlayer] using hPrizes

theorem retreatActive_preserves_total_cards (state : GameState) (state' : GameState)
    (h : retreatActive state = some state') :
    totalCardCount state' = totalCardCount state := by
  simp [retreatActive] at h
  cases hRetreat : retreatWithCost (getPlayerState state state.activePlayer) with
  | none =>
      simp [hRetreat] at h
  | some playerState =>
      simp [hRetreat] at h
      cases h
      cases hPlayer : state.activePlayer <;>
        simp [totalCardCount, getPlayerState, setPlayerState, hPlayer] at hRetreat ⊢
      · have hCards := retreatWithCost_preserves_player_cards state.playerOne playerState hRetreat
        simp [hCards]
      · have hCards := retreatWithCost_preserves_player_cards state.playerTwo playerState hRetreat
        simp [hCards]

theorem retreatWithCost_preserves_prizes (playerState : PlayerState) (newState : PlayerState)
    (h : retreatWithCost playerState = some newState) :
    newState.prizes = playerState.prizes := by
  rcases (retreatWithCost_some_iff playerState newState).1 h with
    ⟨active, paid, newActive, rest, hActive, hPaid, hBench, rfl⟩
  simp

theorem retreatActive_preserves_prizes (state : GameState) (state' : GameState)
    (h : retreatActive state = some state') :
    state'.playerOne.prizes = state.playerOne.prizes ∧
      state'.playerTwo.prizes = state.playerTwo.prizes := by
  simp [retreatActive] at h
  cases hRetreat : retreatWithCost (getPlayerState state state.activePlayer) with
  | none => simp [hRetreat] at h
  | some playerState =>
    simp [hRetreat] at h
    cases h
    cases hPlayer : state.activePlayer <;> simp [getPlayerState, setPlayerState, hPlayer] at hRetreat ⊢
    · have hPrizes := retreatWithCost_preserves_prizes _ _ hRetreat
      simpa [hPlayer] using hPrizes
    · have hPrizes := retreatWithCost_preserves_prizes _ _ hRetreat
      simpa [hPlayer] using hPrizes

end PokemonLean.Switching
