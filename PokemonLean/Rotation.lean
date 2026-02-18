import PokemonLean.Basic
import PokemonLean.Switching

namespace PokemonLean.Rotation

open PokemonLean
open PokemonLean.Switching

def discardRetreatEnergy (cost : List EnergyType) (pokemon : PokemonInPlay) : Option PokemonInPlay :=
  match consumeEnergyCost cost pokemon.energy with
  | none => none
  | some remaining => some { pokemon with energy := remaining }

def isFreeRetreat (cost : List EnergyType) : Prop :=
  cost = []

def stranded (playerState : PlayerState) : Prop :=
  playerState.bench = []

def promoteBenchAt (playerState : PlayerState) (index : Nat) : Option (PokemonInPlay × List PokemonInPlay) :=
  removeAt? playerState.bench index

def pivotAt? (playerState : PlayerState) (index : Nat) : Option PokemonInPlay :=
  listGet? playerState.bench index

def retreatWithCostAt (playerState : PlayerState) (cost : List EnergyType) (index : Nat) :
    Option PlayerState :=
  match playerState.active with
  | none => none
  | some active =>
      match discardRetreatEnergy cost active with
      | none => none
      | some paid =>
          match promoteBenchAt playerState index with
          | none => none
          | some (pivot, rest) =>
              some { playerState with active := some pivot, bench := rest ++ [paid] }

def freeRetreatAt (playerState : PlayerState) (index : Nat) : Option PlayerState :=
  retreatWithCostAt playerState [] index

def switchOwnActive (state : GameState) (index : Nat) : Option GameState :=
  switchActive state index

def bossesOrders (state : GameState) (opponentIndex : Nat) : Option GameState :=
  let opponent := otherPlayer state.activePlayer
  match switchWithBenchIndex (getPlayerState state opponent) opponentIndex with
  | none => none
  | some switched => some (setPlayerState state opponent switched)

def escapeRope (state : GameState) (selfIndex opponentIndex : Nat) : Option GameState :=
  let player := state.activePlayer
  let opponent := otherPlayer player
  match switchWithBenchIndex (getPlayerState state player) selfIndex with
  | none => none
  | some selfSwitched =>
      match switchWithBenchIndex (getPlayerState state opponent) opponentIndex with
      | none => none
      | some oppSwitched =>
          let state' := setPlayerState state player selfSwitched
          some (setPlayerState state' opponent oppSwitched)

theorem discardRetreatEnergy_nil (pokemon : PokemonInPlay) :
    discardRetreatEnergy [] pokemon = some pokemon := by
  simp [discardRetreatEnergy, consumeEnergyCost]

theorem discardRetreatEnergy_card (cost : List EnergyType) (pokemon paid : PokemonInPlay)
    (h : discardRetreatEnergy cost pokemon = some paid) :
    paid.card = pokemon.card := by
  unfold discardRetreatEnergy at h
  cases hConsume : consumeEnergyCost cost pokemon.energy with
  | none =>
      simp [hConsume] at h
  | some remaining =>
      simp [hConsume] at h
      cases h
      rfl

theorem discardRetreatEnergy_damage (cost : List EnergyType) (pokemon paid : PokemonInPlay)
    (h : discardRetreatEnergy cost pokemon = some paid) :
    paid.damage = pokemon.damage := by
  unfold discardRetreatEnergy at h
  cases hConsume : consumeEnergyCost cost pokemon.energy with
  | none =>
      simp [hConsume] at h
  | some remaining =>
      simp [hConsume] at h
      cases h
      rfl

theorem discardRetreatEnergy_status (cost : List EnergyType) (pokemon paid : PokemonInPlay)
    (h : discardRetreatEnergy cost pokemon = some paid) :
    paid.status = pokemon.status := by
  unfold discardRetreatEnergy at h
  cases hConsume : consumeEnergyCost cost pokemon.energy with
  | none =>
      simp [hConsume] at h
  | some remaining =>
      simp [hConsume] at h
      cases h
      rfl

theorem discardRetreatEnergy_energy_sound (cost : List EnergyType) (pokemon paid : PokemonInPlay)
    (h : discardRetreatEnergy cost pokemon = some paid) :
    energyCostSatisfied cost pokemon.energy = true := by
  unfold discardRetreatEnergy at h
  cases hConsume : consumeEnergyCost cost pokemon.energy with
  | none =>
      simp [hConsume] at h
  | some remaining =>
      exact consumeEnergyCost_sound cost pokemon.energy remaining hConsume

theorem discardRetreatEnergy_some_iff (cost : List EnergyType) (pokemon : PokemonInPlay) :
    (∃ paid, discardRetreatEnergy cost pokemon = some paid) ↔
      energyCostSatisfied cost pokemon.energy = true := by
  constructor
  · intro h
    rcases h with ⟨paid, hPaid⟩
    exact discardRetreatEnergy_energy_sound cost pokemon paid hPaid
  · intro h
    rcases (energyCostSatisfied_iff_consume cost pokemon.energy).1 h with ⟨remaining, hConsume⟩
    refine ⟨{ pokemon with energy := remaining }, ?_⟩
    simp [discardRetreatEnergy, hConsume]

theorem discardRetreatEnergy_colorless_length (pokemon paid : PokemonInPlay)
    (h : discardRetreatEnergy [.colorless] pokemon = some paid) :
    paid.energy.length + 1 = pokemon.energy.length := by
  simp [discardRetreatEnergy] at h
  cases hRemove : removeFirstEnergy .colorless pokemon.energy with
  | none =>
      simp [consumeEnergyCost, hRemove] at h
  | some remaining =>
      simp [consumeEnergyCost, hRemove] at h
      cases h
      simpa using removeFirstEnergy_length .colorless pokemon.energy remaining hRemove

theorem isFreeRetreat_nil : isFreeRetreat [] := by
  simp [isFreeRetreat]

theorem isFreeRetreat_cons_false (head : EnergyType) (tail : List EnergyType) :
    ¬ isFreeRetreat (head :: tail) := by
  simp [isFreeRetreat]

theorem isFreeRetreat_iff (cost : List EnergyType) :
    isFreeRetreat cost ↔ cost = [] := by
  rfl

theorem stranded_iff_bench_nil (playerState : PlayerState) :
    stranded playerState ↔ playerState.bench = [] := by
  rfl

theorem stranded_of_bench_eq_nil (playerState : PlayerState) (h : playerState.bench = []) :
    stranded playerState := by
  simpa [stranded] using h

theorem not_stranded_of_bench_ne_nil (playerState : PlayerState) (h : playerState.bench ≠ []) :
    ¬ stranded playerState := by
  simpa [stranded] using h

theorem promoteBenchAt_eq_removeAt (playerState : PlayerState) (index : Nat) :
    promoteBenchAt playerState index = removeAt? playerState.bench index := by
  rfl

theorem promoteBenchAt_some_mem (playerState : PlayerState) (index : Nat) (pivot : PokemonInPlay)
    (rest : List PokemonInPlay) (h : promoteBenchAt playerState index = some (pivot, rest)) :
    pivot ∈ playerState.bench := by
  exact removeAt?_mem playerState.bench index pivot rest h

theorem promoteBenchAt_some_length (playerState : PlayerState) (index : Nat) (pivot : PokemonInPlay)
    (rest : List PokemonInPlay) (h : promoteBenchAt playerState index = some (pivot, rest)) :
    rest.length + 1 = playerState.bench.length := by
  exact removeAt?_length playerState.bench index pivot rest h

theorem pivotAt?_eq_listGet (playerState : PlayerState) (index : Nat) :
    pivotAt? playerState index = listGet? playerState.bench index := by
  rfl

theorem pivotAt?_zero (playerState : PlayerState) :
    pivotAt? playerState 0 = listGet? playerState.bench 0 := by
  rfl

theorem pivotAt?_none_of_stranded (playerState : PlayerState) (index : Nat)
    (hStranded : stranded playerState) :
    pivotAt? playerState index = none := by
  unfold pivotAt? stranded at *
  simp [hStranded, listGet?]

theorem stranded_implies_no_promoteBenchAt (playerState : PlayerState) (index : Nat)
    (hStranded : stranded playerState) :
    promoteBenchAt playerState index = none := by
  unfold promoteBenchAt stranded at *
  simp [hStranded, removeAt?]

theorem stranded_implies_no_switchWithBenchIndex (playerState : PlayerState) (index : Nat)
    (hStranded : stranded playerState) :
    switchWithBenchIndex playerState index = none := by
  unfold stranded at hStranded
  cases hActive : playerState.active with
  | none =>
      simp [switchWithBenchIndex, hActive]
  | some active =>
      simp [switchWithBenchIndex, hActive, hStranded, removeAt?]

theorem stranded_implies_no_switchHead (playerState : PlayerState)
    (hStranded : stranded playerState) :
    switchHead playerState = none := by
  simpa [switchHead] using
    stranded_implies_no_switchWithBenchIndex playerState 0 hStranded

theorem retreatWithCostAt_none_of_no_active (playerState : PlayerState) (cost : List EnergyType) (index : Nat)
    (hActive : playerState.active = none) :
    retreatWithCostAt playerState cost index = none := by
  simp [retreatWithCostAt, hActive]

theorem retreatWithCostAt_none_of_stranded (playerState : PlayerState) (cost : List EnergyType) (index : Nat)
    (hStranded : stranded playerState) :
    retreatWithCostAt playerState cost index = none := by
  unfold stranded at hStranded
  cases hActive : playerState.active with
  | none =>
      simp [retreatWithCostAt, hActive]
  | some active =>
      cases hPaid : discardRetreatEnergy cost active with
      | none =>
          simp [retreatWithCostAt, hActive, hPaid]
      | some paid =>
          simp [retreatWithCostAt, hActive, hPaid, hStranded, promoteBenchAt, removeAt?]

theorem retreatWithCostAt_some_iff (playerState : PlayerState) (cost : List EnergyType)
    (index : Nat) (newState : PlayerState) :
    retreatWithCostAt playerState cost index = some newState ↔
      ∃ active paid pivot rest,
        playerState.active = some active ∧
        discardRetreatEnergy cost active = some paid ∧
        promoteBenchAt playerState index = some (pivot, rest) ∧
        newState = { playerState with active := some pivot, bench := rest ++ [paid] } := by
  constructor
  · intro h
    cases hActive : playerState.active with
    | none =>
        simp [retreatWithCostAt, hActive] at h
    | some active =>
        simp [retreatWithCostAt, hActive] at h
        cases hPaid : discardRetreatEnergy cost active with
        | none =>
            simp [hPaid] at h
        | some paid =>
            simp [hPaid] at h
            cases hPromote : promoteBenchAt playerState index with
            | none =>
                simp [hPromote] at h
            | some pair =>
                rcases pair with ⟨pivot, rest⟩
                simp [hPromote] at h
                cases h
                refine ⟨active, paid, pivot, rest, ?_, ?_, ?_, rfl⟩
                · rfl
                · simp [hPaid]
                · rfl
  · rintro ⟨active, paid, pivot, rest, hActive, hPaid, hPromote, rfl⟩
    simp [retreatWithCostAt, hActive, hPaid, hPromote]

theorem retreatWithCostAt_active_some (playerState : PlayerState) (cost : List EnergyType)
    (index : Nat) (newState : PlayerState)
    (h : retreatWithCostAt playerState cost index = some newState) :
    ∃ active, playerState.active = some active ∧ newState.active.isSome := by
  rcases (retreatWithCostAt_some_iff playerState cost index newState).1 h with
    ⟨active, paid, pivot, rest, hActive, hPaid, hPromote, rfl⟩
  exact ⟨active, hActive, by simp⟩

theorem retreatWithCostAt_bench_length (playerState : PlayerState) (cost : List EnergyType)
    (index : Nat) (newState : PlayerState)
    (h : retreatWithCostAt playerState cost index = some newState) :
    newState.bench.length = playerState.bench.length := by
  rcases (retreatWithCostAt_some_iff playerState cost index newState).1 h with
    ⟨active, paid, pivot, rest, hActive, hPaid, hPromote, rfl⟩
  have hLen := promoteBenchAt_some_length playerState index pivot rest hPromote
  simp [List.length_append, hLen]

theorem retreatWithCostAt_preserves_prizes (playerState : PlayerState) (cost : List EnergyType)
    (index : Nat) (newState : PlayerState)
    (h : retreatWithCostAt playerState cost index = some newState) :
    newState.prizes = playerState.prizes := by
  rcases (retreatWithCostAt_some_iff playerState cost index newState).1 h with
    ⟨active, paid, pivot, rest, hActive, hPaid, hPromote, rfl⟩
  simp

theorem retreatWithCostAt_preserves_hand (playerState : PlayerState) (cost : List EnergyType)
    (index : Nat) (newState : PlayerState)
    (h : retreatWithCostAt playerState cost index = some newState) :
    newState.hand = playerState.hand := by
  rcases (retreatWithCostAt_some_iff playerState cost index newState).1 h with
    ⟨active, paid, pivot, rest, hActive, hPaid, hPromote, rfl⟩
  simp

theorem retreatWithCostAt_preserves_deck (playerState : PlayerState) (cost : List EnergyType)
    (index : Nat) (newState : PlayerState)
    (h : retreatWithCostAt playerState cost index = some newState) :
    newState.deck = playerState.deck := by
  rcases (retreatWithCostAt_some_iff playerState cost index newState).1 h with
    ⟨active, paid, pivot, rest, hActive, hPaid, hPromote, rfl⟩
  simp

theorem retreatWithCostAt_preserves_discard (playerState : PlayerState) (cost : List EnergyType)
    (index : Nat) (newState : PlayerState)
    (h : retreatWithCostAt playerState cost index = some newState) :
    newState.discard = playerState.discard := by
  rcases (retreatWithCostAt_some_iff playerState cost index newState).1 h with
    ⟨active, paid, pivot, rest, hActive, hPaid, hPromote, rfl⟩
  simp

theorem retreatWithCostAt_preserves_player_cards (playerState : PlayerState) (cost : List EnergyType)
    (index : Nat) (newState : PlayerState)
    (h : retreatWithCostAt playerState cost index = some newState) :
    playerCardCount newState = playerCardCount playerState := by
  rcases (retreatWithCostAt_some_iff playerState cost index newState).1 h with
    ⟨active, paid, pivot, rest, hActive, hPaid, hPromote, rfl⟩
  have hLen : rest.length + 1 = playerState.bench.length :=
    promoteBenchAt_some_length playerState index pivot rest hPromote
  unfold playerCardCount
  rw [bench_card_count (bench := rest ++ [paid])]
  rw [bench_card_count (bench := playerState.bench)]
  have hBenchLen : (rest ++ [paid]).length = playerState.bench.length := by
    simpa [List.length_append] using hLen
  simp [hActive, hBenchLen]

theorem freeRetreatAt_def (playerState : PlayerState) (index : Nat) :
    freeRetreatAt playerState index = retreatWithCostAt playerState [] index := by
  rfl

theorem freeRetreatAt_some_iff (playerState : PlayerState) (index : Nat) (newState : PlayerState) :
    freeRetreatAt playerState index = some newState ↔
      ∃ active paid pivot rest,
        playerState.active = some active ∧
        discardRetreatEnergy [] active = some paid ∧
        promoteBenchAt playerState index = some (pivot, rest) ∧
        newState = { playerState with active := some pivot, bench := rest ++ [paid] } := by
  simpa [freeRetreatAt] using retreatWithCostAt_some_iff playerState [] index newState

theorem freeRetreatAt_none_of_stranded (playerState : PlayerState) (index : Nat)
    (hStranded : stranded playerState) :
    freeRetreatAt playerState index = none := by
  simpa [freeRetreatAt] using retreatWithCostAt_none_of_stranded playerState [] index hStranded

theorem freeRetreatAt_preserves_player_cards (playerState : PlayerState) (index : Nat) (newState : PlayerState)
    (h : freeRetreatAt playerState index = some newState) :
    playerCardCount newState = playerCardCount playerState := by
  exact retreatWithCostAt_preserves_player_cards playerState [] index newState h

theorem freeRetreatAt_preserves_prizes (playerState : PlayerState) (index : Nat) (newState : PlayerState)
    (h : freeRetreatAt playerState index = some newState) :
    newState.prizes = playerState.prizes := by
  exact retreatWithCostAt_preserves_prizes playerState [] index newState h

theorem switchOwnActive_eq_switchActive (state : GameState) (index : Nat) :
    switchOwnActive state index = switchActive state index := by
  rfl

theorem switchOwnActive_preserves_total_cards (state : GameState) (index : Nat) (state' : GameState)
    (h : switchOwnActive state index = some state') :
    totalCardCount state' = totalCardCount state := by
  exact switchActive_preserves_total_cards state index state' h

theorem switchOwnActive_preserves_prizes (state : GameState) (index : Nat) (state' : GameState)
    (h : switchOwnActive state index = some state') :
    state'.playerOne.prizes = state.playerOne.prizes ∧
      state'.playerTwo.prizes = state.playerTwo.prizes := by
  exact switchActive_preserves_prizes state index state' h

theorem bossesOrders_some_iff (state : GameState) (opponentIndex : Nat) (state' : GameState) :
    bossesOrders state opponentIndex = some state' ↔
      ∃ switched,
        switchWithBenchIndex (getPlayerState state (otherPlayer state.activePlayer)) opponentIndex = some switched ∧
        state' = setPlayerState state (otherPlayer state.activePlayer) switched := by
  constructor
  · intro h
    unfold bossesOrders at h
    cases hSwitch : switchWithBenchIndex (getPlayerState state (otherPlayer state.activePlayer)) opponentIndex with
    | none =>
        simp [hSwitch] at h
    | some switched =>
        simp [hSwitch] at h
        cases h
        refine ⟨switched, ?_, rfl⟩
        simp
  · rintro ⟨switched, hSwitch, rfl⟩
    simp [bossesOrders, hSwitch]

theorem bossesOrders_activePlayer (state : GameState) (opponentIndex : Nat) (state' : GameState)
    (h : bossesOrders state opponentIndex = some state') :
    state'.activePlayer = state.activePlayer := by
  rcases (bossesOrders_some_iff state opponentIndex state').1 h with ⟨switched, hSwitch, rfl⟩
  cases hPlayer : state.activePlayer <;> simp [setPlayerState, otherPlayer, hPlayer]

theorem bossesOrders_none_of_opponent_stranded (state : GameState) (opponentIndex : Nat)
    (hStranded : stranded (getPlayerState state (otherPlayer state.activePlayer))) :
    bossesOrders state opponentIndex = none := by
  unfold bossesOrders
  have hNoSwitch :
      switchWithBenchIndex (getPlayerState state (otherPlayer state.activePlayer)) opponentIndex = none :=
    stranded_implies_no_switchWithBenchIndex
      (getPlayerState state (otherPlayer state.activePlayer)) opponentIndex hStranded
  simp [hNoSwitch]

theorem escapeRope_some_iff (state : GameState) (selfIndex opponentIndex : Nat) (state' : GameState) :
    escapeRope state selfIndex opponentIndex = some state' ↔
      ∃ selfSwitched oppSwitched,
        switchWithBenchIndex (getPlayerState state state.activePlayer) selfIndex = some selfSwitched ∧
        switchWithBenchIndex (getPlayerState state (otherPlayer state.activePlayer)) opponentIndex = some oppSwitched ∧
        state' = setPlayerState
          (setPlayerState state state.activePlayer selfSwitched)
          (otherPlayer state.activePlayer) oppSwitched := by
  constructor
  · intro h
    unfold escapeRope at h
    cases hSelf : switchWithBenchIndex (getPlayerState state state.activePlayer) selfIndex with
    | none =>
        simp [hSelf] at h
    | some selfSwitched =>
        cases hOpp : switchWithBenchIndex (getPlayerState state (otherPlayer state.activePlayer)) opponentIndex with
        | none =>
            simp [hSelf, hOpp] at h
        | some oppSwitched =>
            simp [hSelf, hOpp] at h
            cases h
            refine ⟨selfSwitched, oppSwitched, ?_, ?_, rfl⟩
            · simp
            · simp
  · rintro ⟨selfSwitched, oppSwitched, hSelf, hOpp, rfl⟩
    simp [escapeRope, hSelf, hOpp]

theorem escapeRope_activePlayer (state : GameState) (selfIndex opponentIndex : Nat) (state' : GameState)
    (h : escapeRope state selfIndex opponentIndex = some state') :
    state'.activePlayer = state.activePlayer := by
  rcases (escapeRope_some_iff state selfIndex opponentIndex state').1 h with
    ⟨selfSwitched, oppSwitched, hSelf, hOpp, rfl⟩
  cases hPlayer : state.activePlayer <;> simp [setPlayerState, otherPlayer, hPlayer]

theorem escapeRope_none_of_active_stranded (state : GameState) (selfIndex opponentIndex : Nat)
    (hStranded : stranded (getPlayerState state state.activePlayer)) :
    escapeRope state selfIndex opponentIndex = none := by
  unfold escapeRope
  have hNoSwitch :
      switchWithBenchIndex (getPlayerState state state.activePlayer) selfIndex = none :=
    stranded_implies_no_switchWithBenchIndex (getPlayerState state state.activePlayer) selfIndex hStranded
  simp [hNoSwitch]

theorem escapeRope_none_of_opponent_stranded (state : GameState) (selfIndex opponentIndex : Nat)
    (hStranded : stranded (getPlayerState state (otherPlayer state.activePlayer))) :
    escapeRope state selfIndex opponentIndex = none := by
  unfold escapeRope
  cases hSelf : switchWithBenchIndex (getPlayerState state state.activePlayer) selfIndex with
  | none =>
      simp [hSelf]
  | some selfSwitched =>
      have hNoSwitch :
          switchWithBenchIndex (getPlayerState state (otherPlayer state.activePlayer)) opponentIndex = none :=
        stranded_implies_no_switchWithBenchIndex
          (getPlayerState state (otherPlayer state.activePlayer)) opponentIndex hStranded
      simp [hSelf, hNoSwitch]

end PokemonLean.Rotation
