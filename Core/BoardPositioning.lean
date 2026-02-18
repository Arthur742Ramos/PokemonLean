/-
  Core/BoardPositioning.lean — Armada 627 File 3/3
  Bench management strategy, promoting from bench to active,
  bench space optimization, evolution on bench,
  bench-sitting strategies (setup attackers behind wall)
-/
import Core.Types

-- ============================================================
-- Section 1: Promoting from bench to active
-- ============================================================

/-- Promote a benched Pokemon to active position -/
def promoteBenchToActive (board : BoardState) (benchIdx : Nat) : BoardState :=
  if h : benchIdx < board.bench.length then
    let promoted := board.bench.get ⟨benchIdx, h⟩
    let newBench := removeBenchAt board.bench benchIdx
    { board with active := some promoted, bench := newBench }
  else board

/-- When active is KO'd, must promote from bench -/
def mustPromote (board : BoardState) : Bool :=
  match board.active with
  | none => decide (board.bench.length > 0)
  | some p => isKnockedOut p && decide (board.bench.length > 0)

theorem promote_sets_active (board : BoardState) (idx : Nat)
    (h : idx < board.bench.length) :
    (promoteBenchToActive board idx).active = some (board.bench.get ⟨idx, h⟩) := by
  simp [promoteBenchToActive, h]

theorem promote_removes_from_bench (board : BoardState) (idx : Nat)
    (h : idx < board.bench.length) :
    (promoteBenchToActive board idx).bench.length = board.bench.length - 1 := by
  simp [promoteBenchToActive, h, removeBenchAt, List.length_eraseIdx]

theorem promote_invalid_idx_unchanged (board : BoardState) (idx : Nat)
    (h : ¬ idx < board.bench.length) :
    promoteBenchToActive board idx = board := by
  simp [promoteBenchToActive, h]

theorem promote_total_field_count (board : BoardState) (idx : Nat)
    (h : idx < board.bench.length) :
    (promoteBenchToActive board idx).bench.length + 1 = board.bench.length := by
  simp [promoteBenchToActive, h, removeBenchAt, List.length_eraseIdx]; omega

theorem must_promote_empty_bench_no_active :
    mustPromote { active := none, bench := [], stadium := StadiumCard.none, benchAbility := BenchAbility.none } = false := by rfl

theorem must_promote_no_active_with_bench (p : Pokemon) :
    mustPromote { active := none, bench := [p], stadium := StadiumCard.none, benchAbility := BenchAbility.none } = true := by rfl

-- ============================================================
-- Section 2: Evolution on bench
-- ============================================================

/-- Evolve a benched Pokemon at a given index -/
def evolveBenched (bench : List Pokemon) (idx : Nat) (evolution : Pokemon) : List Pokemon :=
  if idx < bench.length then
    List.mapIdx (fun i p => if i == idx then { evolution with isEvolved := true } else p) bench
  else bench

theorem evolve_preserves_bench_length (bench : List Pokemon) (idx : Nat) (evo : Pokemon) :
    (evolveBenched bench idx evo).length = bench.length := by
  simp [evolveBenched]; split
  · simp [List.length_mapIdx]
  · rfl

theorem evolve_invalid_idx_unchanged (bench : List Pokemon) (idx : Nat) (evo : Pokemon)
    (h : ¬ idx < bench.length) : evolveBenched bench idx evo = bench := by
  simp [evolveBenched, h]

theorem evolve_on_empty_bench (idx : Nat) (evo : Pokemon) :
    evolveBenched [] idx evo = [] := by
  simp [evolveBenched]

-- ============================================================
-- Section 3: Bench space optimization
-- ============================================================

theorem empty_slots_max_when_empty (s : StadiumCard) :
    emptyBenchSlots [] s = stadiumBenchLimit s := by
  simp [emptyBenchSlots]

theorem empty_slots_zero_when_full (bench : List Pokemon) (s : StadiumCard)
    (h : bench.length = stadiumBenchLimit s) :
    emptyBenchSlots bench s = 0 := by
  simp [emptyBenchSlots, h]

theorem utilization_zero_when_empty (s : StadiumCard) :
    benchUtilization [] s = 0 := by
  simp [benchUtilization]

theorem utilization_100_when_full_default
    (bench : List Pokemon) (h : bench.length = 5) :
    benchUtilization bench StadiumCard.none = 100 := by
  simp [benchUtilization, stadiumBenchLimit, h]

theorem utilization_100_sky_field
    (bench : List Pokemon) (h : bench.length = 8) :
    benchUtilization bench StadiumCard.skyField = 100 := by
  simp [benchUtilization, stadiumBenchLimit, h]

-- ============================================================
-- Section 4: Wall strategy — setup attackers behind wall
-- ============================================================

/-- Check if board has wall-behind strategy: wall active, setup on bench -/
def hasWallStrategy (board : BoardState) : Bool :=
  match board.active with
  | some p => isWallPokemon p && decide (countSetupAttackers board.bench > 0)
  | none => false

theorem wall_needs_active (board : BoardState) (h : board.active = none) :
    hasWallStrategy board = false := by
  simp [hasWallStrategy, h]

theorem wall_strategy_needs_bench_attacker (p : Pokemon) :
    hasWallStrategy ⟨some p, [], StadiumCard.none, BenchAbility.none⟩ = false := by
  simp [hasWallStrategy, countSetupAttackers]

theorem count_setup_empty : countSetupAttackers [] = 0 := rfl

theorem count_setup_le_bench (bench : List Pokemon) :
    countSetupAttackers bench ≤ bench.length := by
  simp [countSetupAttackers]; exact List.length_filter_le _ _

-- ============================================================
-- Section 5: Board state invariants
-- ============================================================

/-- Check if game state is valid (at least one Pokemon) -/
def validGameState (board : BoardState) : Bool :=
  decide (totalFieldPokemon board > 0)

theorem total_field_ge_bench (board : BoardState) :
    totalFieldPokemon board ≥ board.bench.length := by
  unfold totalFieldPokemon; split <;> omega

theorem total_field_with_active (board : BoardState) (p : Pokemon)
    (h : board.active = some p) :
    totalFieldPokemon board = 1 + board.bench.length := by
  simp [totalFieldPokemon, h]

theorem valid_with_active (p : Pokemon) (bench : List Pokemon) (s : StadiumCard)
    (a : BenchAbility) :
    validGameState ⟨some p, bench, s, a⟩ = true := by
  simp [validGameState, totalFieldPokemon]; omega

theorem empty_board_invalid :
    validGameState ⟨none, [], StadiumCard.none, BenchAbility.none⟩ = false := by rfl

-- ============================================================
-- Section 6: Bench positioning strategy helpers
-- ============================================================

/-- Find highest HP Pokemon on bench (for promoting) -/
def highestHpBenchIdx (bench : List Pokemon) : Option Nat :=
  let indexed := bench.enum
  match indexed.foldl (fun acc ⟨i, p⟩ =>
    match acc with
    | none => some (i, p.currentHp)
    | some (_, bestHp) => if p.currentHp > bestHp then some (i, p.currentHp) else acc
  ) (none : Option (Nat × Nat)) with
  | some (idx, _) => some idx
  | none => none

/-- Find lowest retreat cost Pokemon on bench -/
def lowestRetreatBenchIdx (bench : List Pokemon) : Option Nat :=
  let indexed := bench.enum
  match indexed.foldl (fun acc ⟨i, p⟩ =>
    match acc with
    | none => some (i, p.retreatCost)
    | some (_, bestCost) => if p.retreatCost < bestCost then some (i, p.retreatCost) else acc
  ) (none : Option (Nat × Nat)) with
  | some (idx, _) => some idx
  | none => none

theorem highest_hp_empty : highestHpBenchIdx [] = none := by rfl

theorem lowest_retreat_empty : lowestRetreatBenchIdx [] = none := by rfl

-- ============================================================
-- Section 7: Retreat and switch mechanics
-- ============================================================

/-- Retreat: swap active with bench Pokemon, paying retreat cost -/
def retreat (board : BoardState) (benchIdx : Nat) (energyAvailable : Nat) : Option BoardState :=
  match board.active with
  | none => none
  | some active =>
    if h : benchIdx < board.bench.length then
      if energyAvailable ≥ active.retreatCost then
        let replacement := board.bench.get ⟨benchIdx, h⟩
        let newBench := (removeBenchAt board.bench benchIdx) ++ [active]
        some { board with active := some replacement, bench := newBench }
      else none
    else none

theorem retreat_needs_active (board : BoardState) (idx energy : Nat)
    (h : board.active = none) :
    retreat board idx energy = none := by
  simp [retreat, h]

theorem retreat_needs_energy (board : BoardState) (idx energy : Nat) (p : Pokemon)
    (hActive : board.active = some p)
    (hIdx : idx < board.bench.length)
    (hEnergy : ¬ energy ≥ p.retreatCost) :
    retreat board idx energy = none := by
  simp [retreat, hActive, hIdx, hEnergy]

theorem zero_retreat_always_works (board : BoardState) (idx : Nat) (p : Pokemon)
    (hActive : board.active = some p)
    (hIdx : idx < board.bench.length)
    (hCost : p.retreatCost = 0) :
    (retreat board idx 0).isSome = true := by
  simp [retreat, hActive, hIdx, hCost]

-- ============================================================
-- Section 8: Bench-sitting value computation
-- ============================================================

theorem bench_sit_value_nonneg (p : Pokemon) :
    benchSitValue p ≥ 0 := by omega

theorem unevolved_basic_has_sit_value
    (p : Pokemon) (h : p.isEvolved = false) : benchSitValue p ≥ 10 := by
  simp [benchSitValue, h]; omega

theorem setup_attacker_high_value (p : Pokemon)
    (h : isSetupAttacker p = true) :
    benchSitValue p ≥ 20 := by
  simp [benchSitValue, h]; split <;> omega

-- ============================================================
-- Section 9: Cross-mechanic composition theorems
-- ============================================================

theorem full_default_bench_five (bench : List Pokemon)
    (h : benchIsFull bench StadiumCard.none = true) :
    bench.length ≥ 5 := by
  simp [benchIsFull, stadiumBenchLimit] at h; exact h

theorem promote_from_full_creates_room (board : BoardState) (idx : Nat)
    (hFull : board.bench.length = stadiumBenchLimit board.stadium)
    (hIdx : idx < board.bench.length) :
    (promoteBenchToActive board idx).bench.length < stadiumBenchLimit board.stadium := by
  simp [promoteBenchToActive, hIdx, removeBenchAt, List.length_eraseIdx]; omega

theorem protection_preserves_bench_count (bench : List Pokemon) (dmg : Nat)
    (a : BenchAbility) :
    (bench.map (fun p => applyDamage p (effectiveBenchDamage a dmg))).length = bench.length := by
  simp

theorem sky_field_removal_trim (bench : List Pokemon)
    (h : bench.length = 8) :
    (trimBench bench 5).length = 5 := by
  simp [trimBench, List.length_take]; omega

theorem add_then_trim_valid (bench : List Pokemon) (p : Pokemon) (s : StadiumCard) :
    (trimBench (bench ++ [p]) (stadiumBenchLimit s)).length ≤ stadiumBenchLimit s := by
  simp [trimBench, List.length_take]; omega
