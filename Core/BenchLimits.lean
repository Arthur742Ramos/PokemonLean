/-
  Core/BenchLimits.lean — Armada 627 File 1/3
  Bench size limits: default 5, Sky Field 8, Collapsed Stadium 4,
  Parallel City 3, bench overflow/discard mechanics
-/
import Core.Types

-- ============================================================
-- Section 1: Stadium bench limit properties
-- ============================================================

theorem default_bench_limit_is_five :
    stadiumBenchLimit StadiumCard.none = 5 := rfl

theorem sky_field_bench_limit_is_eight :
    stadiumBenchLimit StadiumCard.skyField = 8 := rfl

theorem collapsed_stadium_bench_limit_is_four :
    stadiumBenchLimit StadiumCard.collapsedStadium = 4 := rfl

theorem parallel_city_bench_limit_is_three :
    stadiumBenchLimit StadiumCard.parallelCity = 3 := rfl

theorem sky_field_expands_bench :
    stadiumBenchLimit StadiumCard.skyField > stadiumBenchLimit StadiumCard.none := by decide

theorem collapsed_stadium_shrinks_bench :
    stadiumBenchLimit StadiumCard.collapsedStadium < stadiumBenchLimit StadiumCard.none := by decide

theorem parallel_city_most_restrictive :
    stadiumBenchLimit StadiumCard.parallelCity < stadiumBenchLimit StadiumCard.collapsedStadium := by decide

theorem all_limits_positive : ∀ (s : StadiumCard), stadiumBenchLimit s > 0 := by
  intro s; cases s <;> decide

theorem sky_field_doubles_not_quite :
    stadiumBenchLimit StadiumCard.skyField < 2 * stadiumBenchLimit StadiumCard.none := by decide

theorem collapsed_plus_parallel_lt_sky :
    stadiumBenchLimit StadiumCard.collapsedStadium + stadiumBenchLimit StadiumCard.parallelCity
    < stadiumBenchLimit StadiumCard.skyField := by decide

theorem all_limits_le_eight : ∀ (s : StadiumCard), stadiumBenchLimit s ≤ 8 := by
  intro s; cases s <;> decide

theorem all_limits_ge_three : ∀ (s : StadiumCard), stadiumBenchLimit s ≥ 3 := by
  intro s; cases s <;> decide

-- ============================================================
-- Section 2: Bench full / has room logic
-- ============================================================

theorem empty_bench_never_full : ∀ (s : StadiumCard), benchIsFull [] s = false := by
  intro s; cases s <;> simp [benchIsFull, stadiumBenchLimit]

theorem empty_bench_always_has_room : ∀ (s : StadiumCard), benchHasRoom [] s = true := by
  intro s; cases s <;> simp [benchHasRoom, stadiumBenchLimit]

theorem bench_full_implies_not_has_room (bench : List Pokemon) (s : StadiumCard) :
    benchIsFull bench s = true → benchHasRoom bench s = false := by
  simp [benchIsFull, benchHasRoom]

theorem bench_has_room_implies_not_full (bench : List Pokemon) (s : StadiumCard) :
    benchHasRoom bench s = true → benchIsFull bench s = false := by
  simp [benchIsFull, benchHasRoom]

theorem bench_full_iff_not_has_room (bench : List Pokemon) (s : StadiumCard) :
    benchIsFull bench s = true ↔ benchHasRoom bench s = false := by
  simp [benchIsFull, benchHasRoom]

-- ============================================================
-- Section 3: Bench overflow — stadium replacement mechanics
-- ============================================================

theorem trim_bench_respects_limit (bench : List Pokemon) (limit : Nat) :
    (trimBench bench limit).length ≤ limit := by
  simp [trimBench, List.length_take]; omega

theorem trim_bench_no_change_when_under (bench : List Pokemon) (limit : Nat)
    (h : bench.length ≤ limit) : trimBench bench limit = bench := by
  simp [trimBench, List.take_of_length_le h]

theorem trim_bench_length_exact (bench : List Pokemon) (limit : Nat)
    (h : bench.length ≥ limit) : (trimBench bench limit).length = limit := by
  simp [trimBench, List.length_take]; omega

theorem sky_field_to_none_overflow (bench : List Pokemon)
    (h : bench.length > 5) :
    benchOverflowCount bench StadiumCard.skyField StadiumCard.none = bench.length - 5 := by
  unfold benchOverflowCount; simp [stadiumBenchLimit]; intro habs; omega

theorem no_overflow_when_under_limit (bench : List Pokemon) (s1 s2 : StadiumCard)
    (h : bench.length ≤ stadiumBenchLimit s2) :
    benchOverflowCount bench s1 s2 = 0 := by
  unfold benchOverflowCount; simp; intro habs; omega

theorem overflow_zero_when_expanding (bench : List Pokemon)
    (h : bench.length ≤ stadiumBenchLimit StadiumCard.none) :
    benchOverflowCount bench StadiumCard.none StadiumCard.skyField = 0 := by
  unfold benchOverflowCount; simp [stadiumBenchLimit]; intro habs
  simp [stadiumBenchLimit] at h; omega

-- ============================================================
-- Section 4: Adding to bench
-- ============================================================

theorem add_to_bench_valid_length (bench : List Pokemon) (p : Pokemon) (s : StadiumCard)
    (hValid : bench.length ≤ stadiumBenchLimit s) :
    (addToBench bench p s).length ≤ stadiumBenchLimit s := by
  unfold addToBench; split
  · next h => simp; omega
  · next h => exact hValid

theorem add_to_bench_increases_when_room (bench : List Pokemon) (p : Pokemon) (s : StadiumCard)
    (h : bench.length < stadiumBenchLimit s) :
    (addToBench bench p s).length = bench.length + 1 := by
  simp [addToBench, h, List.length_append]

theorem add_to_bench_unchanged_when_full (bench : List Pokemon) (p : Pokemon) (s : StadiumCard)
    (h : ¬ bench.length < stadiumBenchLimit s) :
    addToBench bench p s = bench := by
  simp [addToBench, h]

theorem add_to_empty_bench_singleton (p : Pokemon) (s : StadiumCard) :
    addToBench [] p s = [p] := by
  cases s <;> simp [addToBench, stadiumBenchLimit]

theorem add_bench_preserves_existing (bench : List Pokemon) (p : Pokemon) (s : StadiumCard)
    (h : bench.length < stadiumBenchLimit s) (q : Pokemon) (hq : q ∈ bench) :
    q ∈ addToBench bench p s := by
  simp [addToBench, h]; exact Or.inl hq

-- ============================================================
-- Section 5: Bench count and type composition
-- ============================================================

theorem count_by_type_le_length (bench : List Pokemon) (t : EnergyType) :
    countBenchByType bench t ≤ bench.length := by
  simp [countBenchByType]; exact List.length_filter_le _ _

theorem count_by_type_empty (t : EnergyType) :
    countBenchByType [] t = 0 := rfl

theorem bench_remove_decreases_length (bench : List Pokemon) (idx : Nat)
    (h : idx < bench.length) :
    (removeBenchAt bench idx).length = bench.length - 1 := by
  simp [removeBenchAt, List.length_eraseIdx, h]

-- ============================================================
-- Section 6: Stadium transition theorems
-- ============================================================

theorem sky_field_gain_from_none :
    benchSeatDelta StadiumCard.none StadiumCard.skyField = 3 := by decide

theorem collapsed_loss_from_none :
    benchSeatDelta StadiumCard.none StadiumCard.collapsedStadium = -1 := by decide

theorem parallel_city_loss_from_none :
    benchSeatDelta StadiumCard.none StadiumCard.parallelCity = -2 := by decide

theorem sky_field_to_collapsed_loss :
    benchSeatDelta StadiumCard.skyField StadiumCard.collapsedStadium = -4 := by decide

theorem stadium_delta_antisymmetric (a b : StadiumCard) :
    benchSeatDelta a b = -benchSeatDelta b a := by
  cases a <;> cases b <;> decide

theorem stadium_delta_self_zero (s : StadiumCard) :
    benchSeatDelta s s = 0 := by
  cases s <;> decide

theorem sky_field_to_parallel_loss :
    benchSeatDelta StadiumCard.skyField StadiumCard.parallelCity = -5 := by decide

theorem collapsed_to_sky_gain :
    benchSeatDelta StadiumCard.collapsedStadium StadiumCard.skyField = 4 := by decide
