/-
  Core/BenchProtection.lean — Armada 627 File 2/3
  Bench barrier mechanics (Manaphy Wave Veil, Mr. Mime Bench Barrier),
  bench sniping (Boss's Orders, Greninja Star, spread damage),
  damage calculation with protection
-/
import Core.Types

-- ============================================================
-- Section 1: Wave Veil (Manaphy) theorems
-- ============================================================

theorem wave_veil_blocks_all_damage (dmg : Nat) :
    benchDamageBlocked BenchAbility.waveVeil dmg = true := by
  simp [benchDamageBlocked]

theorem wave_veil_effective_damage_zero (dmg : Nat) :
    effectiveBenchDamage BenchAbility.waveVeil dmg = 0 := by
  simp [effectiveBenchDamage, benchDamageBlocked]

theorem wave_veil_blocks_any_amount (n : Nat) :
    effectiveBenchDamage BenchAbility.waveVeil (n * 100) = 0 := by
  simp [effectiveBenchDamage, benchDamageBlocked]

-- ============================================================
-- Section 2: Mr. Mime Bench Barrier theorems
-- ============================================================

theorem bench_barrier_blocks_small_damage :
    benchDamageBlocked BenchAbility.benchBarrier 10 = true := by decide

theorem bench_barrier_blocks_threshold :
    benchDamageBlocked BenchAbility.benchBarrier 20 = true := by decide

theorem bench_barrier_allows_large_damage :
    benchDamageBlocked BenchAbility.benchBarrier 30 = false := by decide

theorem bench_barrier_threshold_boundary :
    benchDamageBlocked BenchAbility.benchBarrier mimeBarrierThreshold = true := by decide

theorem bench_barrier_above_threshold (dmg : Nat) (h : dmg > mimeBarrierThreshold) :
    benchDamageBlocked BenchAbility.benchBarrier dmg = false := by
  simp [benchDamageBlocked, mimeBarrierThreshold] at *; omega

theorem bench_barrier_at_or_below (dmg : Nat) (h : dmg ≤ mimeBarrierThreshold) :
    benchDamageBlocked BenchAbility.benchBarrier dmg = true := by
  simp [benchDamageBlocked, mimeBarrierThreshold] at *; omega

theorem bench_barrier_effective_large (dmg : Nat) (h : dmg > mimeBarrierThreshold) :
    effectiveBenchDamage BenchAbility.benchBarrier dmg = dmg := by
  unfold effectiveBenchDamage
  simp [benchDamageBlocked, mimeBarrierThreshold] at *; omega

theorem bench_barrier_effective_small (dmg : Nat) (h : dmg ≤ mimeBarrierThreshold) :
    effectiveBenchDamage BenchAbility.benchBarrier dmg = 0 := by
  unfold effectiveBenchDamage
  simp [benchDamageBlocked, mimeBarrierThreshold] at *; omega

-- ============================================================
-- Section 3: No protection theorems
-- ============================================================

theorem no_ability_never_blocks (dmg : Nat) :
    benchDamageBlocked BenchAbility.none dmg = false := by rfl

theorem no_ability_full_damage (dmg : Nat) :
    effectiveBenchDamage BenchAbility.none dmg = dmg := by
  simp [effectiveBenchDamage, benchDamageBlocked]

-- ============================================================
-- Section 4: Bench sniping mechanics
-- ============================================================

/-- Apply snipe damage to a specific bench Pokemon -/
def snipeBench (bench : List Pokemon) (idx : Nat) (dmg : Nat)
    (ability : BenchAbility) : List Pokemon :=
  let eff := effectiveBenchDamage ability dmg
  List.mapIdx (fun i p => if i == idx then applyDamage p eff else p) bench

/-- Apply spread damage to all bench Pokemon -/
def spreadDamageBench (bench : List Pokemon) (dmg : Nat)
    (ability : BenchAbility) : List Pokemon :=
  let eff := effectiveBenchDamage ability dmg
  bench.map (fun p => applyDamage p eff)

theorem snipe_preserves_bench_length (bench : List Pokemon) (idx dmg : Nat) (ability : BenchAbility) :
    (snipeBench bench idx dmg ability).length = bench.length := by
  simp [snipeBench, List.length_mapIdx]

theorem spread_preserves_bench_length (bench : List Pokemon) (dmg : Nat) (ability : BenchAbility) :
    (spreadDamageBench bench dmg ability).length = bench.length := by
  simp [spreadDamageBench]

theorem spread_with_wave_veil_no_change (bench : List Pokemon) (dmg : Nat) :
    spreadDamageBench bench dmg BenchAbility.waveVeil = bench := by
  simp [spreadDamageBench, effectiveBenchDamage, benchDamageBlocked, applyDamage]

theorem spread_empty_bench (dmg : Nat) (ability : BenchAbility) :
    spreadDamageBench [] dmg ability = [] := by rfl

theorem snipe_empty_bench (idx dmg : Nat) (ability : BenchAbility) :
    snipeBench [] idx dmg ability = [] := by rfl

-- ============================================================
-- Section 5: Boss's Orders — gust mechanics
-- ============================================================

/-- Boss's Orders: swap a benched Pokemon with the active -/
def bossOrders (board : BoardState) (benchIdx : Nat) : BoardState :=
  if h : benchIdx < board.bench.length then
    let target := board.bench.get ⟨benchIdx, h⟩
    let newBench := match board.active with
      | some a => (removeBenchAt board.bench benchIdx) ++ [a]
      | none => removeBenchAt board.bench benchIdx
    { board with active := some target, bench := newBench }
  else board

theorem boss_orders_sets_target_active (board : BoardState) (idx : Nat)
    (h : idx < board.bench.length) :
    (bossOrders board idx).active = some (board.bench.get ⟨idx, h⟩) := by
  simp [bossOrders, h]

theorem boss_orders_invalid_idx_unchanged (board : BoardState) (idx : Nat)
    (h : ¬ idx < board.bench.length) :
    bossOrders board idx = board := by
  simp [bossOrders, h]

-- ============================================================
-- Section 6: Greninja Star snipe damage values
-- ============================================================

theorem greninja_snipe_passes_barrier :
    benchDamageBlocked BenchAbility.benchBarrier greninjaMoonShuriken = false := by decide

theorem greninja_snipe_blocked_by_wave_veil :
    benchDamageBlocked BenchAbility.waveVeil greninjaMoonShuriken = true := by decide

theorem greninja_effective_no_protection :
    effectiveBenchDamage BenchAbility.none greninjaMoonShuriken = 90 := by decide

theorem greninja_effective_with_barrier :
    effectiveBenchDamage BenchAbility.benchBarrier greninjaMoonShuriken = 90 := by decide

theorem greninja_effective_with_wave_veil :
    effectiveBenchDamage BenchAbility.waveVeil greninjaMoonShuriken = 0 := by decide

-- ============================================================
-- Section 7: Damage application properties
-- ============================================================

theorem apply_damage_reduces_hp (p : Pokemon) (dmg : Nat) :
    (applyDamage p dmg).currentHp ≤ p.currentHp := by
  simp [applyDamage]

theorem apply_zero_damage_unchanged (p : Pokemon) :
    (applyDamage p 0).currentHp = p.currentHp := by
  simp [applyDamage]

theorem apply_damage_floor_zero (p : Pokemon) (dmg : Nat) (h : dmg ≥ p.currentHp) :
    (applyDamage p dmg).currentHp = 0 := by
  simp [applyDamage]; omega

theorem knockout_from_bench_snipe (p : Pokemon) (dmg : Nat) (h : dmg ≥ p.currentHp) :
    isKnockedOut (applyDamage p dmg) = true := by
  simp [isKnockedOut, applyDamage, beq_iff_eq]; omega

theorem effective_damage_le_raw (ability : BenchAbility) (dmg : Nat) :
    effectiveBenchDamage ability dmg ≤ dmg := by
  simp [effectiveBenchDamage]; split <;> omega

theorem no_damage_no_ko (p : Pokemon) (h : p.currentHp > 0) :
    isKnockedOut (applyDamage p 0) = false := by
  simp [isKnockedOut, applyDamage, beq_iff_eq]; omega

theorem spread_no_ability_damages_all (bench : List Pokemon) (dmg : Nat) :
    spreadDamageBench bench dmg BenchAbility.none =
    bench.map (fun p => applyDamage p dmg) := by
  simp [spreadDamageBench, effectiveBenchDamage, benchDamageBlocked]

theorem wave_veil_prevents_ko (p : Pokemon) (dmg : Nat) (hp : p.currentHp > 0) :
    isKnockedOut (applyDamage p (effectiveBenchDamage BenchAbility.waveVeil dmg)) = false := by
  simp [effectiveBenchDamage, benchDamageBlocked, applyDamage, isKnockedOut, beq_iff_eq]; omega
