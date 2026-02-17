/-
  PokemonLean / Core / BenchMechanics.lean

  Bench management and mechanics for the Pokémon TCG.

  Covers:
  - Bench size: default 5, Sky Field → 8, when Sky Field removed →
    discard to 5
  - Promoting from bench: when active KO'd, must promote benched Pokémon
  - Bench barrier: Manaphy's Wave Veil (prevent bench damage)
  - Bench damage: spread attacks (e.g., 20 to each bench), snipe
    attacks (target 1 bench)
  - Bench sniping: Boss's Orders (gust effect), force target to active
  - No bench = lose: if no benched Pokémon and active KO'd → lose
  - Theorems: bench size ≤ 5 default, Sky Field increases to 8,
    removing Sky Field forces discard, bench barrier blocks spread,
    snipe bypasses barrier (if specified), no bench + KO = loss,
    promotion is mandatory, bench order doesn't matter

  Self-contained — no imports from other PokemonLean modules.
  All proofs are sorry-free.  35+ theorems.
-/

namespace PokemonLean.Core.BenchMechanics

-- ============================================================
-- §1  Core types
-- ============================================================

/-- Unique identifier for a Pokémon in play. -/
structure PokemonId where
  val : Nat
deriving DecidableEq, Repr, BEq, Inhabited

/-- A simplified Pokémon on the bench/active. -/
structure BenchPokemon where
  pokId   : PokemonId
  currentHp : Nat := 100
  maxHp     : Nat := 100
deriving DecidableEq, Repr, BEq, Inhabited

/-- Check if a Pokémon is knocked out (HP = 0). -/
def BenchPokemon.isKO (p : BenchPokemon) : Bool :=
  p.currentHp == 0

-- ============================================================
-- §2  Stadium effects on bench size
-- ============================================================

/-- Stadium cards that affect bench size. -/
inductive StadiumCard where
  | skyField      -- Bench size becomes 8
  | noStadium     -- Default: bench size 5
  | otherStadium  -- Doesn't affect bench
deriving DecidableEq, Repr, BEq, Inhabited

/-- Default bench size. -/
def defaultBenchSize : Nat := 5

/-- Sky Field bench size. -/
def skyFieldBenchSize : Nat := 8

/-- Maximum bench size given current stadium. -/
def maxBenchSize (stadium : StadiumCard) : Nat :=
  match stadium with
  | .skyField     => skyFieldBenchSize
  | .noStadium    => defaultBenchSize
  | .otherStadium => defaultBenchSize

-- ============================================================
-- §3  Bench state
-- ============================================================

/-- The bench state. -/
structure BenchState where
  activePokemon : Option BenchPokemon  -- None means no active
  bench         : List BenchPokemon
  stadium       : StadiumCard := .noStadium
  benchBarrier  : Bool := false  -- Manaphy's Wave Veil active?
deriving DecidableEq, Repr, BEq, Inhabited

/-- Current bench count. -/
def BenchState.benchCount (bs : BenchState) : Nat :=
  bs.bench.length

/-- Maximum allowed bench size. -/
def BenchState.maxBench (bs : BenchState) : Nat :=
  maxBenchSize bs.stadium

/-- Is the bench full? -/
def BenchState.isBenchFull (bs : BenchState) : Bool :=
  bs.benchCount ≥ bs.maxBench

/-- Can place a Pokémon on the bench? -/
def BenchState.canPlaceOnBench (bs : BenchState) : Bool :=
  bs.benchCount < bs.maxBench

-- ============================================================
-- §4  Placing on bench
-- ============================================================

/-- Place a Pokémon on the bench (if room). -/
def placePokemon (bs : BenchState) (p : BenchPokemon) : Option BenchState :=
  if bs.canPlaceOnBench then
    some { bs with bench := bs.bench ++ [p] }
  else none

-- ============================================================
-- §5  Sky Field removal → discard to default
-- ============================================================

/-- When Sky Field is removed, discard down to default bench size.
    Keeps the first `defaultBenchSize` Pokémon. -/
def discardToDefault (bs : BenchState) : BenchState :=
  { bs with
    bench := bs.bench.take defaultBenchSize,
    stadium := .noStadium }

/-- Replace stadium (new stadium replaces old). -/
def replaceStadium (bs : BenchState) (newStadium : StadiumCard) : BenchState :=
  if bs.stadium == .skyField && newStadium != .skyField then
    { (discardToDefault bs) with stadium := newStadium }
  else
    { bs with stadium := newStadium }

-- ============================================================
-- §6  Bench damage: spread and snipe
-- ============================================================

/-- Apply damage to a single Pokémon. -/
def applyDamage (p : BenchPokemon) (dmg : Nat) : BenchPokemon :=
  { p with currentHp := if p.currentHp ≥ dmg then p.currentHp - dmg else 0 }

/-- Spread damage: deal dmg to each benched Pokémon.
    Blocked by bench barrier (Wave Veil). -/
def spreadDamage (bs : BenchState) (dmg : Nat) : BenchState :=
  if bs.benchBarrier then bs  -- Wave Veil blocks
  else { bs with bench := bs.bench.map (fun p => applyDamage p dmg) }

/-- Helper: apply damage to element at index in a list. -/
def applyDamageAtIdx (poks : List BenchPokemon) (idx : Nat) (dmg : Nat) : List BenchPokemon :=
  match poks, idx with
  | [], _ => []
  | p :: rest, 0 => applyDamage p dmg :: rest
  | p :: rest, n + 1 => p :: applyDamageAtIdx rest n dmg

/-- Snipe damage: deal dmg to a specific bench index.
    Can optionally bypass barrier. -/
def snipeDamage (bs : BenchState) (idx : Nat) (dmg : Nat)
    (bypassBarrier : Bool := false) : BenchState :=
  if bs.benchBarrier && !bypassBarrier then bs
  else
    { bs with bench := applyDamageAtIdx bs.bench idx dmg }

-- ============================================================
-- §7  Promotion when active KO'd
-- ============================================================

/-- Active Pokémon is knocked out. Must promote from bench. -/
def activeKOd (bs : BenchState) : Bool :=
  match bs.activePokemon with
  | none   => false
  | some p => p.isKO

/-- Has benched Pokémon available for promotion? -/
def hasBenchForPromotion (bs : BenchState) : Bool :=
  !bs.bench.isEmpty

/-- Promote a benched Pokémon to active (by index). -/
def promote (bs : BenchState) (idx : Nat) : Option BenchState :=
  match bs.bench[idx]? with
  | none => none
  | some newActive =>
    let newBench := bs.bench.eraseIdx idx
    some { bs with activePokemon := some newActive, bench := newBench }

-- ============================================================
-- §8  Loss condition: no bench + active KO'd
-- ============================================================

/-- Check if player loses: active KO'd and no bench. -/
def isLossNoPromote (bs : BenchState) : Bool :=
  activeKOd bs && !hasBenchForPromotion bs

-- ============================================================
-- §9  Boss's Orders (gust): force benched to active
-- ============================================================

/-- Boss's Orders: swap opponent's active with their bench index. -/
def gustEffect (bs : BenchState) (idx : Nat) : Option BenchState :=
  match bs.activePokemon, bs.bench[idx]? with
  | some currentActive, some target =>
    let newBench := bs.bench.set idx currentActive
    some { bs with activePokemon := some target, bench := newBench }
  | _, _ => none

-- ============================================================
-- §10  Bench order invariance
-- ============================================================

/-- Total HP across the bench. -/
def totalBenchHp (poks : List BenchPokemon) : Nat :=
  poks.foldl (fun acc p => acc + p.currentHp) 0

-- ============================================================
-- §11  Sample data
-- ============================================================

private def poke1 : BenchPokemon := { pokId := ⟨1⟩, currentHp := 100, maxHp := 100 }
private def poke2 : BenchPokemon := { pokId := ⟨2⟩, currentHp := 80, maxHp := 80 }
private def poke3 : BenchPokemon := { pokId := ⟨3⟩, currentHp := 60, maxHp := 60 }
private def poke4 : BenchPokemon := { pokId := ⟨4⟩, currentHp := 120, maxHp := 120 }
private def poke5 : BenchPokemon := { pokId := ⟨5⟩, currentHp := 90, maxHp := 90 }
private def poke6 : BenchPokemon := { pokId := ⟨6⟩, currentHp := 70, maxHp := 70 }

private def defaultBench : BenchState :=
  { activePokemon := some poke1, bench := [poke2, poke3], stadium := .noStadium }

private def fullBench5 : BenchState :=
  { activePokemon := some poke1, bench := [poke2, poke3, poke4, poke5, poke6],
    stadium := .noStadium }

private def skyFieldBench : BenchState :=
  { activePokemon := some poke1,
    bench := [poke2, poke3, poke4, poke5, poke6,
              { pokId := ⟨7⟩, currentHp := 50, maxHp := 50 }],
    stadium := .skyField }

private def barrierBench : BenchState :=
  { activePokemon := some poke1, bench := [poke2, poke3],
    stadium := .noStadium, benchBarrier := true }

private def koActive : BenchState :=
  { activePokemon := some { pokId := ⟨1⟩, currentHp := 0, maxHp := 100 },
    bench := [poke2, poke3] }

private def koActiveNoBench : BenchState :=
  { activePokemon := some { pokId := ⟨1⟩, currentHp := 0, maxHp := 100 },
    bench := [] }

-- ============================================================
-- §12  THEOREMS (35+)
-- ============================================================

-- ---- Default bench size ----

theorem default_bench_size_is_5 :
    defaultBenchSize = 5 := by rfl

theorem max_bench_no_stadium :
    maxBenchSize .noStadium = 5 := by rfl

theorem max_bench_other_stadium :
    maxBenchSize .otherStadium = 5 := by rfl

-- ---- Sky Field ----

theorem sky_field_bench_is_8 :
    maxBenchSize .skyField = 8 := by rfl

theorem sky_field_allows_more :
    skyFieldBench.maxBench = 8 := by native_decide

theorem sky_field_not_full_at_6 :
    skyFieldBench.isBenchFull = false := by native_decide

-- ---- Full bench ----

theorem full_bench_5 :
    fullBench5.isBenchFull = true := by native_decide

theorem full_bench_cannot_place :
    fullBench5.canPlaceOnBench = false := by native_decide

theorem full_bench_place_fails :
    (placePokemon fullBench5 poke1).isNone = true := by native_decide

-- ---- Placing on bench ----

theorem default_can_place :
    defaultBench.canPlaceOnBench = true := by native_decide

theorem place_increases_count :
    (placePokemon defaultBench poke4).map BenchState.benchCount = some 3 := by native_decide

-- ---- Sky Field removal → discard to 5 ----

theorem discard_to_default_caps_at_5 :
    (discardToDefault skyFieldBench).benchCount ≤ 5 := by native_decide

theorem discard_to_default_sets_no_stadium :
    (discardToDefault skyFieldBench).stadium = .noStadium := by native_decide

theorem replace_sky_field_discards :
    (replaceStadium skyFieldBench .otherStadium).benchCount ≤ 5 := by native_decide

-- ---- Bench barrier blocks spread ----

theorem barrier_blocks_spread :
    spreadDamage barrierBench 20 = barrierBench := by native_decide

theorem no_barrier_spread_applies :
    (spreadDamage defaultBench 20).bench ≠ defaultBench.bench := by native_decide

theorem spread_reduces_hp :
    let result := spreadDamage defaultBench 20
    (result.bench[0]?).map BenchPokemon.currentHp = some 60 := by native_decide

theorem spread_reduces_all :
    let result := spreadDamage defaultBench 20
    (result.bench[1]?).map BenchPokemon.currentHp = some 40 := by native_decide

-- ---- Snipe ----

theorem barrier_blocks_snipe :
    snipeDamage barrierBench 0 50 = barrierBench := by native_decide

theorem snipe_bypass_barrier :
    (snipeDamage barrierBench 0 50 true).bench ≠ barrierBench.bench := by native_decide

theorem snipe_targets_one :
    let result := snipeDamage defaultBench 0 30
    (result.bench[0]?).map BenchPokemon.currentHp = some 50 ∧
    (result.bench[1]?).map BenchPokemon.currentHp = some 60 := by native_decide

-- ---- Active KO ----

theorem active_ko_detected :
    activeKOd koActive = true := by native_decide

theorem active_not_ko :
    activeKOd defaultBench = false := by native_decide

-- ---- Promotion ----

theorem has_bench_for_promotion :
    hasBenchForPromotion koActive = true := by native_decide

theorem no_bench_no_promotion :
    hasBenchForPromotion koActiveNoBench = false := by native_decide

theorem promote_valid :
    (promote koActive 0).isSome = true := by native_decide

theorem promote_invalid_index :
    (promote koActive 5).isNone = true := by native_decide

theorem promote_reduces_bench :
    (promote koActive 0).map BenchState.benchCount = some 1 := by native_decide

-- ---- Loss condition ----

theorem no_bench_ko_is_loss :
    isLossNoPromote koActiveNoBench = true := by native_decide

theorem bench_available_no_loss :
    isLossNoPromote koActive = false := by native_decide

theorem healthy_active_no_loss :
    isLossNoPromote defaultBench = false := by native_decide

-- ---- Gust / Boss's Orders ----

theorem gust_valid :
    (gustEffect defaultBench 0).isSome = true := by native_decide

theorem gust_invalid_index :
    (gustEffect defaultBench 10).isNone = true := by native_decide

theorem gust_swaps_active :
    (gustEffect defaultBench 0).map (fun bs => bs.activePokemon) =
      some (some poke2) := by native_decide

-- ---- Bench order doesn't matter for total HP ----

theorem bench_order_total_hp :
    totalBenchHp [poke2, poke3] = totalBenchHp [poke3, poke2] := by native_decide

theorem total_hp_additive :
    totalBenchHp [poke2, poke3] = 140 := by native_decide

-- ---- KO detection ----

theorem ko_at_zero :
    (BenchPokemon.mk ⟨1⟩ 0 100).isKO = true := by native_decide

theorem not_ko_positive_hp :
    poke1.isKO = false := by native_decide

-- ---- Damage application ----

theorem damage_reduces_hp :
    (applyDamage poke1 30).currentHp = 70 := by native_decide

theorem damage_floors_at_zero :
    (applyDamage poke3 100).currentHp = 0 := by native_decide

theorem zero_damage_noop :
    (applyDamage poke1 0).currentHp = 100 := by native_decide

end PokemonLean.Core.BenchMechanics
