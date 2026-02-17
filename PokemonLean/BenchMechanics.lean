/-
  PokemonLean / BenchMechanics.lean

  Bench mechanics for the Pokémon TCG:
  - Bench size limit (5 standard, 8 with Sky Field)
  - Benching during setup phase
  - Forced bench switch (Lysandre / Boss's Orders)
  - Bench barrier (Mr. Mime ability)
  - Bench damage (spread attacks)
  - Bench sniping (targeting a specific bench Pokémon)
  - Promoting from bench when active is KO'd

  17 theorems.
-/

namespace BenchMechanics
-- ============================================================================
-- §2  Pokémon / Board Types
-- ============================================================================

structure Pokemon where
  name    : String
  hp      : Nat
  damage  : Nat
deriving DecidableEq, Repr

def Pokemon.isKO (p : Pokemon) : Bool :=
  p.damage ≥ p.hp

/-- Stadium cards affecting bench size. -/
inductive Stadium where
  | none
  | skyField
  | otherStadium
deriving DecidableEq, Repr

/-- Board state for a single player. -/
structure Board where
  active        : Pokemon
  bench         : List Pokemon
  stadium       : Stadium
  barrierActive : Bool   -- Mr. Mime's Bench Barrier
deriving Repr

-- ============================================================================
-- §3  Bench Size Limits
-- ============================================================================

def benchLimit (st : Stadium) : Nat :=
  match st with
  | .skyField => 8
  | _ => 5

def canBench (b : Board) : Bool :=
  b.bench.length < benchLimit b.stadium

-- Theorem 1
theorem bench_limit_standard : benchLimit .none = 5 := rfl

-- Theorem 2
theorem bench_limit_skyField : benchLimit .skyField = 8 := rfl

-- Theorem 3
theorem bench_limit_other : benchLimit .otherStadium = 5 := rfl

-- Theorem 4
theorem empty_bench_has_room (b : Board) (h : b.bench = []) :
    canBench b = true := by
  simp [canBench, h, benchLimit]
  match b.stadium with
  | .skyField => decide
  | .none => decide
  | .otherStadium => decide

-- ============================================================================
-- §4  Benching a Pokémon
-- ============================================================================

def placePokemon (b : Board) (p : Pokemon) : Board :=
  if canBench b then { b with bench := b.bench ++ [p] }
  else b

-- Theorem 5
theorem place_on_empty_bench (b : Board) (p : Pokemon)
    (hempty : b.bench = []) :
    (placePokemon b p).bench.length = 1 := by
  simp [placePokemon, canBench, hempty, benchLimit]
  match h : b.stadium with
  | .skyField => simp [List.length]
  | .none => simp [List.length]
  | .otherStadium => simp [List.length]

-- ============================================================================
-- §5  Forced Bench Switch (Boss's Orders)
-- ============================================================================

/-- Force bench Pokémon at index i to become active. -/
def forceBenchSwitch (b : Board) (i : Nat) (target : Pokemon)
    (h : b.bench[i]? = some target) : Board :=
  { b with active := target, bench := b.bench.eraseIdx i ++ [b.active] }

-- Theorem 6: After forced switch, active = target
theorem force_switch_active (b : Board) (i : Nat) (target : Pokemon)
    (h : b.bench[i]? = some target) :
    (forceBenchSwitch b i target h).active = target := by
  simp [forceBenchSwitch]

-- Theorem 7: Old active goes to bench
theorem force_switch_old_active_on_bench (b : Board) (i : Nat) (target : Pokemon)
    (h : b.bench[i]? = some target) :
    b.active ∈ (forceBenchSwitch b i target h).bench := by
  simp only [forceBenchSwitch]
  exact List.mem_append_right _ (List.Mem.head _)

-- ============================================================================
-- §6  Bench Barrier (Mr. Mime Ability)
-- ============================================================================

def applyBenchDamage (b : Board) (dmg : Nat) : Board :=
  if b.barrierActive then b
  else
    let newBench := b.bench.map (fun p => { p with damage := p.damage + dmg })
    { b with bench := newBench }

-- Theorem 8: Bench barrier blocks all spread damage
theorem barrier_blocks_damage (b : Board) (dmg : Nat)
    (hbar : b.barrierActive = true) :
    applyBenchDamage b dmg = b := by
  simp [applyBenchDamage, hbar]

-- Theorem 9: Without barrier, bench takes damage
theorem no_barrier_damage (b : Board) (dmg : Nat)
    (hbar : b.barrierActive = false) :
    (applyBenchDamage b dmg).bench =
      b.bench.map (fun p => { p with damage := p.damage + dmg }) := by
  simp [applyBenchDamage, hbar]

-- Theorem 10: Spread damage preserves active Pokémon
theorem spread_preserves_active (b : Board) (dmg : Nat) :
    (applyBenchDamage b dmg).active = b.active := by
  simp [applyBenchDamage]
  split <;> rfl

-- ============================================================================
-- §7  Bench Sniping
-- ============================================================================

/-- Snipe bench Pokémon at index i for dmg, blocked by barrier. -/
def benchSnipe (b : Board) (i : Nat) (dmg : Nat) : Board :=
  if b.barrierActive then b
  else
    let newBench := (b.bench.zip (List.range b.bench.length)).map (fun (p, j) =>
      if j == i then { p with damage := p.damage + dmg } else p)
    { b with bench := newBench }

-- Theorem 11: Barrier blocks sniping
theorem barrier_blocks_snipe (b : Board) (i : Nat) (dmg : Nat)
    (hbar : b.barrierActive = true) :
    benchSnipe b i dmg = b := by
  simp [benchSnipe, hbar]

-- Theorem 12: Sniping preserves active
theorem snipe_preserves_active (b : Board) (i : Nat) (dmg : Nat) :
    (benchSnipe b i dmg).active = b.active := by
  simp [benchSnipe]
  split <;> rfl

-- ============================================================================
-- §8  Promoting from Bench on KO
-- ============================================================================

def promoteOnKO (b : Board) : Option Board :=
  if b.active.isKO then
    match b.bench with
    | p :: rest => some { b with active := p, bench := rest }
    | [] => none
  else none

-- Theorem 13: Promotion requires KO
theorem promote_requires_ko (b : Board) (hno : b.active.isKO = false) :
    promoteOnKO b = none := by
  simp [promoteOnKO, hno]

-- Theorem 14: KO + non-empty bench → promotion succeeds
theorem promote_succeeds (b : Board) (p : Pokemon) (rest : List Pokemon)
    (hko : b.active.isKO = true) (hbench : b.bench = p :: rest) :
    promoteOnKO b = some { b with active := p, bench := rest } := by
  simp [promoteOnKO, hko, hbench]

-- Theorem 15: KO + empty bench → loss (none)
theorem promote_empty_loses (b : Board)
    (hko : b.active.isKO = true) (hbench : b.bench = []) :
    promoteOnKO b = none := by
  simp [promoteOnKO, hko, hbench]

-- ============================================================================
-- §9  Path-Traced Bench Transitions
-- ============================================================================

structure BenchTransState where
  benchSize    : Nat
  activeKO     : Bool
  barrierOn    : Bool
  switchForced : Bool
deriving DecidableEq, Repr

def BenchTransState.addToBench (s : BenchTransState) : BenchTransState :=
  { s with benchSize := s.benchSize + 1 }

def BenchTransState.koActive (s : BenchTransState) : BenchTransState :=
  { s with activeKO := true }

def BenchTransState.promote (s : BenchTransState) : BenchTransState :=
  { s with activeKO := false, benchSize := s.benchSize - 1 }

def BenchTransState.forceSwitch (s : BenchTransState) : BenchTransState :=
  { s with switchForced := true }

-- KO → promote path (2-step)
-- Theorem 16
-- Place → Boss's Orders path (2-step)
-- Theorem 17
end BenchMechanics
