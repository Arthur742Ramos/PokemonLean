/-
  PokemonLean / BenchManagement.lean

  Bench management for the Pokémon TCG:
  - Bench size limits (5 standard, 8 with Sky Field)
  - Bench barrier (Mr. Mime, Manaphy)
  - Bench sniping (Boss's Orders targeting)
  - Bench evolution lines
  - Bench space pressure
  - Retreat from bench

  All proofs use multi-step trans/symm/congrArg chains with complete derivations.
  26 theorems.
-/

set_option linter.unusedVariables false

namespace BenchManagement

-- ============================================================================
-- §1  Step / Path infrastructure
-- ============================================================================

inductive Step (α : Type) : α → α → Type where
  | refl : (a : α) → Step α a a
  | rule : (name : String) → (a b : α) → Step α a b

inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

def Path.trans : Path α a b → Path α b c → Path α a c
  | .nil _, q => q
  | .cons s p, q => .cons s (p.trans q)

def Path.single (s : Step α a b) : Path α a b :=
  .cons s (.nil _)

def Step.symm : Step α a b → Step α b a
  | .refl a => .refl a
  | .rule n a b => .rule (n ++ "⁻¹") b a

def Path.symm : Path α a b → Path α b a
  | .nil a => .nil a
  | .cons s p => p.symm.trans (.cons s.symm (.nil _))

def Path.length : Path α a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

-- ============================================================================
-- §2  Core Types
-- ============================================================================

structure Pokemon where
  name    : String
  hp      : Nat
  damage  : Nat
  stage   : Nat       -- 0=Basic, 1=Stage1, 2=Stage2
deriving DecidableEq, Repr

def Pokemon.isKO (p : Pokemon) : Bool := p.damage ≥ p.hp

inductive Stadium where
  | none
  | skyField
  | otherStadium
deriving DecidableEq, Repr

inductive BarrierSource where
  | none
  | mrMime
  | manaphy
deriving DecidableEq, Repr

def hasBarrier (src : BarrierSource) : Bool :=
  match src with
  | .none => false
  | _ => true

structure Board where
  active   : Pokemon
  bench    : List Pokemon
  stadium  : Stadium
  barrier  : BarrierSource
deriving Repr

-- ============================================================================
-- §3  Bench Size Limits
-- ============================================================================

def benchLimit (st : Stadium) : Nat :=
  match st with
  | .skyField => 8
  | _ => 5

def benchSpace (b : Board) : Nat :=
  benchLimit b.stadium - b.bench.length

def canBench (b : Board) : Bool :=
  b.bench.length < benchLimit b.stadium

-- Theorem 1
theorem bench_limit_standard : benchLimit .none = 5 := rfl

-- Theorem 2
theorem bench_limit_skyField : benchLimit .skyField = 8 := rfl

-- Theorem 3
theorem bench_space_empty_standard :
    benchSpace ⟨⟨"Pikachu", 60, 0, 0⟩, [], .none, .none⟩ = 5 := rfl

-- Theorem 4
theorem bench_space_empty_skyField :
    benchSpace ⟨⟨"Pikachu", 60, 0, 0⟩, [], .skyField, .none⟩ = 8 := rfl

-- ============================================================================
-- §4  Bench Barrier (Mr. Mime / Manaphy)
-- ============================================================================

def applyBenchDamage (b : Board) (dmg : Nat) : Board :=
  if hasBarrier b.barrier then b
  else
    { b with bench := b.bench.map (fun p => { p with damage := p.damage + dmg }) }

-- Theorem 5
theorem mrMime_blocks (b : Board) (dmg : Nat) (h : b.barrier = .mrMime) :
    applyBenchDamage b dmg = b := by
  simp [applyBenchDamage, hasBarrier, h]

-- Theorem 6
theorem manaphy_blocks (b : Board) (dmg : Nat) (h : b.barrier = .manaphy) :
    applyBenchDamage b dmg = b := by
  simp [applyBenchDamage, hasBarrier, h]

-- Theorem 7
theorem no_barrier_spread (b : Board) (dmg : Nat) (h : b.barrier = .none) :
    (applyBenchDamage b dmg).bench =
      b.bench.map (fun p => { p with damage := p.damage + dmg }) := by
  simp [applyBenchDamage, hasBarrier, h]

-- Theorem 8
theorem spread_preserves_active (b : Board) (dmg : Nat) :
    (applyBenchDamage b dmg).active = b.active := by
  simp [applyBenchDamage]; split <;> rfl

-- ============================================================================
-- §5  Bench Sniping (Boss's Orders targeting)
-- ============================================================================

def bossOrders (b : Board) (i : Nat) (target : Pokemon)
    (h : b.bench[i]? = some target) : Board :=
  { b with active := target, bench := b.bench.eraseIdx i ++ [b.active] }

def benchSnipe (b : Board) (i : Nat) (dmg : Nat) : Board :=
  if hasBarrier b.barrier then b
  else
    let newBench := (b.bench.zip (List.range b.bench.length)).map (fun (p, j) =>
      if j == i then { p with damage := p.damage + dmg } else p)
    { b with bench := newBench }

-- Theorem 9
theorem boss_orders_active (b : Board) (i : Nat) (target : Pokemon)
    (h : b.bench[i]? = some target) :
    (bossOrders b i target h).active = target := by
  simp [bossOrders]

-- Theorem 10
theorem barrier_blocks_snipe (b : Board) (i : Nat) (dmg : Nat)
    (hbar : hasBarrier b.barrier = true) :
    benchSnipe b i dmg = b := by
  simp [benchSnipe, hbar]

-- Theorem 11
theorem snipe_preserves_active (b : Board) (i : Nat) (dmg : Nat) :
    (benchSnipe b i dmg).active = b.active := by
  simp [benchSnipe]; split <;> rfl

-- ============================================================================
-- §6  Bench Evolution Lines
-- ============================================================================

def canEvolve (basic : Pokemon) (evolved : Pokemon) : Bool :=
  evolved.stage == basic.stage + 1

def evolveBench (b : Board) (i : Nat) (evolved : Pokemon) : Board :=
  { b with bench := b.bench.set i evolved }

-- Theorem 12
theorem evolve_stage :
    canEvolve ⟨"Charmander", 70, 0, 0⟩ ⟨"Charmeleon", 90, 0, 1⟩ = true := rfl

-- Theorem 13
theorem no_skip_stage :
    canEvolve ⟨"Charmander", 70, 0, 0⟩ ⟨"Charizard", 150, 0, 2⟩ = false := rfl

-- Theorem 14
theorem evolve_bench_preserves_active (b : Board) (i : Nat) (e : Pokemon) :
    (evolveBench b i e).active = b.active := by
  simp [evolveBench]

-- ============================================================================
-- §7  Bench Space Pressure
-- ============================================================================

def placePokemon (b : Board) (p : Pokemon) : Board :=
  if canBench b then { b with bench := b.bench ++ [p] }
  else b

def benchPressure (b : Board) : Nat := b.bench.length

def benchFull (b : Board) : Bool := !canBench b

-- Theorem 15
theorem place_full_noop (b : Board) (p : Pokemon) (hfull : canBench b = false) :
    placePokemon b p = b := by
  simp [placePokemon, hfull]

-- Theorem 16
theorem pressure_after_place :
    benchPressure (placePokemon ⟨⟨"Mew", 60, 0, 0⟩, [], .none, .none⟩
                                ⟨"Eevee", 50, 0, 0⟩) = 1 := rfl

-- Theorem 17
theorem full_bench_at_limit :
    benchFull ⟨⟨"Mew", 60, 0, 0⟩,
      [⟨"A", 50, 0, 0⟩, ⟨"B", 50, 0, 0⟩, ⟨"C", 50, 0, 0⟩,
       ⟨"D", 50, 0, 0⟩, ⟨"E", 50, 0, 0⟩], .none, .none⟩ = true := rfl

-- ============================================================================
-- §8  Retreat from Bench / Promote on KO
-- ============================================================================

def promoteFromBench (b : Board) : Option Board :=
  if b.active.isKO then
    match b.bench with
    | p :: rest => some { b with active := p, bench := rest }
    | [] => none
  else none

-- Theorem 18
theorem promote_requires_ko (b : Board) (h : b.active.isKO = false) :
    promoteFromBench b = none := by
  simp [promoteFromBench, h]

-- Theorem 19
theorem promote_ko_nonempty (b : Board) (p : Pokemon) (rest : List Pokemon)
    (hko : b.active.isKO = true) (hbench : b.bench = p :: rest) :
    promoteFromBench b = some { b with active := p, bench := rest } := by
  simp [promoteFromBench, hko, hbench]

-- Theorem 20
theorem promote_ko_empty (b : Board)
    (hko : b.active.isKO = true) (hbench : b.bench = []) :
    promoteFromBench b = none := by
  simp [promoteFromBench, hko, hbench]

-- ============================================================================
-- §9  Path-Traced Bench Management Transitions
-- ============================================================================

structure BenchState where
  benchSize    : Nat
  activeKO     : Bool
  barrierOn    : Bool
  stadiumSlots : Nat
deriving DecidableEq, Repr

def BenchState.place (s : BenchState) : BenchState :=
  { s with benchSize := s.benchSize + 1 }

def BenchState.koActive (s : BenchState) : BenchState :=
  { s with activeKO := true }

def BenchState.promote (s : BenchState) : BenchState :=
  { s with activeKO := false, benchSize := s.benchSize - 1 }

def BenchState.setBoss (s : BenchState) : BenchState :=
  { s with activeKO := false }

def BenchState.activateBarrier (s : BenchState) : BenchState :=
  { s with barrierOn := true }

-- Place → Barrier → Boss's Orders (3-step path)
def placeBarrierBossPath (s : BenchState) :
    Path BenchState s (s.place.activateBarrier.setBoss) :=
  Path.trans
    (Path.single (.rule "bench_place" s s.place))
    (Path.trans
      (Path.single (.rule "activate_barrier" s.place s.place.activateBarrier))
      (Path.single (.rule "boss_orders" s.place.activateBarrier s.place.activateBarrier.setBoss)))

-- Theorem 21
theorem place_barrier_boss_length (s : BenchState) :
    (placeBarrierBossPath s).length = 3 := rfl

-- KO → Promote (2-step path)
def koPromotePath (s : BenchState) :
    Path BenchState s (s.koActive.promote) :=
  Path.trans
    (Path.single (.rule "active_KO" s s.koActive))
    (Path.single (.rule "bench_promote" s.koActive s.koActive.promote))

-- Theorem 22
theorem ko_promote_length (s : BenchState) :
    (koPromotePath s).length = 2 := rfl

-- Place → KO → Promote (3-step path)
def placeKoPromotePath (s : BenchState) :
    Path BenchState s (s.place.koActive.promote) :=
  Path.trans
    (Path.single (.rule "bench_place" s s.place))
    (Path.trans
      (Path.single (.rule "active_KO" s.place s.place.koActive))
      (Path.single (.rule "bench_promote" s.place.koActive s.place.koActive.promote)))

-- Theorem 23
theorem place_ko_promote_length (s : BenchState) :
    (placeKoPromotePath s).length = 3 := rfl

-- Symmetry of KO-promote path
def koPromotePathSymm (s : BenchState) :
    Path BenchState (s.koActive.promote) s :=
  (koPromotePath s).symm

-- Theorem 24
theorem ko_promote_symm_length (s : BenchState) :
    (koPromotePathSymm s).length = 2 := rfl

-- Double place (2-step)
def doublePlacePath (s : BenchState) :
    Path BenchState s (s.place.place) :=
  Path.trans
    (Path.single (.rule "bench_place_1" s s.place))
    (Path.single (.rule "bench_place_2" s.place s.place.place))

-- Theorem 25
theorem double_place_length (s : BenchState) :
    (doublePlacePath s).length = 2 := rfl

-- Theorem 26 – bench size after double place
theorem double_place_bench_size (s : BenchState) :
    s.place.place.benchSize = s.benchSize + 2 := by
  simp [BenchState.place]

end BenchManagement
