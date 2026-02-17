/-
  PokemonLean / SpreadDamage.lean

  Spread damage mechanics for the Pokémon TCG:
  - Bench snipe attacks & spread to all opponents' Pokémon
  - Damage spread strategies & bench damage calculation
  - Mr. Mime bench barrier & Manaphy bench protection
  - Spread vs focused damage comparison
  - Multi-target damage distribution

  spread-damage state transitions.
  Multi-step trans / symm / congrArg chains — paths ARE the math.
  20 theorems.
-/

namespace PokemonLean.SpreadDamage
-- ============================================================================
-- §2  Pokémon and Board Types
-- ============================================================================

structure Pokemon where
  name   : String
  hp     : Nat
  damage : Nat
deriving DecidableEq, Repr

def Pokemon.isKO (p : Pokemon) : Bool := p.damage ≥ p.hp

def Pokemon.remainingHP (p : Pokemon) : Int :=
  (p.hp : Int) - (p.damage : Int)

/-- Bench protection abilities. -/
inductive BenchProtection where
  | none
  | mrMimeBarrier    -- blocks all bench damage
  | manaphyWave      -- blocks bench damage from attacks
deriving DecidableEq, Repr

/-- Board state for spread damage analysis. -/
structure Board where
  active     : Pokemon
  bench      : List Pokemon
  protection : BenchProtection
deriving Repr

-- ============================================================================
-- §3  Spread Damage Types
-- ============================================================================

/-- Types of spread attacks. -/
inductive SpreadType where
  | uniformAll (dmg : Nat)         -- same damage to all bench
  | snipeSingle (idx : Nat) (dmg : Nat)  -- target one bench slot
  | activeAndBench (activeDmg benchDmg : Nat)  -- different amounts
  | scaledByBench (perMon : Nat)   -- damage scales with bench count
deriving DecidableEq, Repr

/-- Calculate total damage from a spread attack. -/
def totalSpreadDamage (spread : SpreadType) (benchCount : Nat) : Nat :=
  match spread with
  | .uniformAll dmg => dmg * benchCount
  | .snipeSingle _ dmg => dmg
  | .activeAndBench activeDmg benchDmg => activeDmg + benchDmg * benchCount
  | .scaledByBench perMon => perMon * benchCount

/-- Focused attack: all damage on active. -/
def focusedDamage (dmg : Nat) : Nat := dmg

-- ============================================================================
-- §4  Bench Protection Logic
-- ============================================================================

/-- Whether bench damage is blocked. -/
def benchDamageBlocked (prot : BenchProtection) : Bool :=
  match prot with
  | .none => false
  | .mrMimeBarrier => true
  | .manaphyWave => true

/-- Apply uniform spread to bench. -/
def applyUniformSpread (bench : List Pokemon) (dmg : Nat)
    (prot : BenchProtection) : List Pokemon :=
  if benchDamageBlocked prot then bench
  else bench.map (fun p => { p with damage := p.damage + dmg })

/-- Snipe a specific bench slot. -/
def applySnipeAux (bench : List Pokemon) (idx : Nat) (dmg : Nat)
    (cur : Nat := 0) : List Pokemon :=
  match bench with
  | [] => []
  | p :: rest =>
    let p' := if cur == idx then { p with damage := p.damage + dmg } else p
    p' :: applySnipeAux rest idx dmg (cur + 1)

def applySnipe (bench : List Pokemon) (idx : Nat) (dmg : Nat)
    (prot : BenchProtection) : List Pokemon :=
  if benchDamageBlocked prot then bench
  else applySnipeAux bench idx dmg

/-- Count KOs on bench. -/
def benchKOCount (bench : List Pokemon) : Nat :=
  bench.filter Pokemon.isKO |>.length

-- ============================================================================
-- §5  Core Theorems: Protection
-- ============================================================================

/-- Theorem 1: Mr. Mime barrier blocks all uniform spread. -/
theorem mrMime_blocks_spread (bench : List Pokemon) (dmg : Nat) :
    applyUniformSpread bench dmg .mrMimeBarrier = bench := by
  simp [applyUniformSpread, benchDamageBlocked]

/-- Theorem 2: Manaphy blocks all uniform spread. -/
theorem manaphy_blocks_spread (bench : List Pokemon) (dmg : Nat) :
    applyUniformSpread bench dmg .manaphyWave = bench := by
  simp [applyUniformSpread, benchDamageBlocked]

/-- Theorem 3: No protection means damage applies. -/
theorem no_protection_spread (bench : List Pokemon) (dmg : Nat) :
    applyUniformSpread bench dmg .none =
    bench.map (fun p => { p with damage := p.damage + dmg }) := by
  simp [applyUniformSpread, benchDamageBlocked]

/-- Theorem 4: Mr. Mime blocks snipe. -/
theorem mrMime_blocks_snipe (bench : List Pokemon) (idx dmg : Nat) :
    applySnipe bench idx dmg .mrMimeBarrier = bench := by
  simp [applySnipe, benchDamageBlocked]

/-- Theorem 5: Manaphy blocks snipe. -/
theorem manaphy_blocks_snipe (bench : List Pokemon) (idx dmg : Nat) :
    applySnipe bench idx dmg .manaphyWave = bench := by
  simp [applySnipe, benchDamageBlocked]

-- ============================================================================
-- §6  Spread Damage Computation
-- ============================================================================

/-- Theorem 6: Uniform spread to empty bench does nothing. -/
theorem spread_empty_bench (dmg : Nat) (prot : BenchProtection) :
    applyUniformSpread [] dmg prot = [] := by
  unfold applyUniformSpread benchDamageBlocked
  cases prot <;> simp [List.map]

/-- Theorem 7: Total spread of uniform all scales linearly. -/
theorem total_uniform_scales (dmg benchCount : Nat) :
    totalSpreadDamage (.uniformAll dmg) benchCount = dmg * benchCount := rfl

/-- Theorem 8: Total active-and-bench damage decomposition. -/
theorem total_active_bench (aDmg bDmg benchCount : Nat) :
    totalSpreadDamage (.activeAndBench aDmg bDmg) benchCount =
    aDmg + bDmg * benchCount := rfl

/-- Theorem 9: Snipe total is independent of bench count. -/
theorem snipe_independent (idx dmg benchCount : Nat) :
    totalSpreadDamage (.snipeSingle idx dmg) benchCount = dmg := rfl

/-- Theorem 10: Scaled damage on empty bench is zero. -/
theorem scaled_empty_bench (perMon : Nat) :
    totalSpreadDamage (.scaledByBench perMon) 0 = 0 := by
  simp [totalSpreadDamage]

-- ============================================================================
-- §7  Spread vs Focused Comparison
-- ============================================================================

/-- Theorem 11: Focused is better for single-target KO when damage > spread. -/
theorem focused_more_single_target (focDmg spreadDmg : Nat)
    (h : focDmg > spreadDmg) :
    focusedDamage focDmg > totalSpreadDamage (.uniformAll spreadDmg) 1 := by
  simp [focusedDamage, totalSpreadDamage, Nat.mul_one]
  exact h

/-- Theorem 12: Spread outdamages focused when bench is large enough. -/
theorem spread_more_total (spreadDmg focDmg benchCount : Nat)
    (h : spreadDmg * benchCount > focDmg) :
    totalSpreadDamage (.uniformAll spreadDmg) benchCount >
    focusedDamage focDmg := by
  simp [totalSpreadDamage, focusedDamage]
  exact h

-- ============================================================================
-- §8  Spread Damage Path Traces
-- ============================================================================

structure SpreadState where
  activeDmg   : Nat
  benchDmgs   : List Nat
  protectionOn : Bool
  kos          : Nat
deriving DecidableEq, Repr

def SpreadState.benchCount (s : SpreadState) : Nat := s.benchDmgs.length

def SpreadState.totalBenchDmg (s : SpreadState) : Nat :=
  s.benchDmgs.foldl (· + ·) 0

/-- Apply uniform spread to state. -/
def SpreadState.applySpread (s : SpreadState) (dmg : Nat) : SpreadState :=
  if s.protectionOn then s
  else { s with benchDmgs := s.benchDmgs.map (· + dmg) }

/-- Apply snipe to state at index. -/
def SpreadState.applySnipe (s : SpreadState) (idx dmg : Nat) : SpreadState :=
  if s.protectionOn then s
  else
    let rec go (ds : List Nat) (cur : Nat) : List Nat :=
      match ds with
      | [] => []
      | d :: rest =>
        (if cur == idx then d + dmg else d) :: go rest (cur + 1)
    { s with benchDmgs := go s.benchDmgs 0 }

/-- Apply focused damage to active. -/
def SpreadState.applyFocused (s : SpreadState) (dmg : Nat) : SpreadState :=
  { s with activeDmg := s.activeDmg + dmg }

/-- Count KOs given HP thresholds. -/
def SpreadState.countKOs (s : SpreadState) (hps : List Nat) : Nat :=
  (s.benchDmgs.zip hps).filter (fun (d, hp) => d ≥ hp) |>.length

-- ============================================================================
-- §9  Path-Traced Spread Sequences
-- ============================================================================


-- ============================================================================
-- §10  Multi-Turn Spread Paths
-- ============================================================================


-- ============================================================================
-- §11  Protection Toggle Paths
-- ============================================================================

/-- Enable protection (e.g. play Manaphy). -/
def SpreadState.enableProtection (s : SpreadState) : SpreadState :=
  { s with protectionOn := true }

/-- Disable protection (e.g. Boss's Orders KOs Manaphy). -/
def SpreadState.disableProtection (s : SpreadState) : SpreadState :=
  { s with protectionOn := false }

/-- Theorem 18: Protection blocks spread — state unchanged. -/
theorem protection_blocks_spread (s : SpreadState) (dmg : Nat)
    (h : s.protectionOn = true) :
    s.applySpread dmg = s := by
  simp [SpreadState.applySpread, h]

/-- Theorem 19: Protection blocks snipe — state unchanged. -/
theorem protection_blocks_snipe (s : SpreadState) (idx dmg : Nat)
    (h : s.protectionOn = true) :
    s.applySnipe idx dmg = s := by
  simp [SpreadState.applySnipe, h]


end PokemonLean.SpreadDamage
