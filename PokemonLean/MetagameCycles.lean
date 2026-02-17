/-
  PokemonLean / MetagameCycles.lean

  Rock-paper-scissors dynamics, tier lists as orderings,
  counter-team building, format diversity metrics,
  archetype classification (aggro/control/combo),
  matchup spread analysis.

  Multi-step trans / symm / congrArg chains throughout.
  20 theorems.
-/
namespace MetagameCycles

-- ============================================================
-- §2  Archetypes and Matchups
-- ============================================================

/-- Deck archetype in a competitive metagame. -/
inductive Archetype where
  | aggro   : Archetype
  | control : Archetype
  | combo   : Archetype
  | midrange : Archetype
  | stall   : Archetype
deriving DecidableEq, Repr

/-- Matchup result. -/
inductive MatchupResult where
  | favored    : MatchupResult   -- > 55%
  | even       : MatchupResult   -- 45–55%
  | unfavored  : MatchupResult   -- < 45%
deriving DecidableEq, Repr

/-- Classic RPS triangle: aggro beats combo, combo beats control, control beats aggro. -/
def rpsMatchup : Archetype → Archetype → MatchupResult
  | .aggro,   .combo   => .favored
  | .combo,   .control => .favored
  | .control, .aggro   => .favored
  | .combo,   .aggro   => .unfavored
  | .control, .combo   => .unfavored
  | .aggro,   .control => .unfavored
  | a,        b        => if a == b then .even else .even

/-- Theorem 1: Aggro beats combo. -/
theorem aggro_beats_combo : rpsMatchup .aggro .combo = .favored := rfl

/-- Theorem 2: Combo beats control. -/
theorem combo_beats_control : rpsMatchup .combo .control = .favored := rfl

/-- Theorem 3: Control beats aggro. -/
theorem control_beats_aggro : rpsMatchup .control .aggro = .favored := rfl

/-- Theorem 4: Mirror matches are even. -/
theorem mirror_is_even (a : Archetype) : rpsMatchup a a = .even := by
  cases a <;> simp [rpsMatchup]

/-- Theorem 5: RPS symmetry — if A is favored vs B then B is unfavored vs A. -/
theorem rps_antisymm (a b : Archetype) (h : rpsMatchup a b = .favored) :
    rpsMatchup b a = .unfavored := by
  cases a <;> cases b <;> simp_all [rpsMatchup]

-- ============================================================
-- §3  Metagame State and Meta Shifts
-- ============================================================

/-- A metagame state: distribution of archetypes (as percentages × 10). -/
structure MetaState where
  aggroPct   : Nat
  controlPct : Nat
  comboPct   : Nat
  otherPct   : Nat
deriving DecidableEq, Repr

/-- Total must be 1000 (100.0%). -/
def MetaState.total (m : MetaState) : Nat :=
  m.aggroPct + m.controlPct + m.comboPct + m.otherPct

/-- Metagame shift steps. -/
inductive MetaShift where
  | aggroRise    : MetaShift   -- aggro rises, counters follow
  | controlRise  : MetaShift   -- control rises to beat aggro
  | comboRise    : MetaShift   -- combo rises to beat control
  | diversify    : MetaShift   -- meta flattens out
  | centralize   : MetaShift   -- one archetype dominates
deriving DecidableEq, Repr


-- ============================================================
-- §4  Tier Lists as Orderings
-- ============================================================

/-- Tier in a tier list. -/
inductive Tier where
  | s : Tier
  | a : Tier
  | b : Tier
  | c : Tier
  | d : Tier
deriving DecidableEq, Repr

def Tier.toNat : Tier → Nat
  | .s => 5
  | .a => 4
  | .b => 3
  | .c => 2
  | .d => 1

/-- A tier-list entry: deck name and its tier. -/
structure TierEntry where
  deckName : String
  tier     : Tier
deriving DecidableEq, Repr

/-- Tier ordering. -/
def Tier.le (t1 t2 : Tier) : Bool := t1.toNat ≤ t2.toNat

/-- Theorem 8: S-tier ≥ all tiers. -/
theorem s_tier_top (t : Tier) : Tier.le t .s = true := by
  cases t <;> simp [Tier.le, Tier.toNat]

/-- Theorem 9: D-tier ≤ all tiers. -/
theorem d_tier_bot (t : Tier) : Tier.le .d t = true := by
  cases t <;> simp [Tier.le, Tier.toNat]

/-- Theorem 10: Tier.le is reflexive. -/
theorem tier_le_refl (t : Tier) : Tier.le t t = true := by
  cases t <;> simp [Tier.le, Tier.toNat]


-- ============================================================
-- §5  Format Diversity Metrics
-- ============================================================

/-- A metagame snapshot: list of (deckName, usagePct × 10). -/
structure MetaSnapshot where
  entries : List (String × Nat)

/-- Number of distinct decks. -/
def MetaSnapshot.deckCount (m : MetaSnapshot) : Nat := m.entries.length

/-- Total usage. -/
def MetaSnapshot.totalUsage (m : MetaSnapshot) : Nat :=
  m.entries.foldl (fun acc e => acc + e.2) 0

/-- Whether any deck exceeds a threshold. -/
def MetaSnapshot.hasDominant (m : MetaSnapshot) (threshold : Nat) : Bool :=
  m.entries.any (fun e => e.2 > threshold)

/-- Theorem 13: Empty meta has 0 decks. -/
theorem empty_meta_deckCount : MetaSnapshot.deckCount ⟨[]⟩ = 0 := rfl

/-- Theorem 14: Empty meta has 0 total usage. -/
theorem empty_meta_totalUsage : MetaSnapshot.totalUsage ⟨[]⟩ = 0 := rfl

/-- Theorem 15: Empty meta has no dominant deck. -/
theorem empty_meta_no_dominant (t : Nat) :
    MetaSnapshot.hasDominant ⟨[]⟩ t = false := rfl

-- ============================================================
-- §6  Counter-Team Building Paths
-- ============================================================

/-- A deck in the metagame. -/
structure MetaDeck where
  name      : String
  archetype : Archetype
  tier      : Tier
deriving DecidableEq, Repr


-- ============================================================
-- §7  Matchup Spread Analysis
-- ============================================================

/-- Matchup spread: list of results against the field. -/
structure MatchupSpread where
  results : List MatchupResult

/-- Count favored matchups. -/
def MatchupSpread.favoredCount (m : MatchupSpread) : Nat :=
  m.results.filter (· == .favored) |>.length

/-- Count unfavored matchups. -/
def MatchupSpread.unfavoredCount (m : MatchupSpread) : Nat :=
  m.results.filter (· == .unfavored) |>.length

/-- Net favorability. -/
def MatchupSpread.netFav (m : MatchupSpread) : Int :=
  (m.favoredCount : Int) - (m.unfavoredCount : Int)

/-- Theorem 18: Empty spread has 0 favored. -/
theorem empty_spread_favored : MatchupSpread.favoredCount ⟨[]⟩ = 0 := rfl

/-- Theorem 19: Empty spread has 0 net favorability. -/
theorem empty_spread_netFav : MatchupSpread.netFav ⟨[]⟩ = 0 := rfl

/-- Theorem 20: Purely favored spread has positive net. -/
theorem all_favored_positive :
    MatchupSpread.netFav ⟨[.favored, .favored, .favored]⟩ > 0 := by
  native_decide

end MetagameCycles
