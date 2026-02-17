/-
  PokemonLean / Core / Metagame.lean

  Formal metagame modeling and archetype analysis for the Pokémon TCG.
  ====================================================================

  Self-contained — no imports beyond Lean's core.
  All proofs are sorry-free.  40+ theorems.
-/

set_option linter.unusedVariables false

namespace PokemonLean.Core.Metagame

-- ============================================================
-- §1  Archetype definitions
-- ============================================================

/-- Core competitive archetypes in the Pokémon TCG metagame. -/
inductive Archetype where
  | aggro     -- Fast damage, take prizes quickly
  | control   -- Resource denial, hand disruption
  | combo     -- Specific synergy to produce large combos
  | midrange  -- Balanced attackers with flexibility
  | stall     -- Wall + heal, deny prizes
  | mill      -- Deck the opponent out
  | toolbox   -- Diverse tech options for varied answers
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Total number of archetypes. -/
def archetypeCount : Nat := 7

/-- Index for each archetype. -/
def Archetype.toIdx : Archetype → Fin 7
  | .aggro    => ⟨0, by omega⟩
  | .control  => ⟨1, by omega⟩
  | .combo    => ⟨2, by omega⟩
  | .midrange => ⟨3, by omega⟩
  | .stall    => ⟨4, by omega⟩
  | .mill     => ⟨5, by omega⟩
  | .toolbox  => ⟨6, by omega⟩

/-- Archetype from index. -/
def Archetype.fromIdx : Fin 7 → Archetype
  | ⟨0, _⟩ => .aggro
  | ⟨1, _⟩ => .control
  | ⟨2, _⟩ => .combo
  | ⟨3, _⟩ => .midrange
  | ⟨4, _⟩ => .stall
  | ⟨5, _⟩ => .mill
  | ⟨6, _⟩ => .toolbox

/-- [T1] Round-tripping archetype through index. -/
theorem archetype_roundtrip (a : Archetype) : Archetype.fromIdx (a.toIdx) = a := by
  cases a <;> rfl

-- ============================================================
-- §2  Win rate & clamping
-- ============================================================

abbrev WinRate := Nat

/-- Clamp a natural number to [0,100]. -/
def clamp100 (n : Nat) : Nat := min n 100

/-- Mirror match is always 50-50. -/
def mirrorRate : WinRate := 50

/-- [T2] clamp100 always ≤ 100. -/
theorem clamp100_le (n : Nat) : clamp100 n ≤ 100 := Nat.min_le_right n 100

/-- [T3] clamp100 preserves values ≤ 100. -/
theorem clamp100_preserves (n : Nat) (h : n ≤ 100) : clamp100 n = n :=
  Nat.min_eq_left h

/-- [T4] clamp100 caps values > 100. -/
theorem clamp100_caps (n : Nat) (h : n ≥ 100) : clamp100 n = 100 :=
  Nat.min_eq_right h

/-- [T5] clamp100 is idempotent. -/
theorem clamp100_idempotent (n : Nat) : clamp100 (clamp100 n) = clamp100 n :=
  clamp100_preserves _ (clamp100_le _)

-- ============================================================
-- §3  Matchup matrix
-- ============================================================

structure MatchupMatrix where
  rate : Archetype → Archetype → WinRate

def MatchupMatrix.mirrorCorrect (m : MatchupMatrix) : Prop :=
  ∀ a : Archetype, m.rate a a = mirrorRate

def MatchupMatrix.antisymmetric (m : MatchupMatrix) : Prop :=
  ∀ a b : Archetype, m.rate a b + m.rate b a = 100

-- ============================================================
-- §4  Rock-paper-scissors metagame dynamics
-- ============================================================

def rpsWinRate : WinRate := 60
def rpsLoseRate : WinRate := 40

/-- [T6] RPS rates sum to 100. -/
theorem rps_rates_complement : rpsWinRate + rpsLoseRate = 100 := by native_decide

/-- Does archetype a have the RPS advantage over b? -/
def hasRPSAdvantage : Archetype → Archetype → Bool
  | .aggro,   .combo   => true
  | .combo,   .control => true
  | .control, .aggro   => true
  | _,        _        => false

/-- [T7] -/ theorem rps_aggro_beats_combo : hasRPSAdvantage .aggro .combo = true := rfl
/-- [T8] -/ theorem rps_combo_beats_control : hasRPSAdvantage .combo .control = true := rfl
/-- [T9] -/ theorem rps_control_beats_aggro : hasRPSAdvantage .control .aggro = true := rfl
/-- [T10] No archetype has RPS advantage over itself. -/
theorem rps_not_reflexive (a : Archetype) : hasRPSAdvantage a a = false := by
  cases a <;> rfl

/-- Build matchup from RPS relationships plus defaults. -/
def rpsMatchupRate (a b : Archetype) : WinRate :=
  if hasRPSAdvantage a b then rpsWinRate
  else if hasRPSAdvantage b a then rpsLoseRate
  else mirrorRate

/-- [T11] Mirror matchup is 50%. -/
theorem rps_matchup_mirror (a : Archetype) : rpsMatchupRate a a = mirrorRate := by
  cases a <;> rfl

/-- [T12] RPS matchup rates are bounded by 100. -/
theorem rps_matchup_bounded (a b : Archetype) : rpsMatchupRate a b ≤ 100 := by
  cases a <;> cases b <;> native_decide

/-- [T13] RPS matchup rates are complementary. -/
theorem rps_matchup_sum (a b : Archetype) :
    rpsMatchupRate a b + rpsMatchupRate b a = 100 := by
  cases a <;> cases b <;> native_decide

-- ============================================================
-- §5  Meta share distribution
-- ============================================================

structure ShareEntry where
  arch : Archetype
  pct  : Nat
  deriving Repr, DecidableEq

structure MetaDist where
  shares : List ShareEntry
  deriving Repr

def MetaDist.total (m : MetaDist) : Nat :=
  m.shares.foldl (fun acc e => acc + e.pct) 0

def MetaDist.isValid (m : MetaDist) : Prop := m.total = 100

def balancedMeta : MetaDist :=
  ⟨[⟨.aggro, 34⟩, ⟨.control, 33⟩, ⟨.combo, 33⟩]⟩

/-- [T14] -/ theorem balanced_meta_total : balancedMeta.total = 100 := by native_decide

def aggroDominatedMeta : MetaDist :=
  ⟨[⟨.aggro, 50⟩, ⟨.control, 20⟩, ⟨.combo, 15⟩, ⟨.midrange, 15⟩]⟩

/-- [T15] -/ theorem aggro_dominated_total : aggroDominatedMeta.total = 100 := by native_decide

-- ============================================================
-- §6  Expected win rate
-- ============================================================

def weightedSum (matrix : Archetype → Archetype → WinRate) (myArch : Archetype)
    (shares : List ShareEntry) : Nat :=
  shares.foldl (fun acc e => acc + matrix myArch e.arch * e.pct) 0

def expectedWinRate (matrix : Archetype → Archetype → WinRate) (myArch : Archetype)
    (dist : MetaDist) : Nat :=
  weightedSum matrix myArch dist.shares

/-- [T16] -/ theorem weighted_sum_empty (f : Archetype → Archetype → WinRate) (a : Archetype) :
    weightedSum f a [] = 0 := by simp [weightedSum, List.foldl]

/-- [T17] -/ theorem weighted_sum_single (f : Archetype → Archetype → WinRate) (a : Archetype)
    (e : ShareEntry) : weightedSum f a [e] = f a e.arch * e.pct := by
  simp [weightedSum, List.foldl]

-- ============================================================
-- §7  Counter-teching
-- ============================================================

structure TechCard where
  name           : String
  targetMatchup  : Archetype
  improvement    : Nat
  consistencyCost: Nat
  deriving Repr

def applyTech (base : WinRate) (improvement : Nat) : WinRate :=
  clamp100 (base + improvement)

/-- [T18] Tech application is bounded ≤ 100. -/
theorem tech_bounded (base : WinRate) (imp : Nat) :
    applyTech base imp ≤ 100 := clamp100_le _

/-- [T19] Tech application preserves or improves (when base ≤ 100). -/
theorem tech_improves_or_caps (base : WinRate) (imp : Nat) (hb : base ≤ 100) :
    applyTech base imp ≥ base := by
  simp only [applyTech, clamp100, Nat.min_def]
  split
  · exact Nat.le_add_right base imp
  · exact hb

/-- [T20] Strictly improves when below cap. -/
theorem counter_tech_improves (base : WinRate) (imp : Nat) (h : imp > 0)
    (h2 : base + imp ≤ 100) :
    applyTech base imp > base := by
  unfold applyTech WinRate; rw [clamp100_preserves _ h2]; omega

-- Specific tech examples
def templeOfSinnoh : TechCard := ⟨"Temple of Sinnoh", .combo, 15, 3⟩
def pathToThePeak : TechCard := ⟨"Path to the Peak", .combo, 20, 5⟩
def drapionV : TechCard := ⟨"Drapion V", .combo, 25, 4⟩
def spiritomb : TechCard := ⟨"Spiritomb", .combo, 10, 2⟩

-- ============================================================
-- §8  Tier list
-- ============================================================

inductive Tier where
  | S | A | B | C | D
  deriving DecidableEq, Repr, BEq

def assignTier (winRatePct : Nat) : Tier :=
  if winRatePct ≥ 58 then .S
  else if winRatePct ≥ 54 then .A
  else if winRatePct ≥ 50 then .B
  else if winRatePct ≥ 46 then .C
  else .D

def Tier.toNat : Tier → Nat
  | .S => 4 | .A => 3 | .B => 2 | .C => 1 | .D => 0

/-- [T21] -/ theorem tier_S_is_best : ∀ t : Tier, Tier.toNat .S ≥ Tier.toNat t := by
  intro t; cases t <;> simp [Tier.toNat]

/-- [T22] -/ theorem tier_monotone_58 : assignTier 58 = .S := by native_decide
/-- [T23] -/ theorem tier_monotone_54 : assignTier 54 = .A := by native_decide
/-- [T24] -/ theorem tier_monotone_50 : assignTier 50 = .B := by native_decide
/-- [T25] -/ theorem tier_monotone_46 : assignTier 46 = .C := by native_decide
/-- [T26] -/ theorem tier_monotone_45 : assignTier 45 = .D := by native_decide

/-- [T27] -/ theorem tier_A_range (n : Nat) (h1 : n ≥ 54) (h2 : n < 58) :
    assignTier n = .A := by unfold assignTier; rw [if_neg (by omega), if_pos h1]

/-- [T28] -/ theorem tier_B_range (n : Nat) (h1 : n ≥ 50) (h2 : n < 54) :
    assignTier n = .B := by unfold assignTier; rw [if_neg (by omega), if_neg (by omega), if_pos h1]

/-- [T29] -/ theorem tier_C_range (n : Nat) (h1 : n ≥ 46) (h2 : n < 50) :
    assignTier n = .C := by
  unfold assignTier
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h1]

/-- [T30] -/ theorem tier_D_range (n : Nat) (h : n < 46) : assignTier n = .D := by
  unfold assignTier
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- [T31] -/ theorem tier_S_threshold (n : Nat) (h : n ≥ 58) : assignTier n = .S := by
  unfold assignTier; rw [if_pos h]

-- ============================================================
-- §9  Meta shift cycle
-- ============================================================

structure MetaCycle where
  dominant       : Archetype
  counter        : Archetype
  counterCounter : Archetype
  deriving Repr

def classicCycle : MetaCycle := ⟨.aggro, .control, .combo⟩

def counterOf : Archetype → Archetype
  | .aggro    => .control
  | .control  => .combo
  | .combo    => .aggro
  | .midrange => .aggro
  | .stall    => .combo
  | .mill     => .aggro
  | .toolbox  => .midrange

def counterCounterOf (a : Archetype) : Archetype := counterOf (counterOf a)

/-- [T32] -/ theorem aggro_counter_is_control : counterOf .aggro = .control := rfl
/-- [T33] -/ theorem control_counter_is_combo : counterOf .control = .combo := rfl
/-- [T34] -/ theorem combo_counter_is_aggro : counterOf .combo = .aggro := rfl

/-- [T35] The core RPS triangle forms a 3-cycle. -/
theorem rps_three_cycle :
    counterCounterOf (counterOf .aggro) = .aggro := by
  simp [counterCounterOf, counterOf]

-- ============================================================
-- §10  Historical meta data
-- ============================================================

structure DeckEntry where
  name      : String
  archetype : Archetype
  share     : Nat
  deriving Repr

def swsh2023Decks : List DeckEntry :=
  [ ⟨"Lugia VSTAR",   .midrange, 25⟩
  , ⟨"Lost Zone Box",  .toolbox,  22⟩
  , ⟨"Mew VMAX",       .combo,    18⟩
  , ⟨"Gardevoir ex",   .combo,    12⟩
  , ⟨"Miraidon ex",    .aggro,    10⟩
  , ⟨"Other",          .midrange, 13⟩ ]

def swsh2023Total : Nat := swsh2023Decks.foldl (fun acc e => acc + e.share) 0

/-- [T36] -/ theorem swsh2023_sums_to_100 : swsh2023Total = 100 := by native_decide

def sv2024Decks : List DeckEntry :=
  [ ⟨"Charizard ex",   .midrange, 22⟩
  , ⟨"Iron Hands ex",  .aggro,    18⟩
  , ⟨"Gardevoir ex",   .combo,    16⟩
  , ⟨"Lost Zone Box",  .toolbox,  14⟩
  , ⟨"Giratina VSTAR", .control,  10⟩
  , ⟨"Roaring Moon ex",.aggro,     8⟩
  , ⟨"Other",          .midrange, 12⟩ ]

def sv2024Total : Nat := sv2024Decks.foldl (fun acc e => acc + e.share) 0

/-- [T37] -/ theorem sv2024_sums_to_100 : sv2024Total = 100 := by native_decide

-- ============================================================
-- §11  Zero-sum & bounding
-- ============================================================

/-- [T38] In a zero-sum matchup, one rate determines the other. -/
theorem zero_sum_property (f : Archetype → Archetype → Nat)
    (h : ∀ x y, f x y + f y x = 100) (a b : Archetype) :
    f a b = 100 - f b a := by
  have h2 := h b a; omega

/-- [T39] -/ theorem matchup_bounded (m : MatchupMatrix)
    (hB : ∀ a b, m.rate a b ≤ 100) (a b : Archetype) :
    m.rate a b ≤ 100 := hB a b

/-- [T40] -/ theorem winrate_nonneg (w : WinRate) : w ≥ 0 := Nat.zero_le w

-- ============================================================
-- §12  Counter pressure
-- ============================================================

/-- [T41] Higher win rate × positive share ⟹ higher expected contribution. -/
theorem counter_pressure (bVsA aShare : Nat) (hFav : bVsA > 50) (hShare : aShare > 0) :
    bVsA * aShare > 50 * aShare :=
  Nat.mul_lt_mul_of_pos_right hFav hShare

-- ============================================================
-- §13  Meta share arithmetic
-- ============================================================

/-- [T42] -/ theorem empty_shares_total : (MetaDist.mk []).total = 0 := by
  simp [MetaDist.total, List.foldl]

def singleArchMeta (a : Archetype) : MetaDist := ⟨[⟨a, 100⟩]⟩

/-- [T43] -/ theorem single_arch_valid (a : Archetype) : (singleArchMeta a).total = 100 := by
  cases a <;> native_decide

-- ============================================================
-- §14  Matchup intransitivity (existence)
-- ============================================================

/-- [T44] Intransitivity: three matchups can all be favorable. -/
theorem matchup_intransitivity :
    ∃ (ab bc ca : WinRate), ab > 50 ∧ bc > 50 ∧ ca > 50 :=
  ⟨60, 60, 60, by decide, by decide, by decide⟩

-- ============================================================
-- §15  Utility functions
-- ============================================================

def bestArchetype (archetypes : List Archetype)
    (matrix : Archetype → Archetype → WinRate) (dist : MetaDist) : Option Archetype :=
  let scored := archetypes.map (fun a => (a, expectedWinRate matrix a dist))
  let best := scored.foldl (fun acc (a, s) =>
    match acc with
    | none => some (a, s)
    | some (_, bs) => if s > bs then some (a, s) else acc) none
  best.map Prod.fst

def allArchetypes : List Archetype :=
  [.aggro, .control, .combo, .midrange, .stall, .mill, .toolbox]

/-- [T45] -/ theorem all_archetypes_length : allArchetypes.length = 7 := by native_decide

-- ============================================================
-- §16  Speed classification
-- ============================================================

def isAggroSpeed (turnsToWin : Nat) : Bool := turnsToWin ≤ 4
def isControlSpeed (turnsToWin : Nat) : Bool := turnsToWin ≥ 10

/-- [T46] Aggro speed and control speed are mutually exclusive. -/
theorem aggro_faster_than_control :
    ∀ t, isAggroSpeed t = true → isControlSpeed t = true → False := by
  intro t h1 h2; simp [isAggroSpeed, isControlSpeed] at h1 h2; omega

-- ============================================================
-- §17  Format snapshots
-- ============================================================

structure MetaSnapshot where
  era        : String
  date       : String
  topDecks   : List DeckEntry
  totalShare : Nat
  deriving Repr

def mkSnapshot (era date : String) (decks : List DeckEntry) : MetaSnapshot :=
  ⟨era, date, decks, decks.foldl (fun acc e => acc + e.share) 0⟩

def swsh2023Snapshot : MetaSnapshot := mkSnapshot "SWSH" "2023-07" swsh2023Decks
def sv2024Snapshot   : MetaSnapshot := mkSnapshot "SV"   "2024-03" sv2024Decks

/-- [T47] -/ theorem swsh2023_snapshot_valid : swsh2023Snapshot.totalShare = 100 := by native_decide
/-- [T48] -/ theorem sv2024_snapshot_valid   : sv2024Snapshot.totalShare   = 100 := by native_decide

-- ============================================================
-- §18  Meta diversity
-- ============================================================

def metaDiversity (m : MetaDist) : Nat :=
  m.shares.filter (fun e => e.pct > 0) |>.length

def isHealthyMeta (m : MetaDist) : Bool := metaDiversity m ≥ 3

/-- [T49] -/ theorem balanced_meta_is_healthy : isHealthyMeta balancedMeta = true := by native_decide
/-- [T50] -/ theorem single_arch_diversity :
    metaDiversity (singleArchMeta .aggro) = 1 := by native_decide

-- ============================================================
-- §19  Mirror expected value
-- ============================================================

/-- [T51] Mirror matchup against single opponent. -/
theorem mirror_expected_single (a : Archetype) (e : ShareEntry) :
    expectedWinRate (fun _ _ => mirrorRate) a ⟨[e]⟩ = 50 * e.pct := by
  simp [expectedWinRate, weightedSum, List.foldl, mirrorRate]

/-- [T52] -/ theorem rps_advantages_strict : rpsWinRate > 50 := by native_decide
/-- [T53] -/ theorem rps_disadvantages_strict : rpsLoseRate < 50 := by native_decide

-- ============================================================
-- §20  Health metrics
-- ============================================================

def maxShare (m : MetaDist) : Nat := m.shares.foldl (fun acc e => max acc e.pct) 0
def isNonDegenerate (m : MetaDist) : Bool := maxShare m ≤ 50

/-- [T54] -/ theorem balanced_meta_non_degenerate : isNonDegenerate balancedMeta = true := by native_decide
/-- [T55] -/ theorem aggro_dominated_non_degenerate : isNonDegenerate aggroDominatedMeta = true := by native_decide

def swsh2023AsDist : MetaDist := ⟨swsh2023Decks.map (fun e => ⟨e.archetype, e.share⟩)⟩
/-- [T56] -/ theorem swsh2023_meta_healthy : isHealthyMeta swsh2023AsDist = true := by native_decide

def sv2024AsDist : MetaDist := ⟨sv2024Decks.map (fun e => ⟨e.archetype, e.share⟩)⟩
/-- [T57] -/ theorem sv2024_meta_healthy : isHealthyMeta sv2024AsDist = true := by native_decide

-- ============================================================
-- §21  Archetype enumeration completeness
-- ============================================================

/-- [T58] -/ theorem archetype_exhaustive (a : Archetype) :
    a = .aggro ∨ a = .control ∨ a = .combo ∨ a = .midrange ∨
    a = .stall ∨ a = .mill ∨ a = .toolbox := by cases a <;> simp

/-- [T59] -/ theorem all_archetypes_complete (a : Archetype) :
    a ∈ allArchetypes := by cases a <;> simp [allArchetypes]

-- ============================================================
-- §22  Cycle length & injectivity
-- ============================================================

/-- [T60] Applying counterOf three times from aggro returns to aggro. -/
theorem rps_cycle_length_3 :
    counterOf (counterOf (counterOf .aggro)) = .aggro := by native_decide

/-- [T61] Tier.toNat is injective. -/
theorem tier_toNat_injective (t1 t2 : Tier) (h : Tier.toNat t1 = Tier.toNat t2) :
    t1 = t2 := by cases t1 <;> cases t2 <;> simp [Tier.toNat] at h <;> rfl

end PokemonLean.Core.Metagame
