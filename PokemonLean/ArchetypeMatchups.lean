/-
  PokemonLean/ArchetypeMatchups.lean — Matchup theory and tier list formalization
  Rock-paper-scissors dynamics, matchup spreads, tier classification
-/
import PokemonLean.Archetypes

namespace PokemonLean.ArchetypeMatchups

open PokemonLean.Archetypes

-- ============================================================================
-- MATCHUP THEORY
-- ============================================================================

/-- Matchup result: favorable, even, or unfavorable -/
inductive MatchupResult where
  | favorable    -- >55% win rate
  | even         -- 45-55% win rate
  | unfavorable  -- <45% win rate
  deriving Repr, BEq, DecidableEq

/-- Win rate as a percentage (0-100) -/
abbrev WinRate := Nat

/-- Classify a win rate into a matchup result -/
def classifyMatchup (wr : WinRate) : MatchupResult :=
  if wr > 55 then .favorable
  else if wr ≥ 45 then .even
  else .unfavorable

theorem high_wr_favorable : classifyMatchup 70 = .favorable := by decide
theorem fifty_is_even : classifyMatchup 50 = .even := by decide
theorem low_wr_unfavorable : classifyMatchup 30 = .unfavorable := by decide
theorem boundary_55_even : classifyMatchup 55 = .even := by decide
theorem boundary_56_favorable : classifyMatchup 56 = .favorable := by decide
theorem boundary_45_even : classifyMatchup 45 = .even := by decide
theorem boundary_44_unfavorable : classifyMatchup 44 = .unfavorable := by decide

-- ============================================================================
-- CLASSIC MATCHUP TRIANGLE
-- ============================================================================

/-- The classic archetype matchup wheel:
    Aggro beats Combo (too fast)
    Combo beats Control (overwhelms disruption)
    Control beats Aggro (outlasts)
    Midrange is roughly even vs all -/
def archetypeMatchup (attacker defender : Archetype) : WinRate :=
  match attacker, defender with
  | .aggro, .combo     => 65
  | .aggro, .control   => 40
  | .aggro, .midrange  => 50
  | .aggro, .aggro     => 50
  | .control, .aggro   => 60
  | .control, .combo   => 40
  | .control, .midrange => 45
  | .control, .control => 50
  | .combo, .control   => 60
  | .combo, .aggro     => 35
  | .combo, .midrange  => 55
  | .combo, .combo     => 50
  | .midrange, .aggro  => 50
  | .midrange, .control => 55
  | .midrange, .combo  => 45
  | .midrange, .midrange => 50

-- Core triangle theorems
theorem aggro_beats_combo : archetypeMatchup .aggro .combo > 50 := by decide
theorem combo_beats_control : archetypeMatchup .combo .control > 50 := by decide
theorem control_beats_aggro : archetypeMatchup .control .aggro > 50 := by decide

theorem aggro_loses_to_control : archetypeMatchup .aggro .control < 50 := by decide
theorem combo_loses_to_aggro : archetypeMatchup .combo .aggro < 50 := by decide
theorem control_loses_to_combo : archetypeMatchup .control .combo < 50 := by decide

-- Mirror matches are 50-50
theorem aggro_mirror : archetypeMatchup .aggro .aggro = 50 := by decide
theorem control_mirror : archetypeMatchup .control .control = 50 := by decide
theorem combo_mirror : archetypeMatchup .combo .combo = 50 := by decide
theorem midrange_mirror : archetypeMatchup .midrange .midrange = 50 := by decide

-- Midrange has no terrible matchups
theorem midrange_no_terrible_matchup_aggro :
    archetypeMatchup .midrange .aggro ≥ 45 := by decide
theorem midrange_no_terrible_matchup_control :
    archetypeMatchup .midrange .control ≥ 45 := by decide
theorem midrange_no_terrible_matchup_combo :
    archetypeMatchup .midrange .combo ≥ 45 := by decide

-- ============================================================================
-- MATCHUP SPREAD
-- ============================================================================

/-- A matchup spread is a deck's win rates against the field -/
structure MatchupSpread where
  vsAggro : WinRate
  vsControl : WinRate
  vsCombo : WinRate
  vsMidrange : WinRate
  deriving Repr, BEq

/-- Get the spread for an archetype -/
def getSpread (a : Archetype) : MatchupSpread :=
  { vsAggro := archetypeMatchup a .aggro
  , vsControl := archetypeMatchup a .control
  , vsCombo := archetypeMatchup a .combo
  , vsMidrange := archetypeMatchup a .midrange }

/-- Weighted win rate given metagame shares (as percentages summing to 100) -/
def weightedWinRate (spread : MatchupSpread) (aggroShare controlShare comboShare midrangeShare : Nat) : Nat :=
  (spread.vsAggro * aggroShare + spread.vsControl * controlShare +
   spread.vsCombo * comboShare + spread.vsMidrange * midrangeShare) / 100

/-- Count favorable matchups in a spread -/
def favorableCount (s : MatchupSpread) : Nat :=
  (if s.vsAggro > 55 then 1 else 0) +
  (if s.vsControl > 55 then 1 else 0) +
  (if s.vsCombo > 55 then 1 else 0) +
  (if s.vsMidrange > 55 then 1 else 0)

/-- Count unfavorable matchups -/
def unfavorableCount (s : MatchupSpread) : Nat :=
  (if s.vsAggro < 45 then 1 else 0) +
  (if s.vsControl < 45 then 1 else 0) +
  (if s.vsCombo < 45 then 1 else 0) +
  (if s.vsMidrange < 45 then 1 else 0)

theorem aggro_has_one_favorable : favorableCount (getSpread .aggro) = 1 := by decide
theorem aggro_has_one_unfavorable : unfavorableCount (getSpread .aggro) = 1 := by decide
theorem control_has_one_favorable : favorableCount (getSpread .control) = 1 := by decide
theorem combo_has_one_favorable : favorableCount (getSpread .combo) = 1 := by decide

-- ============================================================================
-- TIER LIST
-- ============================================================================

/-- Tier classification -/
inductive Tier where
  | S  -- dominant, best deck
  | A  -- strong, competitive
  | B  -- viable, some weaknesses
  | C  -- playable but outclassed
  | D  -- not recommended
  deriving Repr, BEq, DecidableEq

/-- Tier ranking as a number (higher = better) -/
def tierRank (t : Tier) : Nat :=
  match t with
  | .S => 5
  | .A => 4
  | .B => 3
  | .C => 2
  | .D => 1

/-- Classify a deck into a tier based on weighted win rate -/
def classifyTier (weightedWR : Nat) : Tier :=
  if weightedWR ≥ 58 then .S
  else if weightedWR ≥ 53 then .A
  else if weightedWR ≥ 48 then .B
  else if weightedWR ≥ 43 then .C
  else .D

theorem high_wr_is_S : classifyTier 60 = .S := by decide
theorem mid_wr_is_B : classifyTier 50 = .B := by decide
theorem low_wr_is_D : classifyTier 40 = .D := by decide
theorem threshold_S : classifyTier 58 = .S := by decide
theorem threshold_A : classifyTier 53 = .A := by decide
theorem threshold_B : classifyTier 48 = .B := by decide
theorem threshold_C : classifyTier 43 = .C := by decide

/-- Higher tier always has higher rank -/
theorem S_above_A : tierRank .S > tierRank .A := by decide
theorem A_above_B : tierRank .A > tierRank .B := by decide
theorem B_above_C : tierRank .B > tierRank .C := by decide
theorem C_above_D : tierRank .C > tierRank .D := by decide

/-- Is a deck tier-viable (B or above)? -/
def isTierViable (t : Tier) : Bool :=
  tierRank t ≥ 3

theorem S_viable : isTierViable .S = true := by decide
theorem A_viable : isTierViable .A = true := by decide
theorem B_viable : isTierViable .B = true := by decide
theorem C_not_viable : isTierViable .C = false := by decide
theorem D_not_viable : isTierViable .D = false := by decide

-- ============================================================================
-- METAGAME ANALYSIS
-- ============================================================================

/-- Metagame state: shares of each archetype (should sum to 100) -/
structure Metagame where
  aggroShare : Nat
  controlShare : Nat
  comboShare : Nat
  midrangeShare : Nat
  deriving Repr, BEq

/-- Check if metagame shares sum to 100 -/
def isValidMeta (m : Metagame) : Bool :=
  m.aggroShare + m.controlShare + m.comboShare + m.midrangeShare == 100

theorem balanced_meta_valid :
    isValidMeta ⟨25, 25, 25, 25⟩ = true := by decide

theorem aggro_heavy_meta_valid :
    isValidMeta ⟨40, 20, 20, 20⟩ = true := by decide

/-- Best archetype choice for an aggro-heavy meta -/
def bestAgainstAggro : Archetype := .control

/-- Best archetype choice for a control-heavy meta -/
def bestAgainstControl : Archetype := .combo

/-- Best archetype choice for a combo-heavy meta -/
def bestAgainstCombo : Archetype := .aggro

theorem counter_aggro_correct :
    archetypeMatchup bestAgainstAggro .aggro > 55 := by decide

theorem counter_control_correct :
    archetypeMatchup bestAgainstControl .control > 55 := by decide

theorem counter_combo_correct :
    archetypeMatchup bestAgainstCombo .combo > 55 := by decide

-- ============================================================================
-- DECK POWER LEVEL
-- ============================================================================

/-- Combined power score for a deck -/
def deckPowerScore (speed consistency favorables : Nat) : Nat :=
  speed * 3 + consistency * 3 + favorables * 10

/-- Compare two decks -/
def isDeckStronger (s1 c1 f1 s2 c2 f2 : Nat) : Bool :=
  deckPowerScore s1 c1 f1 > deckPowerScore s2 c2 f2

theorem power_score_favors_matchups :
    deckPowerScore 5 5 3 > deckPowerScore 8 8 0 := by decide

end PokemonLean.ArchetypeMatchups
