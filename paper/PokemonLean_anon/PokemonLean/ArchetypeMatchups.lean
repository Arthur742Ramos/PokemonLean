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


-- Mirror matches are 50-50

-- Midrange has no terrible matchups

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


-- Higher tier always has higher rank

/-- Is a deck tier-viable (B or above)? -/
def isTierViable (t : Tier) : Bool :=
  tierRank t ≥ 3


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


/-- Best archetype choice for an aggro-heavy meta -/
def bestAgainstAggro : Archetype := .control

/-- Best archetype choice for a control-heavy meta -/
def bestAgainstControl : Archetype := .combo

/-- Best archetype choice for a combo-heavy meta -/
def bestAgainstCombo : Archetype := .aggro


-- ============================================================================
-- DECK POWER LEVEL
-- ============================================================================

/-- Combined power score for a deck -/
def deckPowerScore (speed consistency favorables : Nat) : Nat :=
  speed * 3 + consistency * 3 + favorables * 10

/-- Compare two decks -/
def isDeckStronger (s1 c1 f1 s2 c2 f2 : Nat) : Bool :=
  deckPowerScore s1 c1 f1 > deckPowerScore s2 c2 f2


end PokemonLean.ArchetypeMatchups
