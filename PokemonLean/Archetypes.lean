/-
  PokemonLean/Archetypes.lean — Deck archetype classification and theory
  Aggro / Control / Combo / Midrange formalization
  Speed vs consistency tradeoffs, 60-card rules, 4-copy limit
-/
import PokemonLean.Basic
import PokemonLean.Core.Types

namespace PokemonLean.Archetypes

-- ============================================================================
-- ARCHETYPE CLASSIFICATION
-- ============================================================================

/-- The four fundamental deck archetypes -/
inductive Archetype where
  | aggro    -- fast damage, win quickly
  | control  -- deny resources, win slowly
  | combo    -- assemble pieces for big turn
  | midrange -- balanced approach
  deriving Repr, BEq, DecidableEq

/-- Speed rating 1-10 (how fast the deck tries to win) -/
abbrev Speed := Nat

/-- Consistency rating 1-10 (how reliably the deck executes its plan) -/
abbrev Consistency := Nat

/-- An archetype profile -/
structure ArchetypeProfile where
  archetype : Archetype
  speed : Speed
  consistency : Consistency
  avgTurnsToWin : Nat  -- average turns to take 6 prizes
  deriving Repr, BEq

/-- Typical speed for each archetype -/
def typicalSpeed (a : Archetype) : Nat :=
  match a with
  | .aggro    => 9
  | .control  => 3
  | .combo    => 7
  | .midrange => 5

/-- Typical consistency for each archetype -/
def typicalConsistency (a : Archetype) : Nat :=
  match a with
  | .aggro    => 5
  | .control  => 7
  | .combo    => 4
  | .midrange => 8

/-- Average turns to win for each archetype -/
def typicalTurnsToWin (a : Archetype) : Nat :=
  match a with
  | .aggro    => 4
  | .control  => 12
  | .combo    => 6
  | .midrange => 8

-- ============================================================================
-- ARCHETYPE THEOREMS
-- ============================================================================


-- ============================================================================
-- SPEED-CONSISTENCY TRADEOFF
-- ============================================================================

/-- Speed + consistency budget: archetypes must make tradeoffs -/
def speedConsistencySum (a : Archetype) : Nat :=
  typicalSpeed a + typicalConsistency a


/-- A deck is speed-oriented if speed > consistency -/
def isSpeedOriented (a : Archetype) : Bool :=
  typicalSpeed a > typicalConsistency a

/-- A deck is consistency-oriented if consistency > speed -/
def isConsistencyOriented (a : Archetype) : Bool :=
  typicalConsistency a > typicalSpeed a


-- ============================================================================
-- 60-CARD DECK BUILDING RULES
-- ============================================================================

/-- Standard deck size -/
def deckSize : Nat := 60

/-- Maximum copies of any single card (except basic energy) -/
def maxCopies : Nat := 4

/-- Card role in a deck -/
inductive CardRole where
  | attacker      -- deals damage
  | support       -- supports strategy (draw, search)
  | energy        -- provides energy
  | techCard      -- situational counter
  | setupPiece    -- early game setup
  | winCondition  -- primary win path
  deriving Repr, BEq, DecidableEq

/-- Deck composition: counts of each category -/
structure DeckComposition where
  pokemonCards : Nat
  trainerCards : Nat
  energyCards : Nat
  deriving Repr, BEq

/-- A deck composition is legal if it sums to 60 -/
def isLegalSize (d : DeckComposition) : Bool :=
  d.pokemonCards + d.trainerCards + d.energyCards == deckSize

/-- Must have at least 1 basic Pokemon -/
def hasBasicPokemon (basicCount : Nat) : Bool :=
  basicCount ≥ 1

/-- Check 4-copy limit for a card count -/
def withinCopyLimit (copies : Nat) (isBasicEnergy : Bool) : Bool :=
  if isBasicEnergy then true else copies ≤ maxCopies


theorem legal_deck_sums_to_60 (p t e : Nat) (h : p + t + e = 60) :
    isLegalSize ⟨p, t, e⟩ = true := by
  simp [isLegalSize, deckSize, h]


theorem basic_energy_unlimited (n : Nat) : withinCopyLimit n true = true := by
  simp [withinCopyLimit]


-- ============================================================================
-- ARCHETYPE-SPECIFIC DECK COMPOSITIONS
-- ============================================================================

/-- Typical aggro composition -/
def aggroComposition : DeckComposition := ⟨16, 32, 12⟩

/-- Typical control composition -/
def controlComposition : DeckComposition := ⟨8, 40, 12⟩

/-- Typical combo composition -/
def comboComposition : DeckComposition := ⟨14, 36, 10⟩

/-- Typical midrange composition -/
def midrangeComposition : DeckComposition := ⟨12, 34, 14⟩


-- ============================================================================
-- DRAW ENGINE AND CONSISTENCY
-- ============================================================================

/-- Number of draw/search supporters in a deck -/
def drawEngineSize (supporters searchCards : Nat) : Nat :=
  supporters + searchCards

/-- Minimum recommended draw engine -/
def minDrawEngine : Nat := 12

/-- Check if draw engine is sufficient -/
def hasAdequateDrawEngine (supporters searchCards : Nat) : Bool :=
  drawEngineSize supporters searchCards ≥ minDrawEngine


/-- Probability proxy: more draw = more consistent (simplified) -/
def consistencyScore (drawCards totalCards : Nat) : Nat :=
  if totalCards == 0 then 0 else (drawCards * 100) / totalCards


-- ============================================================================
-- ENERGY CURVE
-- ============================================================================

/-- Attack cost categories -/
def isLowCost (energyCost : Nat) : Bool := energyCost ≤ 2
def isMidCost (energyCost : Nat) : Bool := energyCost == 3 || energyCost == 4
def isHighCost (energyCost : Nat) : Bool := energyCost ≥ 5


/-- Aggro decks should prefer low-cost attacks -/
def aggroPreference (cost : Nat) : Nat :=
  if cost ≤ 1 then 10
  else if cost ≤ 2 then 7
  else if cost ≤ 3 then 3
  else 1


end PokemonLean.Archetypes
