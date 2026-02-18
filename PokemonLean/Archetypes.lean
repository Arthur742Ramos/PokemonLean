/-
  PokemonLean/Archetypes.lean — Deck archetype classification and theory
  Aggro / Control / Combo / Midrange formalization
  Speed vs consistency tradeoffs, 60-card rules, 4-copy limit
-/
import PokemonLean.Basic

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

theorem aggro_fastest : typicalSpeed .aggro ≥ typicalSpeed .midrange := by decide
theorem aggro_faster_than_control : typicalSpeed .aggro > typicalSpeed .control := by decide
theorem aggro_faster_than_combo : typicalSpeed .aggro > typicalSpeed .combo := by decide
theorem control_slowest : typicalSpeed .control ≤ typicalSpeed .midrange := by decide

theorem midrange_most_consistent :
    typicalConsistency .midrange ≥ typicalConsistency .aggro ∧
    typicalConsistency .midrange ≥ typicalConsistency .combo := by decide

theorem control_more_consistent_than_aggro :
    typicalConsistency .control > typicalConsistency .aggro := by decide

theorem combo_least_consistent :
    typicalConsistency .combo ≤ typicalConsistency .aggro ∧
    typicalConsistency .combo ≤ typicalConsistency .control ∧
    typicalConsistency .combo ≤ typicalConsistency .midrange := by decide

theorem aggro_wins_fastest : typicalTurnsToWin .aggro ≤ typicalTurnsToWin .combo := by decide
theorem control_wins_slowest :
    typicalTurnsToWin .control ≥ typicalTurnsToWin .aggro ∧
    typicalTurnsToWin .control ≥ typicalTurnsToWin .combo ∧
    typicalTurnsToWin .control ≥ typicalTurnsToWin .midrange := by decide

-- ============================================================================
-- SPEED-CONSISTENCY TRADEOFF
-- ============================================================================

/-- Speed + consistency budget: archetypes must make tradeoffs -/
def speedConsistencySum (a : Archetype) : Nat :=
  typicalSpeed a + typicalConsistency a

theorem aggro_tradeoff : speedConsistencySum .aggro = 14 := by decide
theorem control_tradeoff : speedConsistencySum .control = 10 := by decide
theorem combo_tradeoff : speedConsistencySum .combo = 11 := by decide
theorem midrange_tradeoff : speedConsistencySum .midrange = 13 := by decide

/-- A deck is speed-oriented if speed > consistency -/
def isSpeedOriented (a : Archetype) : Bool :=
  typicalSpeed a > typicalConsistency a

/-- A deck is consistency-oriented if consistency > speed -/
def isConsistencyOriented (a : Archetype) : Bool :=
  typicalConsistency a > typicalSpeed a

theorem aggro_is_speed_oriented : isSpeedOriented .aggro = true := by decide
theorem combo_is_speed_oriented : isSpeedOriented .combo = true := by decide
theorem control_is_consistency_oriented : isConsistencyOriented .control = true := by decide
theorem midrange_is_consistency_oriented : isConsistencyOriented .midrange = true := by decide

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

theorem deck_size_is_60 : deckSize = 60 := by rfl
theorem max_copies_is_4 : maxCopies = 4 := by rfl

theorem legal_deck_sums_to_60 (p t e : Nat) (h : p + t + e = 60) :
    isLegalSize ⟨p, t, e⟩ = true := by
  simp [isLegalSize, deckSize, h]

theorem zero_copies_within_limit : withinCopyLimit 0 false = true := by decide
theorem one_copy_within_limit : withinCopyLimit 1 false = true := by decide
theorem four_copies_within_limit : withinCopyLimit 4 false = true := by decide
theorem five_copies_over_limit : withinCopyLimit 5 false = false := by decide

theorem basic_energy_unlimited (n : Nat) : withinCopyLimit n true = true := by
  simp [withinCopyLimit]

theorem must_have_basic : hasBasicPokemon 0 = false := by decide
theorem one_basic_legal : hasBasicPokemon 1 = true := by decide

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

theorem aggro_deck_legal : isLegalSize aggroComposition = true := by decide
theorem control_deck_legal : isLegalSize controlComposition = true := by decide
theorem combo_deck_legal : isLegalSize comboComposition = true := by decide
theorem midrange_deck_legal : isLegalSize midrangeComposition = true := by decide

theorem aggro_most_pokemon :
    aggroComposition.pokemonCards ≥ controlComposition.pokemonCards := by decide

theorem control_most_trainers :
    controlComposition.trainerCards ≥ aggroComposition.trainerCards := by decide

theorem midrange_most_energy :
    midrangeComposition.energyCards ≥ comboComposition.energyCards := by decide

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

theorem adequate_draw_12 : hasAdequateDrawEngine 8 4 = true := by decide
theorem inadequate_draw_5 : hasAdequateDrawEngine 3 2 = false := by decide

/-- Probability proxy: more draw = more consistent (simplified) -/
def consistencyScore (drawCards totalCards : Nat) : Nat :=
  if totalCards == 0 then 0 else (drawCards * 100) / totalCards

theorem more_draw_more_consistent :
    consistencyScore 15 60 ≥ consistencyScore 10 60 := by decide

-- ============================================================================
-- ENERGY CURVE
-- ============================================================================

/-- Attack cost categories -/
def isLowCost (energyCost : Nat) : Bool := energyCost ≤ 2
def isMidCost (energyCost : Nat) : Bool := energyCost == 3 || energyCost == 4
def isHighCost (energyCost : Nat) : Bool := energyCost ≥ 5

theorem zero_is_low_cost : isLowCost 0 = true := by decide
theorem two_is_low_cost : isLowCost 2 = true := by decide
theorem three_not_low_cost : isLowCost 3 = false := by decide
theorem three_is_mid_cost : isMidCost 3 = true := by decide
theorem five_is_high_cost : isHighCost 5 = true := by decide

/-- Aggro decks should prefer low-cost attacks -/
def aggroPreference (cost : Nat) : Nat :=
  if cost ≤ 1 then 10
  else if cost ≤ 2 then 7
  else if cost ≤ 3 then 3
  else 1

theorem aggro_prefers_cheap : aggroPreference 1 > aggroPreference 3 := by decide
theorem aggro_hates_expensive : aggroPreference 1 > aggroPreference 5 := by decide

end PokemonLean.Archetypes
