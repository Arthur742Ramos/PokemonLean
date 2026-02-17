/-
  VSTAR Power Mechanics

  Formalizes the Pokémon TCG VSTAR mechanics:
  - VSTAR Power (once per game)
  - VSTAR markers
  - Giratina VSTAR (Star Requiem + Lost Zone condition)
  - Arceus VSTAR (Starbirth search)
  - Prize penalties for VSTAR knockouts (2 prizes)

-/

namespace VSTARMechanics

-- ============================================================================
-- Core game state
-- ============================================================================

-- ============================================================================
-- VSTAR types
-- ============================================================================

/-- Whether a player has used their VSTAR Power this game. -/
inductive VSTARMarker : Type where
  | unused : VSTARMarker
  | used   : VSTARMarker
deriving Repr, DecidableEq, BEq

/-- Energy types. -/
inductive EnergyType : Type where
  | grass | fire | water | lightning | psychic | fighting
  | darkness | metal | dragon | colorless
deriving Repr, DecidableEq, BEq

/-- Card categories. -/
inductive CardCategory : Type where
  | pokemon | trainer | energy
deriving Repr, DecidableEq, BEq

/-- Pokémon card subtypes relevant to VSTAR. -/
inductive PokemonSubtype : Type where
  | basic | stage1 | stage2 | v | vmax | vstar | ex | gx
deriving Repr, DecidableEq, BEq

/-- A simplified card representation. -/
structure Card where
  name : String
  category : CardCategory
  subtype : Option PokemonSubtype
  hp : Nat
deriving Repr, BEq

/-- Prize count for knocking out a Pokémon. -/
def prizePenalty : PokemonSubtype → Nat
  | PokemonSubtype.basic  => 1
  | PokemonSubtype.stage1 => 1
  | PokemonSubtype.stage2 => 1
  | PokemonSubtype.v      => 2
  | PokemonSubtype.vmax   => 3
  | PokemonSubtype.vstar  => 2
  | PokemonSubtype.ex     => 2
  | PokemonSubtype.gx     => 2

/-- Lost Zone: cards banished from the game. -/
structure LostZone where
  cards : List Card
deriving Repr, BEq

/-- A player's VSTAR state. -/
structure VSTARState where
  marker : VSTARMarker
  lostZone : LostZone
  prizesRemaining : Nat
deriving Repr, BEq

/-- Initial VSTAR state. -/
def VSTARState.initial : VSTARState :=
  { marker := VSTARMarker.unused, lostZone := { cards := [] }, prizesRemaining := 6 }

-- ============================================================================
-- VSTAR Power usage
-- ============================================================================

/-- Can use VSTAR Power only if marker is unused. -/
def canUseVSTARPower (s : VSTARState) : Bool :=
  s.marker == VSTARMarker.unused

/-- Use VSTAR Power: flip the marker. -/
def useVSTARPower (s : VSTARState) : VSTARState :=
  { s with marker := VSTARMarker.used }

/-- After using VSTAR Power, it cannot be used again. -/
-- 1
theorem vstar_power_once (s : VSTARState) (h : canUseVSTARPower s = true) :
    canUseVSTARPower (useVSTARPower s) = false := by
  simp [canUseVSTARPower, useVSTARPower]
  decide

-- 2
theorem vstar_power_initial :
    canUseVSTARPower VSTARState.initial = true := by
  simp [canUseVSTARPower, VSTARState.initial]
  decide

-- 3
theorem vstar_power_used_is_used (s : VSTARState) :
    (useVSTARPower s).marker = VSTARMarker.used := by
  simp [useVSTARPower]

-- 4
theorem vstar_power_idempotent (s : VSTARState) :
    useVSTARPower (useVSTARPower s) = useVSTARPower s := by
  simp [useVSTARPower]

-- ============================================================================
-- Giratina VSTAR: Star Requiem
-- ============================================================================

/-- Count cards in the Lost Zone. -/
def lostZoneCount (s : VSTARState) : Nat :=
  s.lostZone.cards.length

/-- Star Requiem condition: at least 10 cards in Lost Zone. -/
def starRequiemCondition (s : VSTARState) : Bool :=
  lostZoneCount s ≥ 10 && canUseVSTARPower s

/-- Add a card to the Lost Zone. -/
def addToLostZone (c : Card) (s : VSTARState) : VSTARState :=
  { s with lostZone := { cards := c :: s.lostZone.cards } }

-- 5
theorem addToLostZone_increases_count (c : Card) (s : VSTARState) :
    lostZoneCount (addToLostZone c s) = lostZoneCount s + 1 := by
  simp [lostZoneCount, addToLostZone, List.length_cons]

-- 6
theorem addToLostZone_preserves_marker (c : Card) (s : VSTARState) :
    (addToLostZone c s).marker = s.marker := by
  simp [addToLostZone]

-- 7
theorem addToLostZone_preserves_prizes (c : Card) (s : VSTARState) :
    (addToLostZone c s).prizesRemaining = s.prizesRemaining := by
  simp [addToLostZone]

-- 8
theorem star_requiem_needs_ten (s : VSTARState) (h : lostZoneCount s < 10) :
    starRequiemCondition s = false := by
  simp [starRequiemCondition]
  omega

-- ============================================================================
-- Arceus VSTAR: Starbirth
-- ============================================================================

/-- Starbirth: search deck for up to 2 cards (uses VSTAR Power). -/
def starbirth (s : VSTARState) : Option VSTARState :=
  if canUseVSTARPower s then some (useVSTARPower s) else none

-- 9
theorem starbirth_uses_power (s : VSTARState) (h : canUseVSTARPower s = true) :
    starbirth s = some (useVSTARPower s) := by
  simp [starbirth, h]

-- 10
theorem starbirth_fails_if_used (s : VSTARState) (h : canUseVSTARPower s = false) :
    starbirth s = none := by
  simp [starbirth, h]

-- ============================================================================
-- Prize penalty theorems
-- ============================================================================

-- 11
theorem vstar_gives_two_prizes :
    prizePenalty PokemonSubtype.vstar = 2 := rfl

-- 12
theorem v_gives_two_prizes :
    prizePenalty PokemonSubtype.v = 2 := rfl

-- 13
theorem vmax_gives_three_prizes :
    prizePenalty PokemonSubtype.vmax = 3 := rfl

-- 14
theorem basic_gives_one_prize :
    prizePenalty PokemonSubtype.basic = 1 := rfl

/-- Take prizes after a knockout. -/
def takePrizes (sub : PokemonSubtype) (s : VSTARState) : VSTARState :=
  { s with prizesRemaining := s.prizesRemaining - prizePenalty sub }

-- 15
theorem takePrizes_vstar_takes_two (s : VSTARState) :
    (takePrizes PokemonSubtype.vstar s).prizesRemaining =
    s.prizesRemaining - 2 := by
  simp [takePrizes, prizePenalty]

-- 16
-- 17
-- 18
-- 19
-- 20

-- 21
-- 22
-- ============================================================================
-- Lost Zone path coherence
-- ============================================================================

-- 23
theorem lostZone_empty_initial :
    lostZoneCount VSTARState.initial = 0 := rfl

-- 24
theorem addToLostZone_comm_marker (c₁ c₂ : Card) (s : VSTARState) :
    (addToLostZone c₂ (addToLostZone c₁ s)).marker =
    (addToLostZone c₁ (addToLostZone c₂ s)).marker := by
  simp [addToLostZone]

-- 25
theorem addToLostZone_count_two (c₁ c₂ : Card) (s : VSTARState) :
    lostZoneCount (addToLostZone c₂ (addToLostZone c₁ s)) =
    lostZoneCount s + 2 := by
  simp [lostZoneCount, addToLostZone, List.length_cons]

-- ============================================================================
-- VSTAR marker is a two-state system
-- ============================================================================

-- 26
theorem marker_cases (m : VSTARMarker) : m = VSTARMarker.unused ∨ m = VSTARMarker.used := by
  cases m <;> simp

-- 27
theorem unused_ne_used : VSTARMarker.unused ≠ VSTARMarker.used := by
  intro h; cases h

-- 28
theorem useVSTARPower_preserves_lostZone (s : VSTARState) :
    (useVSTARPower s).lostZone = s.lostZone := by
  simp [useVSTARPower]

-- 29
theorem useVSTARPower_preserves_prizes (s : VSTARState) :
    (useVSTARPower s).prizesRemaining = s.prizesRemaining := by
  simp [useVSTARPower]

-- 30
theorem takePrizes_preserves_marker (sub : PokemonSubtype) (s : VSTARState) :
    (takePrizes sub s).marker = s.marker := by
  simp [takePrizes]

end VSTARMechanics
