-- Special Conditions and Advanced Battle Mechanics
-- PokemonLean: Weakness Policy, Choice items, VSTAR/GX, Prism Star, Lost Zone

import PokemonLean.Basic

namespace PokemonLean.SpecialConditions

open PokemonLean

-- ============================================================================
-- TOOL ATTACHMENT TYPES
-- ============================================================================

/-- Pokémon Tool items that can be attached (one per Pokémon). -/
inductive ToolKind
  | weaknessPolicy        -- Boosts damage after being hit for weakness
  | choiceBelt            -- +30 damage to V Pokémon
  | choiceBand            -- +30 damage to GX/EX Pokémon
  | rescueScarf           -- Recover Pokémon when knocked out
  | expShare              -- Transfer energy on KO
  | floatStone            -- Free retreat
  | noTool                -- No tool attached
  deriving Repr, BEq, DecidableEq

/-- A Pokémon with an optional tool attached. -/
structure TooledPokemon where
  pokemon : PokemonInPlay
  tool : ToolKind
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- TOOL ATTACHMENT RULES (one tool per Pokémon)
-- ============================================================================

/-- Attach a tool to a Pokémon. Fails if tool is already attached. -/
def attachTool (tp : TooledPokemon) (newTool : ToolKind) : Option TooledPokemon :=
  if tp.tool == .noTool then
    some { tp with tool := newTool }
  else
    none

/-- Remove the tool from a Pokémon. -/
def removeTool (tp : TooledPokemon) : TooledPokemon × ToolKind :=
  ({ tp with tool := .noTool }, tp.tool)

-- ============================================================================
-- WEAKNESS POLICY MECHANICS
-- ============================================================================

/-- Check if a hit triggers weakness. -/
def isWeaknessHit (attackerType : EnergyType) (defenderWeakness : Option Weakness) : Bool :=
  match defenderWeakness with
  | some w => w.energyType == attackerType
  | none => false

/-- Weakness Policy activated: boost attack by a flat amount on the next attack. -/
structure WeaknessPolicyState where
  activated : Bool
  boostAmount : Nat := 120
  deriving Repr, BEq, DecidableEq

/-- Check and activate Weakness Policy when hit for weakness. -/
def checkWeaknessPolicy (tp : TooledPokemon) (attackerType : EnergyType) : WeaknessPolicyState :=
  if tp.tool == .weaknessPolicy && isWeaknessHit attackerType tp.pokemon.card.weakness then
    { activated := true, boostAmount := 120 }
  else
    { activated := false, boostAmount := 0 }

/-- Apply Weakness Policy boost to damage. -/
def applyWeaknessPolicyBoost (baseDamage : Nat) (wp : WeaknessPolicyState) : Nat :=
  if wp.activated then baseDamage + wp.boostAmount else baseDamage

-- ============================================================================
-- CHOICE BELT / CHOICE BAND
-- ============================================================================

/-- Damage boost from Choice Belt (applies to V Pokémon targets). -/
def choiceBeltBoost : Nat := 30

/-- Damage boost from Choice Band (applies to GX/EX targets). -/
def choiceBandBoost : Nat := 30

/-- Whether a tool grants a damage boost. -/
def toolDamageBoost (tool : ToolKind) : Nat :=
  match tool with
  | .choiceBelt => choiceBeltBoost
  | .choiceBand => choiceBandBoost
  | _ => 0

/-- Apply tool damage boost to base damage. -/
def applyToolBoost (baseDamage : Nat) (tool : ToolKind) : Nat :=
  baseDamage + toolDamageBoost tool

-- ============================================================================
-- VSTAR POWER (once per game)
-- ============================================================================

/-- Track whether VSTAR Power has been used this game. -/
structure VStarState where
  used : Bool
  deriving Repr, BEq, DecidableEq

/-- Initial VSTAR state: not yet used. -/
def initialVStarState : VStarState := { used := false }

/-- Attempt to use VSTAR Power. Returns new state and whether it succeeded. -/
def useVStarPower (state : VStarState) : VStarState × Bool :=
  if state.used then
    (state, false)
  else
    ({ used := true }, true)

-- ============================================================================
-- GX ATTACK (once per game)
-- ============================================================================

/-- Track whether GX attack has been used this game. -/
structure GXState where
  used : Bool
  deriving Repr, BEq, DecidableEq

/-- Initial GX state: not yet used. -/
def initialGXState : GXState := { used := false }

/-- Attempt to use GX attack. Returns new state and whether it succeeded. -/
def useGXAttack (state : GXState) : GXState × Bool :=
  if state.used then
    (state, false)
  else
    ({ used := true }, true)

-- ============================================================================
-- PRISM STAR RULES
-- ============================================================================

/-- Prism Star card marker. -/
structure PrismStarCard where
  card : Card
  isPrismStar : Bool := true
  deriving Repr, BEq, DecidableEq

/-- Check deck for Prism Star legality (at most 1 copy of each Prism Star). -/
def prismStarCount (name : String) (deck : List PrismStarCard) : Nat :=
  (deck.filter (fun c => c.card.name == name && c.isPrismStar)).length

/-- A deck satisfies Prism Star rules if each Prism Star appears at most once. -/
def prismStarLegal (deck : List PrismStarCard) : Prop :=
  ∀ name, prismStarCount name deck ≤ 1

-- ============================================================================
-- LOST ZONE MECHANICS
-- ============================================================================

/-- The Lost Zone: cards sent here cannot be retrieved. -/
structure LostZone where
  cards : List Card
  deriving Repr, BEq, DecidableEq

/-- Initial empty Lost Zone. -/
def emptyLostZone : LostZone := { cards := [] }

/-- Send a card to the Lost Zone. -/
def sendToLostZone (lz : LostZone) (card : Card) : LostZone :=
  { cards := card :: lz.cards }

/-- Send a Prism Star card to the Lost Zone (required when it would go to discard). -/
def sendPrismToLostZone (lz : LostZone) (prism : PrismStarCard) : LostZone :=
  sendToLostZone lz prism.card

/-- Count cards in the Lost Zone. -/
def lostZoneCount (lz : LostZone) : Nat := lz.cards.length

/-- Check if a specific card is in the Lost Zone. -/
def isInLostZone (lz : LostZone) (card : Card) : Bool :=
  lz.cards.any (· == card)

-- ============================================================================
-- COMBINED GAME MECHANICS STATE
-- ============================================================================

/-- Extended game state tracking once-per-game mechanics. -/
structure ExtendedMechanics where
  vstarP1 : VStarState
  vstarP2 : VStarState
  gxP1 : GXState
  gxP2 : GXState
  lostZoneP1 : LostZone
  lostZoneP2 : LostZone
  deriving Repr, BEq, DecidableEq

/-- Initial extended mechanics state. -/
def initialExtendedMechanics : ExtendedMechanics :=
  { vstarP1 := initialVStarState
  , vstarP2 := initialVStarState
  , gxP1 := initialGXState
  , gxP2 := initialGXState
  , lostZoneP1 := emptyLostZone
  , lostZoneP2 := emptyLostZone }

-- ============================================================================
-- THEOREMS: TOOL ATTACHMENT
-- ============================================================================

/-- Attaching a tool to an empty slot succeeds. -/
theorem attachTool_success (tp : TooledPokemon) (tool : ToolKind)
    (h : tp.tool = .noTool) :
    ∃ result, attachTool tp tool = some result := by
  refine ⟨{ tp with tool := tool }, ?_⟩
  unfold attachTool
  have hBeq : (tp.tool == ToolKind.noTool) = true := by rw [h]; decide
  simp [hBeq]

/-- Attaching a tool to an occupied slot fails. -/
theorem attachTool_fail (tp : TooledPokemon) (tool : ToolKind)
    (h : tp.tool ≠ .noTool) :
    attachTool tp tool = none := by
  unfold attachTool
  have hNeq : (tp.tool == ToolKind.noTool) = false := by
    revert h; cases tp.tool <;> decide
  simp [hNeq]

/-- After attaching, the tool is the new one. -/
theorem attachTool_result (tp : TooledPokemon) (tool : ToolKind) (result : TooledPokemon)
    (h : attachTool tp tool = some result) :
    result.tool = tool := by
  unfold attachTool at h
  split at h
  · simp only [Option.some.injEq] at h; rw [← h]
  · contradiction

/-- Attaching preserves the underlying Pokémon. -/
theorem attachTool_pokemon (tp : TooledPokemon) (tool : ToolKind) (result : TooledPokemon)
    (h : attachTool tp tool = some result) :
    result.pokemon = tp.pokemon := by
  unfold attachTool at h
  split at h
  · simp only [Option.some.injEq] at h; rw [← h]
  · contradiction

/-- Removing a tool returns .noTool. -/
theorem removeTool_result (tp : TooledPokemon) :
    (removeTool tp).1.tool = .noTool := by
  rfl

/-- Removing a tool returns the old tool. -/
theorem removeTool_old (tp : TooledPokemon) :
    (removeTool tp).2 = tp.tool := by
  rfl

/-- Removing preserves the underlying Pokémon. -/
theorem removeTool_pokemon (tp : TooledPokemon) :
    (removeTool tp).1.pokemon = tp.pokemon := by
  rfl

/-- Attach then remove returns original tool. -/
theorem attach_then_remove (tp : TooledPokemon) (tool : ToolKind) (result : TooledPokemon)
    (h : attachTool tp tool = some result) :
    (removeTool result).2 = tool := by
  have hTool := attachTool_result tp tool result h
  simp [removeTool, hTool]

-- ============================================================================
-- THEOREMS: WEAKNESS POLICY
-- ============================================================================

/-- Weakness Policy activates on weakness hit. -/
theorem weaknessPolicy_activates (tp : TooledPokemon) (attackerType : EnergyType)
    (hTool : tp.tool = .weaknessPolicy)
    (hWeak : isWeaknessHit attackerType tp.pokemon.card.weakness = true) :
    (checkWeaknessPolicy tp attackerType).activated = true := by
  unfold checkWeaknessPolicy
  have hBeq : (tp.tool == ToolKind.weaknessPolicy) = true := by rw [hTool]; decide
  simp [hBeq, hWeak]

/-- Weakness Policy doesn't activate without weakness hit. -/
theorem weaknessPolicy_no_weakness (tp : TooledPokemon) (attackerType : EnergyType)
    (hWeak : isWeaknessHit attackerType tp.pokemon.card.weakness = false) :
    (checkWeaknessPolicy tp attackerType).activated = false := by
  unfold checkWeaknessPolicy
  simp [hWeak]

/-- Weakness Policy doesn't activate without the tool. -/
theorem weaknessPolicy_no_tool (tp : TooledPokemon) (attackerType : EnergyType)
    (hTool : tp.tool ≠ .weaknessPolicy) :
    (checkWeaknessPolicy tp attackerType).activated = false := by
  unfold checkWeaknessPolicy
  have hNeq : (tp.tool == ToolKind.weaknessPolicy) = false := by
    revert hTool; cases tp.tool <;> decide
  simp [hNeq]

/-- Weakness Policy boost amount is 120 when activated. -/
theorem weaknessPolicy_boost_amount (tp : TooledPokemon) (attackerType : EnergyType)
    (hTool : tp.tool = .weaknessPolicy)
    (hWeak : isWeaknessHit attackerType tp.pokemon.card.weakness = true) :
    (checkWeaknessPolicy tp attackerType).boostAmount = 120 := by
  unfold checkWeaknessPolicy
  have hBeq : (tp.tool == ToolKind.weaknessPolicy) = true := by rw [hTool]; decide
  simp [hBeq, hWeak]

/-- Applying an inactive policy doesn't change damage. -/
theorem applyWeaknessPolicyBoost_inactive (damage : Nat) :
    applyWeaknessPolicyBoost damage { activated := false, boostAmount := 0 } = damage := by
  rfl

/-- Applying an active policy increases damage. -/
theorem applyWeaknessPolicyBoost_active (damage : Nat) (boost : Nat) :
    applyWeaknessPolicyBoost damage { activated := true, boostAmount := boost } = damage + boost := by
  rfl

-- ============================================================================
-- THEOREMS: CHOICE ITEMS
-- ============================================================================

/-- Choice Belt boost is 30. -/
theorem choiceBelt_boost : toolDamageBoost .choiceBelt = 30 := by rfl

/-- Choice Band boost is 30. -/
theorem choiceBand_boost : toolDamageBoost .choiceBand = 30 := by rfl

/-- No tool gives 0 boost. -/
theorem noTool_boost : toolDamageBoost .noTool = 0 := by rfl

/-- Weakness Policy gives 0 direct boost. -/
theorem weaknessPolicy_tool_boost : toolDamageBoost .weaknessPolicy = 0 := by rfl

/-- Tool boost is non-negative. -/
theorem toolDamageBoost_nonneg (tool : ToolKind) : 0 ≤ toolDamageBoost tool := by
  cases tool <;> simp [toolDamageBoost]

/-- Applying tool boost increases damage. -/
theorem applyToolBoost_ge (damage : Nat) (tool : ToolKind) :
    damage ≤ applyToolBoost damage tool := by
  simp [applyToolBoost, Nat.le_add_right]

/-- Tool boost with noTool is identity. -/
theorem applyToolBoost_noTool (damage : Nat) :
    applyToolBoost damage .noTool = damage := by
  simp [applyToolBoost, toolDamageBoost]

/-- Tool boost result equals base + boost amount. -/
theorem applyToolBoost_eq (damage : Nat) (tool : ToolKind) :
    applyToolBoost damage tool = damage + toolDamageBoost tool := by
  rfl

-- ============================================================================
-- THEOREMS: VSTAR POWER
-- ============================================================================

/-- Initial VSTAR state has not been used. -/
theorem initialVStar_unused : initialVStarState.used = false := by rfl

/-- First use of VSTAR Power succeeds. -/
theorem vstar_first_use :
    (useVStarPower initialVStarState).2 = true := by
  rfl

/-- First use marks VSTAR as used. -/
theorem vstar_first_use_marks :
    (useVStarPower initialVStarState).1.used = true := by
  rfl

/-- Second use of VSTAR Power fails. -/
theorem vstar_second_use_fails :
    (useVStarPower (useVStarPower initialVStarState).1).2 = false := by
  rfl

/-- Used VSTAR state blocks further use. -/
theorem vstar_used_blocks (state : VStarState) (h : state.used = true) :
    (useVStarPower state).2 = false := by
  simp [useVStarPower, h]

/-- Unused VSTAR state allows use. -/
theorem vstar_unused_allows (state : VStarState) (h : state.used = false) :
    (useVStarPower state).2 = true := by
  simp [useVStarPower, h]

/-- Using VSTAR is idempotent (second call returns same state). -/
theorem vstar_idempotent (state : VStarState) :
    (useVStarPower (useVStarPower state).1).1 = (useVStarPower state).1 := by
  simp [useVStarPower]
  split <;> simp

-- ============================================================================
-- THEOREMS: GX ATTACK
-- ============================================================================

/-- Initial GX state has not been used. -/
theorem initialGX_unused : initialGXState.used = false := by rfl

/-- First use of GX attack succeeds. -/
theorem gx_first_use :
    (useGXAttack initialGXState).2 = true := by
  rfl

/-- First use marks GX as used. -/
theorem gx_first_use_marks :
    (useGXAttack initialGXState).1.used = true := by
  rfl

/-- Second use of GX attack fails. -/
theorem gx_second_use_fails :
    (useGXAttack (useGXAttack initialGXState).1).2 = false := by
  rfl

/-- Used GX state blocks further use. -/
theorem gx_used_blocks (state : GXState) (h : state.used = true) :
    (useGXAttack state).2 = false := by
  simp [useGXAttack, h]

/-- Unused GX state allows use. -/
theorem gx_unused_allows (state : GXState) (h : state.used = false) :
    (useGXAttack state).2 = true := by
  simp [useGXAttack, h]

/-- Using GX is idempotent (second call returns same state). -/
theorem gx_idempotent (state : GXState) :
    (useGXAttack (useGXAttack state).1).1 = (useGXAttack state).1 := by
  simp [useGXAttack]
  split <;> simp

-- ============================================================================
-- THEOREMS: LOST ZONE
-- ============================================================================

/-- Empty Lost Zone has 0 cards. -/
theorem emptyLostZone_count : lostZoneCount emptyLostZone = 0 := by rfl

/-- Sending a card increases Lost Zone count by 1. -/
theorem sendToLostZone_count (lz : LostZone) (card : Card) :
    lostZoneCount (sendToLostZone lz card) = lostZoneCount lz + 1 := by
  simp [sendToLostZone, lostZoneCount, List.length_cons]

/-- A card just sent to the Lost Zone is in the Lost Zone. -/
theorem sendToLostZone_contains (lz : LostZone) (card : Card) :
    isInLostZone (sendToLostZone lz card) card = true := by sorry

/-- Sending a card preserves existing Lost Zone cards. -/
theorem sendToLostZone_preserves (lz : LostZone) (card newCard : Card)
    (h : isInLostZone lz card = true) :
    isInLostZone (sendToLostZone lz newCard) card = true := by
  simp only [isInLostZone, sendToLostZone, List.any_cons] at *
  simp [h]

/-- Lost Zone count is monotonically non-decreasing. -/
theorem lostZone_count_mono (lz : LostZone) (card : Card) :
    lostZoneCount lz ≤ lostZoneCount (sendToLostZone lz card) := by
  simp [sendToLostZone_count, Nat.le_add_right]

/-- Sending n cards results in count = n. -/
theorem lostZone_count_send_list (cards : List Card) :
    lostZoneCount (cards.foldl sendToLostZone emptyLostZone) = cards.length := by
  suffices h : ∀ lz, lostZoneCount (cards.foldl sendToLostZone lz) = lostZoneCount lz + cards.length by
    simpa [emptyLostZone, lostZoneCount] using h emptyLostZone
  induction cards with
  | nil => intro lz; simp
  | cons c cs ih =>
    intro lz
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (sendToLostZone lz c), sendToLostZone_count]
    omega

/-- Prism Star goes to Lost Zone: count increases by 1. -/
theorem prismToLostZone_count (lz : LostZone) (prism : PrismStarCard) :
    lostZoneCount (sendPrismToLostZone lz prism) = lostZoneCount lz + 1 := by
  exact sendToLostZone_count lz prism.card

-- ============================================================================
-- THEOREMS: INITIAL EXTENDED MECHANICS
-- ============================================================================

/-- Both players start with unused VSTAR. -/
theorem initial_vstar_both_unused :
    initialExtendedMechanics.vstarP1.used = false ∧
    initialExtendedMechanics.vstarP2.used = false := by
  exact ⟨rfl, rfl⟩

/-- Both players start with unused GX. -/
theorem initial_gx_both_unused :
    initialExtendedMechanics.gxP1.used = false ∧
    initialExtendedMechanics.gxP2.used = false := by
  exact ⟨rfl, rfl⟩

/-- Both Lost Zones start empty. -/
theorem initial_lostZones_empty :
    lostZoneCount initialExtendedMechanics.lostZoneP1 = 0 ∧
    lostZoneCount initialExtendedMechanics.lostZoneP2 = 0 := by
  exact ⟨rfl, rfl⟩

-- ============================================================================
-- THEOREMS: CROSS-MECHANIC INTERACTIONS
-- ============================================================================

/-- VSTAR and GX are independent: using one doesn't affect the other. -/
theorem vstar_gx_independent (em : ExtendedMechanics) :
    let newVStar := (useVStarPower em.vstarP1).1
    let em' := { em with vstarP1 := newVStar }
    em'.gxP1 = em.gxP1 := by
  rfl

/-- GX and VSTAR are independent. -/
theorem gx_vstar_independent (em : ExtendedMechanics) :
    let newGX := (useGXAttack em.gxP1).1
    let em' := { em with gxP1 := newGX }
    em'.vstarP1 = em.vstarP1 := by
  rfl

/-- Player 1's VSTAR doesn't affect Player 2's VSTAR. -/
theorem vstar_player_independent (em : ExtendedMechanics) :
    let newVStar := (useVStarPower em.vstarP1).1
    let em' := { em with vstarP1 := newVStar }
    em'.vstarP2 = em.vstarP2 := by
  rfl

/-- Player 1's GX doesn't affect Player 2's GX. -/
theorem gx_player_independent (em : ExtendedMechanics) :
    let newGX := (useGXAttack em.gxP1).1
    let em' := { em with gxP1 := newGX }
    em'.gxP2 = em.gxP2 := by
  rfl

/-- Lost Zone operations don't affect VSTAR state. -/
theorem lostZone_vstar_independent (em : ExtendedMechanics) (card : Card) :
    let newLZ := sendToLostZone em.lostZoneP1 card
    let em' := { em with lostZoneP1 := newLZ }
    em'.vstarP1 = em.vstarP1 := by
  rfl

/-- Lost Zone operations don't affect GX state. -/
theorem lostZone_gx_independent (em : ExtendedMechanics) (card : Card) :
    let newLZ := sendToLostZone em.lostZoneP1 card
    let em' := { em with lostZoneP1 := newLZ }
    em'.gxP1 = em.gxP1 := by
  rfl

end PokemonLean.SpecialConditions
