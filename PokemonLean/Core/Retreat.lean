/-
  PokemonLean / Core / Retreat.lean

  Comprehensive Pokémon TCG retreat system.
  Covers retreat cost (0-5 energy), retreat cost reduction tools
  (Float Stone, Air Balloon), status conditions blocking retreat
  (Asleep, Paralyzed block; Poison, Burn, Confused don't),
  Switch/Escape Rope (bypass cost), Rush In ability, retreat curing
  all special conditions, and the one-retreat-per-turn rule.

  Self-contained — no imports from other PokemonLean modules.
  All proofs are sorry-free.  30+ theorems.
-/

namespace PokemonLean.Core.RetreatMod

-- ============================================================
-- §1  Core Types (self-contained)
-- ============================================================

/-- Special conditions in the Pokémon TCG. -/
inductive SpecialCondition where
  | poisoned
  | burned
  | asleep
  | confused
  | paralyzed
deriving DecidableEq, Repr, BEq, Inhabited

/-- Condition state for a Pokémon (simplified for retreat logic). -/
structure ConditionState where
  isPoisoned  : Bool := false
  isBurned    : Bool := false
  isAsleep    : Bool := false
  isConfused  : Bool := false
  isParalyzed : Bool := false
deriving DecidableEq, Repr, Inhabited

/-- Healthy condition state: no conditions. -/
def ConditionState.healthy : ConditionState := {}

/-- Check if the Pokémon has any special condition. -/
def ConditionState.hasAnyCondition (cs : ConditionState) : Bool :=
  cs.isPoisoned || cs.isBurned || cs.isAsleep || cs.isConfused || cs.isParalyzed

/-- Clear ALL special conditions (happens when retreating, evolving, etc.). -/
def ConditionState.clearAll (_cs : ConditionState) : ConditionState :=
  ConditionState.healthy

-- ============================================================
-- §2  Retreat Cost and Tools
-- ============================================================

/-- Retreat tool attached to a Pokémon. -/
inductive RetreatTool where
  | none         -- No retreat tool
  | floatStone   -- Retreat cost becomes 0
  | airBalloon   -- Retreat cost reduced by 2
deriving DecidableEq, Repr, BEq, Inhabited

/-- Base retreat cost for a Pokémon (0-5 in the TCG). -/
structure RetreatInfo where
  baseCost : Nat
  tool     : RetreatTool
deriving DecidableEq, Repr, Inhabited

/-- Effective retreat cost after applying tools.
    Float Stone → 0, Air Balloon → max(0, base - 2). -/
def RetreatInfo.effectiveCost (ri : RetreatInfo) : Nat :=
  match ri.tool with
  | .none       => ri.baseCost
  | .floatStone => 0
  | .airBalloon => if ri.baseCost ≥ 2 then ri.baseCost - 2 else 0

/-- Whether this Pokémon can retreat for free (effective cost = 0). -/
def RetreatInfo.isFreeRetreat (ri : RetreatInfo) : Bool :=
  ri.effectiveCost == 0

-- ============================================================
-- §3  Retreat Blocking by Status Conditions
-- ============================================================

/-- Can this Pokémon retreat based on its condition state?
    Asleep and Paralyzed BLOCK retreat.
    Poisoned, Burned, and Confused do NOT block retreat. -/
def canRetreatWithConditions (cs : ConditionState) : Bool :=
  !cs.isAsleep && !cs.isParalyzed

/-- Does a specific condition block retreat? -/
def conditionBlocksRetreat : SpecialCondition → Bool
  | .asleep    => true
  | .paralyzed => true
  | .poisoned  => false
  | .burned    => false
  | .confused  => false

-- ============================================================
-- §4  Energy Payment for Retreat
-- ============================================================

/-- Simplified energy pool for retreat payment. -/
structure RetreatEnergyPool where
  totalEnergy : Nat    -- Total energy cards attached
deriving DecidableEq, Repr, Inhabited

/-- Can the Pokémon pay its retreat cost? -/
def canPayRetreatCost (pool : RetreatEnergyPool) (ri : RetreatInfo) : Bool :=
  pool.totalEnergy ≥ ri.effectiveCost

/-- Energy pool after paying retreat cost. -/
def payRetreatCost (pool : RetreatEnergyPool) (ri : RetreatInfo) : RetreatEnergyPool :=
  if canPayRetreatCost pool ri then
    { totalEnergy := pool.totalEnergy - ri.effectiveCost }
  else pool

-- ============================================================
-- §5  Switch and Escape Rope
-- ============================================================

/-- Methods to move the active Pokémon to bench. -/
inductive SwitchMethod where
  | normalRetreat    -- Pay retreat cost, once per turn
  | switchTrainer    -- Switch trainer card: bypass cost entirely
  | escapeRope       -- Escape Rope: both players switch, bypasses cost
  | rushInAbility    -- Rush In (e.g., Keldeo-EX): move from bench to active
  | bossOrders       -- Boss's Orders: opponent's Pokémon brought active (not retreat)
deriving DecidableEq, Repr, BEq, Inhabited

/-- Does this switch method require paying retreat cost? -/
def SwitchMethod.requiresPayment : SwitchMethod → Bool
  | .normalRetreat => true
  | .switchTrainer => false
  | .escapeRope    => false
  | .rushInAbility => false
  | .bossOrders    => false

/-- Does this switch method count as the once-per-turn retreat? -/
def SwitchMethod.countsAsRetreat : SwitchMethod → Bool
  | .normalRetreat => true
  | .switchTrainer => false
  | .escapeRope    => false
  | .rushInAbility => false
  | .bossOrders    => false

/-- Does this switch method cure special conditions? -/
def SwitchMethod.curesConditions : SwitchMethod → Bool
  | .normalRetreat => true
  | .switchTrainer => true
  | .escapeRope    => true
  | .rushInAbility => true
  | .bossOrders    => true

-- ============================================================
-- §6  Retreat Turn State
-- ============================================================

/-- Turn state for retreat. -/
structure RetreatTurnState where
  hasRetreated : Bool    -- Has the player used their normal retreat this turn?
deriving DecidableEq, Repr, Inhabited

/-- Initial retreat state: haven't retreated yet. -/
def RetreatTurnState.initial : RetreatTurnState :=
  { hasRetreated := false }

/-- Can use normal retreat? Only if haven't used it yet this turn. -/
def RetreatTurnState.canNormalRetreat (rts : RetreatTurnState) : Bool :=
  !rts.hasRetreated

/-- Use the normal retreat. -/
def RetreatTurnState.useRetreat (_rts : RetreatTurnState) : RetreatTurnState :=
  { hasRetreated := true }

-- ============================================================
-- §7  Full Retreat Validation
-- ============================================================

/-- Full retreat check: can a Pokémon retreat normally?
    Requires: no blocking conditions, haven't retreated this turn,
    and enough energy to pay the (tool-adjusted) cost. -/
def canFullRetreat
    (cs : ConditionState)
    (ri : RetreatInfo)
    (pool : RetreatEnergyPool)
    (turnState : RetreatTurnState) : Bool :=
  canRetreatWithConditions cs &&
  turnState.canNormalRetreat &&
  canPayRetreatCost pool ri

/-- Can use a Switch-type effect? Only blocked conditions check is bypassed
    for Switch/Escape Rope. These bypass everything. -/
def canUseSwitch
    (method : SwitchMethod)
    (cs : ConditionState)
    (ri : RetreatInfo)
    (pool : RetreatEnergyPool)
    (turnState : RetreatTurnState) : Bool :=
  match method with
  | .normalRetreat => canFullRetreat cs ri pool turnState
  | .switchTrainer => true   -- Always works
  | .escapeRope    => true   -- Always works
  | .rushInAbility => true   -- Always works (from bench)
  | .bossOrders    => true   -- Always works (opponent's Pokémon)

-- ============================================================
-- §8  Post-Retreat Condition State
-- ============================================================

/-- After retreating (any method), all conditions are cured. -/
def conditionsAfterRetreat (cs : ConditionState) (method : SwitchMethod) :
    ConditionState :=
  if method.curesConditions then cs.clearAll else cs

-- ============================================================
-- §9  Example Pokémon Retreat Scenarios
-- ============================================================

/-- Snorlax: retreat cost 4, no tool. -/
def snorlaxRetreat : RetreatInfo :=
  { baseCost := 4, tool := .none }

/-- Snorlax with Float Stone: retreat cost 0. -/
def snorlaxWithFloatStone : RetreatInfo :=
  { baseCost := 4, tool := .floatStone }

/-- Snorlax with Air Balloon: retreat cost 2. -/
def snorlaxWithAirBalloon : RetreatInfo :=
  { baseCost := 4, tool := .airBalloon }

/-- Jolteon: retreat cost 0 naturally. -/
def jolteonRetreat : RetreatInfo :=
  { baseCost := 0, tool := .none }

/-- Wailord: retreat cost 5 (highest printed). -/
def wailordRetreat : RetreatInfo :=
  { baseCost := 5, tool := .none }

/-- Wailord with Air Balloon: retreat cost 3. -/
def wailordWithAirBalloon : RetreatInfo :=
  { baseCost := 5, tool := .airBalloon }

-- ============================================================
-- §10  Theorems — Status Blocking
-- ============================================================

/-- Paralyzed Pokémon cannot retreat. -/
theorem paralyzed_cannot_retreat :
    canRetreatWithConditions { isParalyzed := true } = false := by rfl

/-- Asleep Pokémon cannot retreat. -/
theorem asleep_cannot_retreat :
    canRetreatWithConditions { isAsleep := true } = false := by rfl

/-- Poisoned Pokémon CAN retreat. -/
theorem poisoned_can_retreat :
    canRetreatWithConditions { isPoisoned := true } = true := by rfl

/-- Burned Pokémon CAN retreat. -/
theorem burned_can_retreat :
    canRetreatWithConditions { isBurned := true } = true := by rfl

/-- Confused Pokémon CAN retreat. -/
theorem confused_can_retreat :
    canRetreatWithConditions { isConfused := true } = true := by rfl

/-- Healthy Pokémon can retreat. -/
theorem healthy_can_retreat :
    canRetreatWithConditions ConditionState.healthy = true := by rfl

/-- Asleep blocks retreat (specific condition check). -/
theorem asleep_blocks : conditionBlocksRetreat .asleep = true := by rfl

/-- Paralyzed blocks retreat (specific condition check). -/
theorem paralyzed_blocks : conditionBlocksRetreat .paralyzed = true := by rfl

/-- Poisoned does not block retreat. -/
theorem poisoned_no_block : conditionBlocksRetreat .poisoned = false := by rfl

/-- Burned does not block retreat. -/
theorem burned_no_block : conditionBlocksRetreat .burned = false := by rfl

/-- Confused does not block retreat. -/
theorem confused_no_block : conditionBlocksRetreat .confused = false := by rfl

-- ============================================================
-- §11  Theorems — Float Stone
-- ============================================================

/-- Float Stone makes any Pokémon free retreat. -/
theorem float_stone_free (cost : Nat) :
    (RetreatInfo.mk cost .floatStone).effectiveCost = 0 := by
  simp [RetreatInfo.effectiveCost]

/-- Float Stone makes retreat free for Snorlax (cost 4). -/
theorem snorlax_float_stone_free :
    snorlaxWithFloatStone.effectiveCost = 0 := by rfl

/-- Float Stone always gives free retreat regardless of base cost. -/
theorem float_stone_always_free (ri : RetreatInfo) (h : ri.tool = .floatStone) :
    ri.isFreeRetreat = true := by
  simp [RetreatInfo.isFreeRetreat, RetreatInfo.effectiveCost, h]

-- ============================================================
-- §12  Theorems — Air Balloon
-- ============================================================

/-- Air Balloon reduces Snorlax retreat from 4 to 2. -/
theorem snorlax_air_balloon :
    snorlaxWithAirBalloon.effectiveCost = 2 := by rfl

/-- Air Balloon reduces Wailord retreat from 5 to 3. -/
theorem wailord_air_balloon :
    wailordWithAirBalloon.effectiveCost = 3 := by rfl

/-- Air Balloon on a 1-cost Pokémon makes retreat free. -/
theorem air_balloon_one_cost :
    (RetreatInfo.mk 1 .airBalloon).effectiveCost = 0 := by rfl

/-- Air Balloon on a 2-cost Pokémon makes retreat free. -/
theorem air_balloon_two_cost :
    (RetreatInfo.mk 2 .airBalloon).effectiveCost = 0 := by rfl

/-- Air Balloon on a 0-cost Pokémon: still 0. -/
theorem air_balloon_zero_cost :
    (RetreatInfo.mk 0 .airBalloon).effectiveCost = 0 := by rfl

-- ============================================================
-- §13  Theorems — Switch/Escape Rope
-- ============================================================

/-- Switch always works (no cost, no condition check). -/
theorem switch_always_works (cs : ConditionState) (ri : RetreatInfo)
    (pool : RetreatEnergyPool) (ts : RetreatTurnState) :
    canUseSwitch .switchTrainer cs ri pool ts = true := by rfl

/-- Escape Rope always works. -/
theorem escape_rope_always_works (cs : ConditionState) (ri : RetreatInfo)
    (pool : RetreatEnergyPool) (ts : RetreatTurnState) :
    canUseSwitch .escapeRope cs ri pool ts = true := by rfl

/-- Switch does not require payment. -/
theorem switch_no_payment : SwitchMethod.switchTrainer.requiresPayment = false := by rfl

/-- Normal retreat requires payment. -/
theorem normal_retreat_payment : SwitchMethod.normalRetreat.requiresPayment = true := by rfl

/-- Switch does not count as retreat for the once-per-turn limit. -/
theorem switch_not_counted : SwitchMethod.switchTrainer.countsAsRetreat = false := by rfl

/-- Escape Rope does not count as retreat. -/
theorem escape_rope_not_counted : SwitchMethod.escapeRope.countsAsRetreat = false := by rfl

-- ============================================================
-- §14  Theorems — Retreat Cures Conditions
-- ============================================================

/-- Normal retreat cures conditions. -/
theorem normal_retreat_cures : SwitchMethod.normalRetreat.curesConditions = true := by rfl

/-- Switch cures conditions. -/
theorem switch_cures : SwitchMethod.switchTrainer.curesConditions = true := by rfl

/-- Retreating a poisoned Pokémon cures the poison. -/
theorem retreat_cures_poison :
    (conditionsAfterRetreat { isPoisoned := true } .normalRetreat).isPoisoned = false := by rfl

/-- Retreating a paralyzed Pokémon via Switch cures paralysis. -/
theorem switch_cures_paralysis :
    (conditionsAfterRetreat { isParalyzed := true } .switchTrainer).isParalyzed = false := by rfl

/-- After retreating, no conditions remain. -/
theorem retreat_clears_all (cs : ConditionState) (m : SwitchMethod) (h : m.curesConditions = true) :
    (conditionsAfterRetreat cs m).hasAnyCondition = false := by
  simp [conditionsAfterRetreat, h, ConditionState.clearAll, ConditionState.healthy,
        ConditionState.hasAnyCondition]

-- ============================================================
-- §15  Theorems — Once Per Turn
-- ============================================================

/-- Initially, retreat is available. -/
theorem initial_can_retreat :
    RetreatTurnState.initial.canNormalRetreat = true := by rfl

/-- After retreating, cannot retreat again normally. -/
theorem retreat_once (rts : RetreatTurnState) :
    (rts.useRetreat).canNormalRetreat = false := by
  simp [RetreatTurnState.useRetreat, RetreatTurnState.canNormalRetreat]

/-- Retreat use is idempotent. -/
theorem retreat_idempotent (rts : RetreatTurnState) :
    (rts.useRetreat).useRetreat = rts.useRetreat := by
  simp [RetreatTurnState.useRetreat]

-- ============================================================
-- §16  Theorems — Energy Payment
-- ============================================================

/-- Jolteon retreats for free (cost 0, no tool needed). -/
theorem jolteon_free_retreat :
    jolteonRetreat.effectiveCost = 0 := by rfl

/-- Can pay retreat with enough energy. -/
theorem can_pay_with_enough :
    canPayRetreatCost { totalEnergy := 4 } snorlaxRetreat = true := by rfl

/-- Cannot pay retreat without enough energy. -/
theorem cannot_pay_without :
    canPayRetreatCost { totalEnergy := 3 } snorlaxRetreat = false := by rfl

/-- Energy remaining after paying retreat: 5 - 4 = 1. -/
theorem energy_after_retreat :
    (payRetreatCost { totalEnergy := 5 } snorlaxRetreat).totalEnergy = 1 := by rfl

/-- Float Stone means no energy payment needed (even with 0 energy). -/
theorem float_stone_no_payment :
    canPayRetreatCost { totalEnergy := 0 } snorlaxWithFloatStone = true := by rfl

/-- Snorlax without tool needs 4 energy to retreat. -/
theorem snorlax_needs_four : snorlaxRetreat.effectiveCost = 4 := by rfl

/-- Wailord without tool needs 5 energy to retreat. -/
theorem wailord_needs_five : wailordRetreat.effectiveCost = 5 := by rfl

/-- No tool means effective cost = base cost. -/
theorem no_tool_base_cost (cost : Nat) :
    (RetreatInfo.mk cost .none).effectiveCost = cost := by
  simp [RetreatInfo.effectiveCost]

end PokemonLean.Core.RetreatMod
