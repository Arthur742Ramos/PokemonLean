/-
  Core/ConditionStrategy.lean — Pokemon TCG Condition-Based Strategies
  Roxanne combos, condition stacking pressure, strategic analysis
-/
import Core.Types
import Core.SpecialConditions
import Core.ConditionRemoval

-- ============================================================
--  Roxanne & Condition Combos
-- ============================================================

/-- Roxanne supporter: opponent draws down to 2, you draw 6.
    Devastating when combined with condition lock. -/
structure RoxannePlay where
  opponentPrizeCards : Nat  -- must be ≤ 3 for Roxanne to be playable
  activeConditions : ConditionState
  deriving Repr

/-- Roxanne is playable when opponent has 3 or fewer prize cards -/
def roxannePlayable (r : RoxannePlay) : Bool :=
  decide (r.opponentPrizeCards ≤ 3)

/-- Roxanne + condition lock value: higher when opponent can't act -/
def roxanneConditionValue (r : RoxannePlay) : Nat :=
  let baseValue := if roxannePlayable r then 50 else 0
  let lockBonus := if !canAttack r.activeConditions then 30 else 0
  let damageBonus := betweenTurnsDamage r.activeConditions
  baseValue + lockBonus + damageBonus

/-- Condition pressure score: how much pressure conditions apply -/
def conditionPressure (cs : ConditionState) : Nat :=
  let damagePressure := betweenTurnsDamage cs
  let lockPressure := if !canAttack cs then 40 else 0
  let confusionPressure := if cs.isConfused then 20 else 0
  damagePressure + lockPressure + confusionPressure

/-- Optimal condition combination: Poison + Burn + Paralysis -/
def maxPressureConditions : ConditionState :=
  applyCondition
    (applyCondition
      (applyCondition noConditions SpecialCondition.poison)
      SpecialCondition.burn)
    SpecialCondition.paralysis

/-- Aggressive condition combo: Poison + Burn + Confusion -/
def aggressiveConditions : ConditionState :=
  applyCondition
    (applyCondition
      (applyCondition noConditions SpecialCondition.poison)
      SpecialCondition.burn)
    SpecialCondition.confusion

/-- Turns to KO from conditions alone (simplified, no healing/cure) -/
def turnsToConditionKO (currentHp : Nat) (cs : ConditionState) : Nat :=
  let dmgPerTurn := betweenTurnsDamage cs
  if dmgPerTurn == 0 then 0  -- never KOs from conditions
  else (currentHp + dmgPerTurn - 1) / dmgPerTurn  -- ceiling division

/-- Strategy: should we use Switch to save our Pokemon? -/
def shouldSwitch (ap : ActivePokemon) (hasBenchMon : Bool) : Bool :=
  hasBenchMon && (needsUrgentRemoval ap.conditions ||
    (ap.pokemon.currentHp ≤ betweenTurnsDamage ap.conditions))

/-- Strategy: is condition stalling viable?
    (opponent locked + taking chip damage) -/
def conditionStallViable (oppConditions : ConditionState) : Bool :=
  !canAttack oppConditions && betweenTurnsDamage oppConditions > 0

/-- Calculate effective damage accounting for confusion flip -/
def effectiveConfusionDamage (baseDamage : Nat) (isConfused : Bool) : Nat :=
  if isConfused then baseDamage / 2  -- 50% chance on average
  else baseDamage

-- ============================================================
--  Theorems: Roxanne Combos
-- ============================================================

theorem roxanne_playable_at_3_prizes :
    roxannePlayable { opponentPrizeCards := 3, activeConditions := noConditions } = true := by
  native_decide

theorem roxanne_playable_at_1_prize :
    roxannePlayable { opponentPrizeCards := 1, activeConditions := noConditions } = true := by
  native_decide

theorem roxanne_not_playable_at_4_prizes :
    roxannePlayable { opponentPrizeCards := 4, activeConditions := noConditions } = false := by
  native_decide

theorem roxanne_not_playable_at_6_prizes :
    roxannePlayable { opponentPrizeCards := 6, activeConditions := noConditions } = false := by
  native_decide

theorem roxanne_plus_paralysis_high_value :
    roxanneConditionValue
      { opponentPrizeCards := 2,
        activeConditions := { noConditions with isParalyzed := true } } = 80 := by
  native_decide

theorem roxanne_plus_sleep_high_value :
    roxanneConditionValue
      { opponentPrizeCards := 2,
        activeConditions := { noConditions with isSleeping := true } } = 80 := by
  native_decide

theorem roxanne_plus_poison_burn_extra_damage :
    roxanneConditionValue
      { opponentPrizeCards := 3,
        activeConditions := { noConditions with isPoisoned := true, isBurned := true } } = 80 := by
  native_decide

theorem roxanne_no_conditions_base_value :
    roxanneConditionValue
      { opponentPrizeCards := 2, activeConditions := noConditions } = 50 := by
  native_decide

-- ============================================================
--  Theorems: Condition Pressure
-- ============================================================

theorem no_conditions_zero_pressure :
    conditionPressure noConditions = 0 := by
  native_decide

theorem paralysis_lock_pressure :
    conditionPressure { noConditions with isParalyzed := true } = 40 := by
  native_decide

theorem sleep_lock_pressure :
    conditionPressure { noConditions with isSleeping := true } = 40 := by
  native_decide

theorem confusion_pressure_value :
    conditionPressure { noConditions with isConfused := true } = 20 := by
  native_decide

theorem poison_pressure_value :
    conditionPressure { noConditions with isPoisoned := true } = 10 := by
  native_decide

theorem burn_pressure_value :
    conditionPressure { noConditions with isBurned := true } = 20 := by
  native_decide

theorem max_pressure_conditions_value :
    conditionPressure maxPressureConditions = 70 := by
  native_decide

theorem aggressive_conditions_value :
    conditionPressure aggressiveConditions = 50 := by
  native_decide

-- ============================================================
--  Theorems: Max Pressure Combo Properties
-- ============================================================

theorem max_pressure_has_poison :
    maxPressureConditions.isPoisoned = true := by rfl

theorem max_pressure_has_burn :
    maxPressureConditions.isBurned = true := by rfl

theorem max_pressure_has_paralysis :
    maxPressureConditions.isParalyzed = true := by rfl

theorem max_pressure_no_confusion :
    maxPressureConditions.isConfused = false := by rfl

theorem max_pressure_no_sleep :
    maxPressureConditions.isSleeping = false := by rfl

theorem max_pressure_cant_attack :
    canAttack maxPressureConditions = false := by rfl

theorem max_pressure_cant_retreat :
    canRetreat maxPressureConditions = false := by rfl

theorem max_pressure_30_between_turns :
    betweenTurnsDamage maxPressureConditions = 30 := by rfl

-- ============================================================
--  Theorems: Aggressive Combo Properties
-- ============================================================

theorem aggressive_has_poison :
    aggressiveConditions.isPoisoned = true := by rfl

theorem aggressive_has_burn :
    aggressiveConditions.isBurned = true := by rfl

theorem aggressive_has_confusion :
    aggressiveConditions.isConfused = true := by rfl

theorem aggressive_can_attack_but_risky :
    canAttack aggressiveConditions = true := by rfl

-- ============================================================
--  Theorems: Turns to KO
-- ============================================================

theorem poison_kos_100hp_in_10_turns :
    turnsToConditionKO 100 { noConditions with isPoisoned := true } = 10 := by
  native_decide

theorem burn_kos_100hp_in_5_turns :
    turnsToConditionKO 100 { noConditions with isBurned := true } = 5 := by
  native_decide

theorem poison_burn_kos_100hp_in_4_turns :
    turnsToConditionKO 100 { noConditions with isPoisoned := true, isBurned := true } = 4 := by
  native_decide

theorem no_damage_conditions_no_ko :
    turnsToConditionKO 200 { noConditions with isSleeping := true } = 0 := by
  native_decide

theorem poison_burn_kos_60hp_in_2_turns :
    turnsToConditionKO 60 { noConditions with isPoisoned := true, isBurned := true } = 2 := by
  native_decide

-- ============================================================
--  Theorems: Switch Strategy
-- ============================================================

theorem should_switch_when_paralyzed :
    shouldSwitch
      { pokemon := { name := "Pikachu", hp := 60, currentHp := 60, energyType := EnergyType.lightning,
                      cardType := CardType.basic, retreatCost := 1 },
        conditions := { noConditions with isParalyzed := true } }
      true = true := by
  native_decide

theorem no_switch_without_bench :
    shouldSwitch
      { pokemon := { name := "Pikachu", hp := 60, currentHp := 60, energyType := EnergyType.lightning,
                      cardType := CardType.basic, retreatCost := 1 },
        conditions := { noConditions with isParalyzed := true } }
      false = false := by
  native_decide

theorem should_switch_dying_to_poison_burn :
    shouldSwitch
      { pokemon := { name := "Ralts", hp := 60, currentHp := 30, energyType := EnergyType.psychic,
                      cardType := CardType.basic, retreatCost := 1 },
        conditions := { noConditions with isPoisoned := true, isBurned := true } }
      true = true := by
  native_decide

-- ============================================================
--  Theorems: Condition Stall Strategy
-- ============================================================

theorem stall_viable_paralysis_poison :
    conditionStallViable { noConditions with isParalyzed := true, isPoisoned := true } = true := by
  native_decide

theorem stall_viable_sleep_burn :
    conditionStallViable { noConditions with isSleeping := true, isBurned := true } = true := by
  native_decide

theorem stall_not_viable_confusion_only :
    conditionStallViable { noConditions with isConfused := true } = false := by
  native_decide

theorem stall_not_viable_no_conditions :
    conditionStallViable noConditions = false := by
  native_decide

theorem stall_not_viable_poison_only :
    conditionStallViable { noConditions with isPoisoned := true } = false := by
  native_decide

-- ============================================================
--  Theorems: Confusion Effective Damage
-- ============================================================

theorem confusion_halves_damage :
    effectiveConfusionDamage 120 true = 60 := by rfl

theorem no_confusion_full_damage :
    effectiveConfusionDamage 120 false = 120 := by rfl

theorem confusion_halves_30 :
    effectiveConfusionDamage 30 true = 15 := by rfl
