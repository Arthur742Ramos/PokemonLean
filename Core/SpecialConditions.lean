/-
  Core/SpecialConditions.lean — Pokemon TCG Special Conditions
  Poison, Burn, Sleep, Paralysis, Confusion, stacking rules, between-turns effects
-/
import Core.Types

-- ============================================================
--  Special Condition Definitions
-- ============================================================

/-- The five special conditions in Pokemon TCG -/
inductive SpecialCondition where
  | poison      -- 1 damage counter (10 HP) between turns
  | burn        -- 2 damage counters (20 HP) between turns + coin flip to cure
  | sleep       -- coin flip between turns to wake up
  | paralysis   -- can't attack or retreat, auto-cures after 1 turn
  | confusion   -- coin flip to attack; fail = 30 damage to self
  deriving Repr, BEq, DecidableEq

/-- Coin flip result -/
inductive CoinFlip where
  | heads
  | tails
  deriving Repr, BEq, DecidableEq

/-- The group a special condition belongs to:
    Persistent = Poison/Burn (stack with each other and with non-persistent)
    NonPersistent = Sleep/Paralysis/Confusion (replace each other) -/
inductive ConditionGroup where
  | persistent
  | nonPersistent
  deriving Repr, BEq, DecidableEq

/-- Classify a special condition into its group -/
def conditionGroup (sc : SpecialCondition) : ConditionGroup :=
  match sc with
  | SpecialCondition.poison    => ConditionGroup.persistent
  | SpecialCondition.burn      => ConditionGroup.persistent
  | SpecialCondition.sleep     => ConditionGroup.nonPersistent
  | SpecialCondition.paralysis => ConditionGroup.nonPersistent
  | SpecialCondition.confusion => ConditionGroup.nonPersistent

/-- A Pokemon's full condition state -/
structure ConditionState where
  isPoisoned   : Bool := false
  isBurned     : Bool := false
  isSleeping   : Bool := false
  isParalyzed  : Bool := false
  isConfused   : Bool := false
  paralyzeTurns : Nat := 0   -- turns remaining for paralysis
  deriving Repr, BEq

/-- A Pokemon in play with its conditions -/
structure ActivePokemon where
  pokemon   : Pokemon
  conditions : ConditionState
  deriving Repr

/-- No conditions at all -/
def noConditions : ConditionState :=
  { isPoisoned := false, isBurned := false, isSleeping := false,
    isParalyzed := false, isConfused := false, paralyzeTurns := 0 }

/-- Fresh active Pokemon with no conditions -/
def freshActive (p : Pokemon) : ActivePokemon :=
  { pokemon := p, conditions := noConditions }

-- ============================================================
--  Condition Application (with stacking rules)
-- ============================================================

/-- Clear all non-persistent conditions -/
def clearNonPersistent (cs : ConditionState) : ConditionState :=
  { cs with isSleeping := false, isParalyzed := false, isConfused := false, paralyzeTurns := 0 }

/-- Apply a special condition following TCG stacking rules:
    - Poison/Burn: simply set the flag (they stack with everything)
    - Sleep/Paralysis/Confusion: replaces any existing non-persistent condition -/
def applyCondition (cs : ConditionState) (sc : SpecialCondition) : ConditionState :=
  match sc with
  | SpecialCondition.poison    => { cs with isPoisoned := true }
  | SpecialCondition.burn      => { cs with isBurned := true }
  | SpecialCondition.sleep     =>
    { (clearNonPersistent cs) with isSleeping := true }
  | SpecialCondition.paralysis =>
    { (clearNonPersistent cs) with isParalyzed := true, paralyzeTurns := 1 }
  | SpecialCondition.confusion =>
    { (clearNonPersistent cs) with isConfused := true }

/-- Poison damage per between-turns check (1 damage counter = 10 HP) -/
def poisonDamage : Nat := 10

/-- Burn damage per between-turns check (2 damage counters = 20 HP) -/
def burnDamage : Nat := 20

/-- Confusion self-damage on failed attack (3 damage counters = 30 HP) -/
def confusionSelfDamage : Nat := 30

-- ============================================================
--  Between-Turns Processing
-- ============================================================

/-- Apply poison damage between turns -/
def applyPoisonBetweenTurns (ap : ActivePokemon) : ActivePokemon :=
  if ap.conditions.isPoisoned then
    { ap with pokemon := applyDamage ap.pokemon poisonDamage }
  else ap

/-- Apply burn damage between turns (damage always applied; flip determines cure) -/
def applyBurnDamage (ap : ActivePokemon) : ActivePokemon :=
  if ap.conditions.isBurned then
    { ap with pokemon := applyDamage ap.pokemon burnDamage }
  else ap

/-- Attempt to cure burn with coin flip -/
def burnCureCheck (ap : ActivePokemon) (flip : CoinFlip) : ActivePokemon :=
  if ap.conditions.isBurned then
    match flip with
    | CoinFlip.heads => { ap with conditions := { ap.conditions with isBurned := false } }
    | CoinFlip.tails => ap
  else ap

/-- Full burn between-turns: damage then flip -/
def applyBurnBetweenTurns (ap : ActivePokemon) (flip : CoinFlip) : ActivePokemon :=
  burnCureCheck (applyBurnDamage ap) flip

/-- Sleep wake-up check between turns -/
def sleepWakeCheck (ap : ActivePokemon) (flip : CoinFlip) : ActivePokemon :=
  if ap.conditions.isSleeping then
    match flip with
    | CoinFlip.heads => { ap with conditions := { ap.conditions with isSleeping := false } }
    | CoinFlip.tails => ap
  else ap

/-- Paralysis auto-cure after 1 turn -/
def paralysisTickDown (ap : ActivePokemon) : ActivePokemon :=
  if ap.conditions.isParalyzed then
    if ap.conditions.paralyzeTurns ≤ 1 then
      { ap with conditions := { ap.conditions with isParalyzed := false, paralyzeTurns := 0 } }
    else
      { ap with conditions := { ap.conditions with paralyzeTurns := ap.conditions.paralyzeTurns - 1 } }
  else ap

/-- Confusion attack check: heads = attack normally, tails = self-damage -/
def confusionAttackCheck (ap : ActivePokemon) (flip : CoinFlip) : ActivePokemon :=
  if ap.conditions.isConfused then
    match flip with
    | CoinFlip.tails => { ap with pokemon := applyDamage ap.pokemon confusionSelfDamage }
    | CoinFlip.heads => ap
  else ap

/-- Can this Pokemon attack? (Paralysis and Sleep prevent attacking) -/
def canAttack (cs : ConditionState) : Bool :=
  !cs.isParalyzed && !cs.isSleeping

/-- Can this Pokemon retreat? (Paralysis and Sleep prevent retreating) -/
def canRetreat (cs : ConditionState) : Bool :=
  !cs.isParalyzed && !cs.isSleeping

/-- Check if Pokemon has any condition at all -/
def hasAnyCondition (cs : ConditionState) : Bool :=
  cs.isPoisoned || cs.isBurned || cs.isSleeping || cs.isParalyzed || cs.isConfused

/-- Count total conditions -/
def conditionCount (cs : ConditionState) : Nat :=
  (if cs.isPoisoned then 1 else 0) +
  (if cs.isBurned then 1 else 0) +
  (if cs.isSleeping then 1 else 0) +
  (if cs.isParalyzed then 1 else 0) +
  (if cs.isConfused then 1 else 0)

/-- Total between-turns damage from conditions -/
def betweenTurnsDamage (cs : ConditionState) : Nat :=
  (if cs.isPoisoned then poisonDamage else 0) +
  (if cs.isBurned then burnDamage else 0)

/-- Full between-turns processing for all conditions -/
def processBetweenTurns (ap : ActivePokemon) (burnFlip sleepFlip : CoinFlip) : ActivePokemon :=
  let step1 := applyPoisonBetweenTurns ap
  let step2 := applyBurnBetweenTurns step1 burnFlip
  let step3 := sleepWakeCheck step2 sleepFlip
  let step4 := paralysisTickDown step3
  step4

-- ============================================================
--  Theorems: Condition Classification
-- ============================================================

theorem poison_is_persistent : conditionGroup SpecialCondition.poison = ConditionGroup.persistent := by
  rfl

theorem burn_is_persistent : conditionGroup SpecialCondition.burn = ConditionGroup.persistent := by
  rfl

theorem sleep_is_nonpersistent : conditionGroup SpecialCondition.sleep = ConditionGroup.nonPersistent := by
  rfl

theorem paralysis_is_nonpersistent : conditionGroup SpecialCondition.paralysis = ConditionGroup.nonPersistent := by
  rfl

theorem confusion_is_nonpersistent : conditionGroup SpecialCondition.confusion = ConditionGroup.nonPersistent := by
  rfl

-- ============================================================
--  Theorems: No-Conditions Baseline
-- ============================================================

theorem noConditions_no_poison : noConditions.isPoisoned = false := by rfl

theorem noConditions_no_burn : noConditions.isBurned = false := by rfl

theorem noConditions_no_sleep : noConditions.isSleeping = false := by rfl

theorem noConditions_no_paralysis : noConditions.isParalyzed = false := by rfl

theorem noConditions_no_confusion : noConditions.isConfused = false := by rfl

theorem noConditions_can_attack : canAttack noConditions = true := by rfl

theorem noConditions_can_retreat : canRetreat noConditions = true := by rfl

theorem noConditions_has_none : hasAnyCondition noConditions = false := by rfl

theorem noConditions_count_zero : conditionCount noConditions = 0 := by rfl

theorem noConditions_zero_between_turns_damage : betweenTurnsDamage noConditions = 0 := by rfl

-- ============================================================
--  Theorems: Poison Mechanics
-- ============================================================

theorem poison_damage_is_ten : poisonDamage = 10 := by rfl

theorem apply_poison_sets_flag :
    (applyCondition noConditions SpecialCondition.poison).isPoisoned = true := by rfl

theorem poison_preserves_burn (cs : ConditionState) :
    (applyCondition cs SpecialCondition.poison).isBurned = cs.isBurned := by
  simp [applyCondition]

theorem poison_preserves_sleep (cs : ConditionState) :
    (applyCondition cs SpecialCondition.poison).isSleeping = cs.isSleeping := by
  simp [applyCondition]

theorem poison_preserves_paralysis (cs : ConditionState) :
    (applyCondition cs SpecialCondition.poison).isParalyzed = cs.isParalyzed := by
  simp [applyCondition]

theorem poison_preserves_confusion (cs : ConditionState) :
    (applyCondition cs SpecialCondition.poison).isConfused = cs.isConfused := by
  simp [applyCondition]

theorem poison_between_turns_deals_10 (ap : ActivePokemon) (h : ap.conditions.isPoisoned = true) :
    (applyPoisonBetweenTurns ap).pokemon = applyDamage ap.pokemon poisonDamage := by
  simp [applyPoisonBetweenTurns, h]

theorem no_poison_no_between_turns_damage (ap : ActivePokemon) (h : ap.conditions.isPoisoned = false) :
    (applyPoisonBetweenTurns ap).pokemon = ap.pokemon := by
  simp [applyPoisonBetweenTurns, h]

-- ============================================================
--  Theorems: Burn Mechanics
-- ============================================================

theorem burn_damage_is_twenty : burnDamage = 20 := by rfl

theorem apply_burn_sets_flag :
    (applyCondition noConditions SpecialCondition.burn).isBurned = true := by rfl

theorem burn_preserves_poison (cs : ConditionState) :
    (applyCondition cs SpecialCondition.burn).isPoisoned = cs.isPoisoned := by
  simp [applyCondition]

theorem burn_preserves_sleep (cs : ConditionState) :
    (applyCondition cs SpecialCondition.burn).isSleeping = cs.isSleeping := by
  simp [applyCondition]

theorem burn_heads_cures (ap : ActivePokemon) (h : ap.conditions.isBurned = true) :
    (burnCureCheck ap CoinFlip.heads).conditions.isBurned = false := by
  simp [burnCureCheck, h]

theorem burn_tails_stays (ap : ActivePokemon) (h : ap.conditions.isBurned = true) :
    (burnCureCheck ap CoinFlip.tails).conditions.isBurned = true := by
  simp [burnCureCheck, h]

-- ============================================================
--  Theorems: Sleep Mechanics
-- ============================================================

theorem apply_sleep_sets_flag :
    (applyCondition noConditions SpecialCondition.sleep).isSleeping = true := by rfl

theorem sleep_prevents_attack :
    canAttack { noConditions with isSleeping := true } = false := by rfl

theorem sleep_prevents_retreat :
    canRetreat { noConditions with isSleeping := true } = false := by rfl

theorem sleep_heads_wakes (ap : ActivePokemon) (h : ap.conditions.isSleeping = true) :
    (sleepWakeCheck ap CoinFlip.heads).conditions.isSleeping = false := by
  simp [sleepWakeCheck, h]

theorem sleep_tails_stays_asleep (ap : ActivePokemon) (h : ap.conditions.isSleeping = true) :
    (sleepWakeCheck ap CoinFlip.tails).conditions.isSleeping = true := by
  simp [sleepWakeCheck, h]

-- ============================================================
--  Theorems: Paralysis Mechanics
-- ============================================================

theorem apply_paralysis_sets_flag :
    (applyCondition noConditions SpecialCondition.paralysis).isParalyzed = true := by rfl

theorem apply_paralysis_sets_one_turn :
    (applyCondition noConditions SpecialCondition.paralysis).paralyzeTurns = 1 := by rfl

theorem paralysis_prevents_attack :
    canAttack { noConditions with isParalyzed := true } = false := by rfl

theorem paralysis_prevents_retreat :
    canRetreat { noConditions with isParalyzed := true } = false := by rfl

theorem paralysis_auto_cures_after_one_turn (ap : ActivePokemon)
    (h1 : ap.conditions.isParalyzed = true) (h2 : ap.conditions.paralyzeTurns ≤ 1) :
    (paralysisTickDown ap).conditions.isParalyzed = false := by
  simp [paralysisTickDown, h1, h2]

-- ============================================================
--  Theorems: Confusion Mechanics
-- ============================================================

theorem confusion_self_damage_is_thirty : confusionSelfDamage = 30 := by rfl

theorem apply_confusion_sets_flag :
    (applyCondition noConditions SpecialCondition.confusion).isConfused = true := by rfl

theorem confusion_heads_no_self_damage (ap : ActivePokemon) (h : ap.conditions.isConfused = true) :
    (confusionAttackCheck ap CoinFlip.heads).pokemon = ap.pokemon := by
  simp [confusionAttackCheck, h]

theorem confusion_tails_self_damage (ap : ActivePokemon) (h : ap.conditions.isConfused = true) :
    (confusionAttackCheck ap CoinFlip.tails).pokemon = applyDamage ap.pokemon confusionSelfDamage := by
  simp [confusionAttackCheck, h]

theorem confusion_allows_attack :
    canAttack { noConditions with isConfused := true } = true := by rfl

theorem confusion_allows_retreat :
    canRetreat { noConditions with isConfused := true } = true := by rfl

-- ============================================================
--  Theorems: Stacking Rules
-- ============================================================

/-- Poison and Burn can coexist -/
theorem poison_burn_stack :
    let cs := applyCondition (applyCondition noConditions SpecialCondition.poison) SpecialCondition.burn
    cs.isPoisoned = true ∧ cs.isBurned = true := by
  constructor <;> rfl

/-- Poison + Burn = 30 damage between turns -/
theorem poison_burn_combined_damage :
    betweenTurnsDamage { noConditions with isPoisoned := true, isBurned := true } = 30 := by rfl

/-- Sleep replaces Paralysis -/
theorem sleep_replaces_paralysis :
    let cs := applyCondition { noConditions with isParalyzed := true, paralyzeTurns := 1 } SpecialCondition.sleep
    cs.isSleeping = true ∧ cs.isParalyzed = false := by
  constructor <;> rfl

/-- Paralysis replaces Sleep -/
theorem paralysis_replaces_sleep :
    let cs := applyCondition { noConditions with isSleeping := true } SpecialCondition.paralysis
    cs.isParalyzed = true ∧ cs.isSleeping = false := by
  constructor <;> rfl

/-- Confusion replaces Sleep -/
theorem confusion_replaces_sleep :
    let cs := applyCondition { noConditions with isSleeping := true } SpecialCondition.confusion
    cs.isConfused = true ∧ cs.isSleeping = false := by
  constructor <;> rfl

/-- Confusion replaces Paralysis -/
theorem confusion_replaces_paralysis :
    let cs := applyCondition { noConditions with isParalyzed := true } SpecialCondition.confusion
    cs.isConfused = true ∧ cs.isParalyzed = false := by
  constructor <;> rfl

/-- Sleep replaces Confusion -/
theorem sleep_replaces_confusion :
    let cs := applyCondition { noConditions with isConfused := true } SpecialCondition.sleep
    cs.isSleeping = true ∧ cs.isConfused = false := by
  constructor <;> rfl

/-- Paralysis replaces Confusion -/
theorem paralysis_replaces_confusion :
    let cs := applyCondition { noConditions with isConfused := true } SpecialCondition.paralysis
    cs.isParalyzed = true ∧ cs.isConfused = false := by
  constructor <;> rfl

/-- Poison stacks with Sleep -/
theorem poison_stacks_with_sleep :
    let cs := applyCondition (applyCondition noConditions SpecialCondition.poison) SpecialCondition.sleep
    cs.isPoisoned = true ∧ cs.isSleeping = true := by
  constructor <;> rfl

/-- Burn stacks with Confusion -/
theorem burn_stacks_with_confusion :
    let cs := applyCondition (applyCondition noConditions SpecialCondition.burn) SpecialCondition.confusion
    cs.isBurned = true ∧ cs.isConfused = true := by
  constructor <;> rfl

/-- Poison + Burn + Confusion all coexist (max persistent + one non-persistent) -/
theorem triple_condition_stack :
    let cs := applyCondition (applyCondition (applyCondition noConditions SpecialCondition.poison)
              SpecialCondition.burn) SpecialCondition.confusion
    cs.isPoisoned = true ∧ cs.isBurned = true ∧ cs.isConfused = true := by
  exact ⟨rfl, rfl, rfl⟩

/-- At most one non-persistent condition after any apply -/
theorem nonpersistent_mutual_exclusion_sleep_para :
    let cs := applyCondition noConditions SpecialCondition.sleep
    let cs2 := applyCondition cs SpecialCondition.paralysis
    cs2.isSleeping = false := by rfl

-- ============================================================
--  Theorems: Between-Turns Processing
-- ============================================================

theorem between_turns_no_conditions_no_change (p : Pokemon) (f1 f2 : CoinFlip) :
    (processBetweenTurns (freshActive p) f1 f2).pokemon = p := by
  simp [processBetweenTurns, freshActive, noConditions,
        applyPoisonBetweenTurns, applyBurnBetweenTurns, applyBurnDamage,
        burnCureCheck, sleepWakeCheck, paralysisTickDown]

theorem between_turns_poison_only_deals_10 (p : Pokemon) (f1 f2 : CoinFlip) :
    let ap : ActivePokemon := { pokemon := p, conditions := { noConditions with isPoisoned := true } }
    (processBetweenTurns ap f1 f2).pokemon = applyDamage p poisonDamage := by
  simp [processBetweenTurns, applyPoisonBetweenTurns, applyBurnBetweenTurns,
        applyBurnDamage, burnCureCheck, sleepWakeCheck, paralysisTickDown, noConditions]

theorem between_turns_burn_only_deals_20 (p : Pokemon) :
    let ap : ActivePokemon := { pokemon := p, conditions := { noConditions with isBurned := true } }
    (processBetweenTurns ap CoinFlip.tails CoinFlip.tails).pokemon = applyDamage p burnDamage := by
  simp [processBetweenTurns, applyPoisonBetweenTurns, applyBurnBetweenTurns,
        applyBurnDamage, burnCureCheck, sleepWakeCheck, paralysisTickDown, noConditions]
