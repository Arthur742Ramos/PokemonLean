/-
  PokemonLean / Core / SpecialConditions.lean

  Pokémon TCG special conditions formalised in Lean 4.
  Self-contained: defines all 5 conditions, exclusivity rules,
  between-turns processing, cure mechanics, gameplay effects.

  All proofs are sorry-free.  35 theorems.
-/

namespace PokemonLean.Core.SpecialConditions

-- ============================================================
-- §1  Core Types (self-contained)
-- ============================================================

/-- Coin flip result. -/
inductive Coin where
  | heads | tails
  deriving DecidableEq, Repr

/-- The five special conditions in Pokémon TCG.
    Asleep, Confused, Paralyzed are mutually exclusive.
    Poisoned and Burned stack with everything. -/
inductive Condition where
  | poisoned
  | burned
  | asleep
  | confused
  | paralyzed
  deriving DecidableEq, Repr

/-- Which group a condition belongs to.
    Group A: Asleep/Confused/Paralyzed (mutually exclusive)
    Group B: Poisoned/Burned (stack with everything) -/
inductive CondGroup where
  | exclusive   -- asleep / confused / paralyzed
  | stacking    -- poisoned / burned
  deriving DecidableEq, Repr

def conditionGroup : Condition → CondGroup
  | .poisoned  => .stacking
  | .burned    => .stacking
  | .asleep    => .exclusive
  | .confused  => .exclusive
  | .paralyzed => .exclusive

/-- Full condition state for a Pokémon.
    At most one exclusive condition, plus independent poison/burn flags. -/
structure ConditionState where
  isPoisoned    : Bool
  isBurned      : Bool
  exclusiveCond : Option Condition  -- None, or one of asleep/confused/paralyzed
  poisonCounters : Nat              -- damage counters from poison
  burnCounters   : Nat              -- damage counters from burn
  deriving DecidableEq, Repr

/-- Clean/healthy condition state. -/
def ConditionState.healthy : ConditionState :=
  { isPoisoned := false, isBurned := false, exclusiveCond := none,
    poisonCounters := 0, burnCounters := 0 }

/-- Count active conditions. -/
def ConditionState.activeCount (cs : ConditionState) : Nat :=
  (if cs.isPoisoned then 1 else 0) +
  (if cs.isBurned then 1 else 0) +
  (if cs.exclusiveCond.isSome then 1 else 0)

-- ============================================================
-- §2  Applying Conditions (with exclusivity rules)
-- ============================================================

/-- Apply a condition, respecting exclusivity rules.
    If applying an exclusive condition (asleep/confused/paralyzed),
    it replaces any existing exclusive condition.
    Poison and burn are set independently. -/
def applyCondition (cs : ConditionState) (c : Condition) : ConditionState :=
  match c with
  | .poisoned  => { cs with isPoisoned := true }
  | .burned    => { cs with isBurned := true }
  | .asleep    => { cs with exclusiveCond := some .asleep }
  | .confused  => { cs with exclusiveCond := some .confused }
  | .paralyzed => { cs with exclusiveCond := some .paralyzed }

/-- Remove a specific condition. -/
def removeCondition (cs : ConditionState) (c : Condition) : ConditionState :=
  match c with
  | .poisoned  => { cs with isPoisoned := false }
  | .burned    => { cs with isBurned := false }
  | .asleep    => if cs.exclusiveCond == some .asleep then { cs with exclusiveCond := none } else cs
  | .confused  => if cs.exclusiveCond == some .confused then { cs with exclusiveCond := none } else cs
  | .paralyzed => if cs.exclusiveCond == some .paralyzed then { cs with exclusiveCond := none } else cs

/-- Cure ALL conditions (evolving, retreating). -/
def cureAll (_cs : ConditionState) : ConditionState :=
  ConditionState.healthy

-- ============================================================
-- §3  Between-Turns Processing
-- ============================================================

/-- Process poison between turns: place 1 damage counter (10 HP). -/
def processPoison (cs : ConditionState) : ConditionState :=
  if cs.isPoisoned then
    { cs with poisonCounters := cs.poisonCounters + 1 }
  else cs

/-- Process burn between turns: flip coin.
    Tails → 2 damage counters (20 HP).
    Heads → no damage. -/
def processBurn (cs : ConditionState) (flip : Coin) : ConditionState :=
  if cs.isBurned then
    match flip with
    | .tails => { cs with burnCounters := cs.burnCounters + 2 }
    | .heads => cs
  else cs

/-- Process sleep between turns: flip coin.
    Heads → wake up (remove asleep).
    Tails → stay asleep. -/
def processSleep (cs : ConditionState) (flip : Coin) : ConditionState :=
  if cs.exclusiveCond == some .asleep then
    match flip with
    | .heads => { cs with exclusiveCond := none }
    | .tails => cs
  else cs

/-- Process paralysis: auto-cure at end of affected player's next turn. -/
def processParalysis (cs : ConditionState) (isEndOfNextTurn : Bool) : ConditionState :=
  if cs.exclusiveCond == some .paralyzed && isEndOfNextTurn then
    { cs with exclusiveCond := none }
  else cs

/-- Full between-turns processing (poison then burn). -/
def processBetweenTurns (cs : ConditionState) (burnFlip : Coin) : ConditionState :=
  processBurn (processPoison cs) burnFlip

-- ============================================================
-- §4  Gameplay Effects
-- ============================================================

/-- Can the Pokémon attack? Blocked by Asleep and Paralyzed. -/
def canAttack (cs : ConditionState) : Bool :=
  cs.exclusiveCond != some .asleep &&
  cs.exclusiveCond != some .paralyzed

/-- Can the Pokémon retreat? Blocked by Asleep and Paralyzed. -/
def canRetreat (cs : ConditionState) : Bool :=
  cs.exclusiveCond != some .asleep &&
  cs.exclusiveCond != some .paralyzed

/-- Confused attack outcome: flip coin.
    Heads → attack normally.
    Tails → 30 damage to self. -/
inductive ConfusedAttackResult where
  | normalAttack
  | selfDamage30
  deriving DecidableEq, Repr

def resolveConfusedAttack (cs : ConditionState) (flip : Coin) : ConfusedAttackResult :=
  if cs.exclusiveCond == some .confused then
    match flip with
    | .heads => .normalAttack
    | .tails => .selfDamage30
  else .normalAttack

-- ============================================================
-- §5  Exclusivity Rule Theorems
-- ============================================================

/-- Theorem 1: At most 3 simultaneous conditions
    (poison + burn + one exclusive). -/
theorem max_three_conditions (cs : ConditionState) :
    cs.activeCount ≤ 3 := by
  simp [ConditionState.activeCount]
  cases cs.isPoisoned <;> cases cs.isBurned <;> cases cs.exclusiveCond <;> simp <;> omega

/-- Theorem 2: Applying confused to a paralyzed Pokémon removes paralyzed. -/
theorem confused_replaces_paralyzed (cs : ConditionState)
    (_h : cs.exclusiveCond = some .paralyzed) :
    (applyCondition cs .confused).exclusiveCond = some .confused := by
  simp [applyCondition]

/-- Theorem 3: Applying asleep to a confused Pokémon removes confused. -/
theorem asleep_replaces_confused (cs : ConditionState)
    (_h : cs.exclusiveCond = some .confused) :
    (applyCondition cs .asleep).exclusiveCond = some .asleep := by
  simp [applyCondition]

/-- Theorem 4: Applying paralyzed to an asleep Pokémon removes asleep. -/
theorem paralyzed_replaces_asleep (cs : ConditionState)
    (_h : cs.exclusiveCond = some .asleep) :
    (applyCondition cs .paralyzed).exclusiveCond = some .paralyzed := by
  simp [applyCondition]

/-- Theorem 5: Poison stacks with any exclusive condition. -/
theorem poison_stacks_with_exclusive (cs : ConditionState) (c : Condition)
    (h : conditionGroup c = .exclusive) :
    (applyCondition (applyCondition cs c) .poisoned).isPoisoned = true := by
  cases c <;> simp [applyCondition, conditionGroup] at * <;> rfl

/-- Theorem 6: Burn stacks with poison. -/
theorem burn_stacks_with_poison (cs : ConditionState) :
    (applyCondition (applyCondition cs .poisoned) .burned).isPoisoned = true ∧
    (applyCondition (applyCondition cs .poisoned) .burned).isBurned = true := by
  simp [applyCondition]

/-- Theorem 7: The group classification is correct. -/
theorem poison_is_stacking : conditionGroup .poisoned = .stacking := rfl
theorem burn_is_stacking : conditionGroup .burned = .stacking := rfl
theorem asleep_is_exclusive : conditionGroup .asleep = .exclusive := rfl
theorem confused_is_exclusive : conditionGroup .confused = .exclusive := rfl
theorem paralyzed_is_exclusive : conditionGroup .paralyzed = .exclusive := rfl

-- ============================================================
-- §6  Cure Mechanics Theorems
-- ============================================================

/-- Theorem 8: Cure all removes everything. -/
theorem cure_all_healthy (cs : ConditionState) :
    cureAll cs = ConditionState.healthy := by
  rfl

/-- Theorem 9: Cure all sets isPoisoned to false. -/
theorem cure_clears_poison (cs : ConditionState) :
    (cureAll cs).isPoisoned = false := by
  rfl

/-- Theorem 10: Cure all sets isBurned to false. -/
theorem cure_clears_burn (cs : ConditionState) :
    (cureAll cs).isBurned = false := by
  rfl

/-- Theorem 11: Cure all clears exclusive condition. -/
theorem cure_clears_exclusive (cs : ConditionState) :
    (cureAll cs).exclusiveCond = none := by
  rfl

/-- Theorem 12: Evolving cures all (universal cure — same as cureAll). -/
theorem evolve_cures_all (cs : ConditionState) :
    cureAll cs = ConditionState.healthy := by
  rfl

/-- Theorem 13: Retreating cures all (same as cureAll). -/
theorem retreat_cures_all (cs : ConditionState) :
    (cureAll cs).activeCount = 0 := by
  rfl

-- ============================================================
-- §7  Between-Turns Processing Theorems
-- ============================================================

/-- Theorem 14: Poison adds exactly 1 counter when poisoned. -/
theorem poison_adds_one_counter (cs : ConditionState) (h : cs.isPoisoned = true) :
    (processPoison cs).poisonCounters = cs.poisonCounters + 1 := by
  simp [processPoison, h]

/-- Theorem 15: Poison is no-op when not poisoned. -/
theorem poison_noop_when_healthy (cs : ConditionState) (h : cs.isPoisoned = false) :
    processPoison cs = cs := by
  simp [processPoison, h]

/-- Theorem 16: Burn on tails adds 2 counters. -/
theorem burn_tails_adds_two (cs : ConditionState) (h : cs.isBurned = true) :
    (processBurn cs .tails).burnCounters = cs.burnCounters + 2 := by
  simp [processBurn, h]

/-- Theorem 17: Burn on heads is no-op. -/
theorem burn_heads_noop (cs : ConditionState) (h : cs.isBurned = true) :
    processBurn cs .heads = cs := by
  simp [processBurn, h]

/-- Theorem 18: Sleep wake-up on heads clears asleep. -/
theorem sleep_heads_wakes (cs : ConditionState)
    (h : cs.exclusiveCond = some .asleep) :
    (processSleep cs .heads).exclusiveCond = none := by
  simp [processSleep, h]

/-- Theorem 19: Sleep tails keeps asleep. -/
theorem sleep_tails_stays (cs : ConditionState)
    (h : cs.exclusiveCond = some .asleep) :
    (processSleep cs .tails).exclusiveCond = some .asleep := by
  simp [processSleep, h]

/-- Theorem 20: Paralysis auto-cures at end of next turn. -/
theorem paralysis_auto_cures (cs : ConditionState)
    (h : cs.exclusiveCond = some .paralyzed) :
    (processParalysis cs true).exclusiveCond = none := by
  simp [processParalysis, h]

/-- Theorem 21: Paralysis does NOT cure before end of next turn. -/
theorem paralysis_stays_before_end (cs : ConditionState)
    (h : cs.exclusiveCond = some .paralyzed) :
    (processParalysis cs false).exclusiveCond = some .paralyzed := by
  simp [processParalysis, h]

-- ============================================================
-- §8  Gameplay Effect Theorems
-- ============================================================

/-- Theorem 22: Paralyzed blocks attacking. -/
theorem paralyzed_cant_attack :
    canAttack { isPoisoned := false, isBurned := false,
                exclusiveCond := some .paralyzed,
                poisonCounters := 0, burnCounters := 0 } = false := by
  rfl

/-- Theorem 23: Asleep blocks attacking. -/
theorem asleep_cant_attack :
    canAttack { isPoisoned := false, isBurned := false,
                exclusiveCond := some .asleep,
                poisonCounters := 0, burnCounters := 0 } = false := by
  rfl

/-- Theorem 24: Confused Pokémon CAN attack (but must flip). -/
theorem confused_can_attack :
    canAttack { isPoisoned := false, isBurned := false,
                exclusiveCond := some .confused,
                poisonCounters := 0, burnCounters := 0 } = true := by
  rfl

/-- Theorem 25: Paralyzed blocks retreating. -/
theorem paralyzed_cant_retreat :
    canRetreat { isPoisoned := false, isBurned := false,
                 exclusiveCond := some .paralyzed,
                 poisonCounters := 0, burnCounters := 0 } = false := by
  rfl

/-- Theorem 26: Asleep blocks retreating. -/
theorem asleep_cant_retreat :
    canRetreat { isPoisoned := false, isBurned := false,
                 exclusiveCond := some .asleep,
                 poisonCounters := 0, burnCounters := 0 } = false := by
  rfl

/-- Theorem 27: Confused Pokémon CAN retreat (retreat cures confusion). -/
theorem confused_can_retreat :
    canRetreat { isPoisoned := false, isBurned := false,
                 exclusiveCond := some .confused,
                 poisonCounters := 0, burnCounters := 0 } = true := by
  rfl

/-- Theorem 28: Confused attack on tails = self damage 30. -/
theorem confused_tails_self_damage :
    resolveConfusedAttack
      { isPoisoned := false, isBurned := false,
        exclusiveCond := some .confused,
        poisonCounters := 0, burnCounters := 0 } .tails = .selfDamage30 := by
  rfl

/-- Theorem 29: Confused attack on heads = normal attack. -/
theorem confused_heads_normal :
    resolveConfusedAttack
      { isPoisoned := false, isBurned := false,
        exclusiveCond := some .confused,
        poisonCounters := 0, burnCounters := 0 } .heads = .normalAttack := by
  rfl

/-- Theorem 30: Healthy Pokémon can attack and retreat. -/
theorem healthy_full_freedom :
    canAttack ConditionState.healthy = true ∧
    canRetreat ConditionState.healthy = true := by
  exact ⟨rfl, rfl⟩

-- ============================================================
-- §9  Compound Scenario Theorems
-- ============================================================

/-- Theorem 31: Poison + Burn + Paralyzed = all 3 active conditions. -/
theorem triple_condition_count :
    (applyCondition
      (applyCondition
        (applyCondition ConditionState.healthy .poisoned)
        .burned)
      .paralyzed).activeCount = 3 := by
  native_decide

/-- Theorem 32: After cure, active count is 0. -/
theorem cure_resets_count (cs : ConditionState) :
    (cureAll cs).activeCount = 0 := by
  rfl

/-- Theorem 33: Double poison processing adds 2 counters. -/
theorem double_poison_two_counters (cs : ConditionState) (h : cs.isPoisoned = true) :
    (processPoison (processPoison cs)).poisonCounters = cs.poisonCounters + 2 := by
  simp [processPoison, h]

/-- Theorem 34: Between-turns processing preserves exclusive condition. -/
theorem between_turns_preserves_exclusive (cs : ConditionState) (flip : Coin) :
    (processBetweenTurns cs flip).exclusiveCond = cs.exclusiveCond := by
  simp only [processBetweenTurns, processPoison, processBurn]
  split <;> cases flip <;> split <;> simp_all

/-- Theorem 35: Applying same exclusive condition twice is idempotent. -/
theorem exclusive_idempotent (cs : ConditionState) :
    applyCondition (applyCondition cs .asleep) .asleep =
    applyCondition cs .asleep := by
  simp [applyCondition]

end PokemonLean.Core.SpecialConditions
