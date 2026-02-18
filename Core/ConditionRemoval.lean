/-
  Core/ConditionRemoval.lean — Pokemon TCG Condition Removal Mechanics
  Evolving, retreating, Switch trainer, and related removal rules
-/
import Core.Types
import Core.SpecialConditions

-- ============================================================
--  Condition Removal Methods
-- ============================================================

/-- Remove ALL special conditions (evolving, Switch, certain abilities) -/
def removeAllConditions (ap : ActivePokemon) : ActivePokemon :=
  { ap with conditions := noConditions }

/-- Retreat: removes all conditions from the retreating Pokemon -/
def retreatActive (active : ActivePokemon) (benchMon : Pokemon) (energyCost : Nat)
    (_h : canRetreat active.conditions = true)
    (_hEnergy : energyCost ≥ active.pokemon.retreatCost) : ActivePokemon × Pokemon :=
  -- The retreating Pokemon loses all conditions and goes to bench
  -- The bench Pokemon becomes active with no conditions
  let cleanedRetreat := { active with conditions := noConditions }
  (freshActive benchMon, cleanedRetreat.pokemon)

/-- Switch trainer card: swap active with bench, remove all conditions -/
def switchTrainer (active : ActivePokemon) (benchMon : Pokemon) : ActivePokemon × Pokemon :=
  (freshActive benchMon, active.pokemon)  -- Switch ignores retreat cost and conditions

/-- Evolving a Pokemon removes all conditions -/
def evolve (ap : ActivePokemon) (evolvedName : String) (newHp : Nat) : ActivePokemon :=
  let newPokemon : Pokemon := { ap.pokemon with
    name := evolvedName
    hp := newHp
    currentHp := ap.pokemon.currentHp + (newHp - ap.pokemon.hp)  -- preserve damage
    isEvolved := true
  }
  { pokemon := newPokemon, conditions := noConditions }

/-- Full Heal trainer card: remove all conditions -/
def fullHeal (ap : ActivePokemon) : ActivePokemon :=
  removeAllConditions ap

/-- Poke Flute: wake up a sleeping Pokemon specifically -/
def pokeFlute (ap : ActivePokemon) : ActivePokemon :=
  { ap with conditions := { ap.conditions with isSleeping := false } }

/-- Specific condition removal: remove just poison -/
def curePoison (ap : ActivePokemon) : ActivePokemon :=
  { ap with conditions := { ap.conditions with isPoisoned := false } }

/-- Specific condition removal: remove just burn -/
def cureBurn (ap : ActivePokemon) : ActivePokemon :=
  { ap with conditions := { ap.conditions with isBurned := false } }

/-- Check if a Pokemon needs condition removal urgently
    (taking 30+ between turns damage, or can't act at all) -/
def needsUrgentRemoval (cs : ConditionState) : Bool :=
  betweenTurnsDamage cs ≥ 30 || (!canAttack cs)

/-- Escape Rope: both players switch, removing conditions from the user's active -/
def useEscapeRope (myActive : ActivePokemon) (myBenchMon : Pokemon)
    (oppActive : ActivePokemon) (oppBenchMon : Pokemon) :
    (ActivePokemon × Pokemon) × (ActivePokemon × Pokemon) :=
  let myResult := switchTrainer myActive myBenchMon
  let oppResult := switchTrainer oppActive oppBenchMon
  (myResult, oppResult)

-- ============================================================
--  Theorems: Removal via Evolution
-- ============================================================

theorem evolve_clears_all_conditions (ap : ActivePokemon) (name : String) (hp : Nat) :
    (evolve ap name hp).conditions = noConditions := by
  simp [evolve]

theorem evolve_clears_poison (ap : ActivePokemon) (name : String) (hp : Nat)
    (_h : ap.conditions.isPoisoned = true) :
    (evolve ap name hp).conditions.isPoisoned = false := by
  simp [evolve, noConditions]

theorem evolve_clears_burn (ap : ActivePokemon) (name : String) (hp : Nat)
    (_h : ap.conditions.isBurned = true) :
    (evolve ap name hp).conditions.isBurned = false := by
  simp [evolve, noConditions]

theorem evolve_clears_sleep (ap : ActivePokemon) (name : String) (hp : Nat)
    (_h : ap.conditions.isSleeping = true) :
    (evolve ap name hp).conditions.isSleeping = false := by
  simp [evolve, noConditions]

theorem evolve_clears_paralysis (ap : ActivePokemon) (name : String) (hp : Nat)
    (_h : ap.conditions.isParalyzed = true) :
    (evolve ap name hp).conditions.isParalyzed = false := by
  simp [evolve, noConditions]

theorem evolve_clears_confusion (ap : ActivePokemon) (name : String) (hp : Nat)
    (_h : ap.conditions.isConfused = true) :
    (evolve ap name hp).conditions.isConfused = false := by
  simp [evolve, noConditions]

theorem evolve_sets_evolved_flag (ap : ActivePokemon) (name : String) (hp : Nat) :
    (evolve ap name hp).pokemon.isEvolved = true := by
  simp [evolve]

-- ============================================================
--  Theorems: Removal via Switch Trainer
-- ============================================================

theorem switch_new_active_has_no_conditions (active : ActivePokemon) (benchMon : Pokemon) :
    (switchTrainer active benchMon).1.conditions = noConditions := by
  simp [switchTrainer, freshActive]

theorem switch_clears_poison (active : ActivePokemon) (benchMon : Pokemon)
    (_h : active.conditions.isPoisoned = true) :
    (switchTrainer active benchMon).1.conditions.isPoisoned = false := by
  simp [switchTrainer, freshActive, noConditions]

theorem switch_clears_paralysis (active : ActivePokemon) (benchMon : Pokemon)
    (_h : active.conditions.isParalyzed = true) :
    (switchTrainer active benchMon).1.conditions.isParalyzed = false := by
  simp [switchTrainer, freshActive, noConditions]

theorem switch_bypasses_paralysis_lock (active : ActivePokemon) (benchMon : Pokemon)
    (_h : active.conditions.isParalyzed = true) :
    canAttack (switchTrainer active benchMon).1.conditions = true := by
  simp [switchTrainer, freshActive, noConditions, canAttack]

theorem switch_bypasses_sleep_lock (active : ActivePokemon) (benchMon : Pokemon)
    (_h : active.conditions.isSleeping = true) :
    canAttack (switchTrainer active benchMon).1.conditions = true := by
  simp [switchTrainer, freshActive, noConditions, canAttack]

-- ============================================================
--  Theorems: Full Heal
-- ============================================================

theorem full_heal_clears_all (ap : ActivePokemon) :
    (fullHeal ap).conditions = noConditions := by
  simp [fullHeal, removeAllConditions]

theorem full_heal_can_attack (ap : ActivePokemon) :
    canAttack (fullHeal ap).conditions = true := by
  simp [fullHeal, removeAllConditions, noConditions, canAttack]

theorem full_heal_can_retreat (ap : ActivePokemon) :
    canRetreat (fullHeal ap).conditions = true := by
  simp [fullHeal, removeAllConditions, noConditions, canRetreat]

theorem full_heal_preserves_hp (ap : ActivePokemon) :
    (fullHeal ap).pokemon.currentHp = ap.pokemon.currentHp := by
  simp [fullHeal, removeAllConditions]

theorem full_heal_no_between_turns_damage (ap : ActivePokemon) :
    betweenTurnsDamage (fullHeal ap).conditions = 0 := by
  simp [fullHeal, removeAllConditions, noConditions, betweenTurnsDamage]

-- ============================================================
--  Theorems: Specific Cures
-- ============================================================

theorem cure_poison_clears_only_poison (ap : ActivePokemon) :
    (curePoison ap).conditions.isPoisoned = false ∧
    (curePoison ap).conditions.isBurned = ap.conditions.isBurned ∧
    (curePoison ap).conditions.isSleeping = ap.conditions.isSleeping := by
  simp [curePoison]

theorem cure_burn_clears_only_burn (ap : ActivePokemon) :
    (cureBurn ap).conditions.isBurned = false ∧
    (cureBurn ap).conditions.isPoisoned = ap.conditions.isPoisoned ∧
    (cureBurn ap).conditions.isSleeping = ap.conditions.isSleeping := by
  simp [cureBurn]

theorem poke_flute_wakes (ap : ActivePokemon) :
    (pokeFlute ap).conditions.isSleeping = false := by
  simp [pokeFlute]

theorem poke_flute_preserves_poison (ap : ActivePokemon) :
    (pokeFlute ap).conditions.isPoisoned = ap.conditions.isPoisoned := by
  simp [pokeFlute]

-- ============================================================
--  Theorems: Urgent Removal Logic
-- ============================================================

theorem poison_burn_needs_urgent_removal :
    needsUrgentRemoval { noConditions with isPoisoned := true, isBurned := true } = true := by
  native_decide

theorem paralysis_needs_urgent_removal :
    needsUrgentRemoval { noConditions with isParalyzed := true } = true := by
  native_decide

theorem sleep_needs_urgent_removal :
    needsUrgentRemoval { noConditions with isSleeping := true } = true := by
  native_decide

theorem no_conditions_no_urgent_removal :
    needsUrgentRemoval noConditions = false := by
  native_decide

theorem poison_alone_not_urgent :
    needsUrgentRemoval { noConditions with isPoisoned := true } = false := by
  native_decide

theorem burn_alone_not_urgent :
    needsUrgentRemoval { noConditions with isBurned := true } = false := by
  native_decide

theorem confusion_alone_not_urgent :
    needsUrgentRemoval { noConditions with isConfused := true } = false := by
  native_decide

-- ============================================================
--  Theorems: Escape Rope Mechanics
-- ============================================================

theorem escape_rope_clears_my_conditions (myAP : ActivePokemon) (myBench : Pokemon)
    (oppAP : ActivePokemon) (oppBench : Pokemon) :
    (useEscapeRope myAP myBench oppAP oppBench).1.1.conditions = noConditions := by
  simp [useEscapeRope, switchTrainer, freshActive]

theorem escape_rope_clears_opp_conditions (myAP : ActivePokemon) (myBench : Pokemon)
    (oppAP : ActivePokemon) (oppBench : Pokemon) :
    (useEscapeRope myAP myBench oppAP oppBench).2.1.conditions = noConditions := by
  simp [useEscapeRope, switchTrainer, freshActive]
