/-
  PokemonLean / Core / RulingEdgeCases.lean

  Edge cases and official rulings formalization.
  Covers abilities vs attacks, weakness/resistance application order,
  damage vs damage counters, KO timing, multiple KOs, sudden death,
  first turn rules, and bench size limits.

  Self-contained — no imports from other PokemonLean modules.
  All proofs are sorry-free.  35+ theorems.
-/

namespace PokemonLean.Core.RulingEdgeCases

-- ============================================================
-- §1  Core Types
-- ============================================================

/-- Pokémon types. -/
inductive PType where
  | fire | water | grass | electric | psychic
  | fighting | dark | steel | dragon | fairy | normal
deriving DecidableEq, Repr, BEq, Inhabited

/-- Position of a Pokémon. -/
inductive Position where
  | active
  | bench
deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================
-- §2  Abilities vs Attacks
-- ============================================================

/-- Whether an ability works from bench.
    Default: true (unless the card text says "your Active Pokémon"). -/
structure AbilityRule where
  worksFromBench : Bool := true
  requiresActive : Bool := false
deriving Repr, Inhabited

/-- Can an ability be used from a given position? -/
def abilityUsable (rule : AbilityRule) (pos : Position) : Bool :=
  match pos with
  | .active => true
  | .bench  => rule.worksFromBench && !rule.requiresActive

-- ============================================================
-- §3  Weakness / Resistance Application Order
-- ============================================================

/-- Weakness doubles FINAL damage (after all modifiers in modern TCG).
    In practice: base + modifiers, then weakness, then resistance.
    Modern TCG (SV era): weakness ×2, resistance −30.
    Apply weakness: multiply by 2. -/
def applyWeakness (dmg : Nat) (isWeak : Bool) : Nat :=
  if isWeak then dmg * 2 else dmg

/-- Apply resistance: subtract 30, floor at 0. -/
def applyResistance (dmg : Nat) (isResist : Bool) : Nat :=
  if isResist then dmg - 30 else dmg

/-- Full damage pipeline:
    1. Start with base damage
    2. Add/subtract modifiers (tools, abilities)
    3. Apply weakness (×2)
    4. Apply resistance (−30)
    Result is final damage, minimum 0. -/
def calcDamage (baseDmg : Nat) (modifier : Int) (isWeak : Bool) (isResist : Bool) : Nat :=
  let modified := if modifier ≥ 0
                  then baseDmg + modifier.toNat
                  else baseDmg - (-modifier).toNat
  let afterWeak := applyWeakness modified isWeak
  applyResistance afterWeak isResist

-- ============================================================
-- §4  Damage vs Damage Counters
-- ============================================================

/-- Damage counters are placed directly and bypass weakness/resistance.
    1 damage counter = 10 HP of damage.
    HP lost from damage counters (bypasses weakness/resistance). -/
def damageCounterHP (counters : Nat) : Nat := counters * 10

/-- Damage from an attack goes through the full pipeline. -/
def attackDamageHP (baseDmg : Nat) (modifier : Int) (isWeak : Bool) (isResist : Bool) : Nat :=
  calcDamage baseDmg modifier isWeak isResist

/-- Total HP loss from both attack damage and damage counters. -/
def totalHPLoss (attackDmg : Nat) (counters : Nat) : Nat :=
  attackDmg + damageCounterHP counters

-- ============================================================
-- §5  KO Timing
-- ============================================================

/-- When KO checks happen. -/
inductive KOTiming where
  | afterAttackResolution   -- Standard: check after attack fully resolves
  | betweenTurns            -- Poison/Burn damage KOs happen between turns
  | duringAttack            -- Some effects check mid-resolution (rare)
deriving DecidableEq, Repr, Inhabited

/-- Is a Pokémon KO'd? (HP ≤ damage taken) -/
def isKOd (maxHP : Nat) (damageTaken : Nat) : Bool :=
  damageTaken ≥ maxHP

/-- KO check: after attack resolution, check all Pokémon. -/
def koCheckAfterAttack (maxHP : Nat) (totalDmg : Nat) : Bool :=
  isKOd maxHP totalDmg

-- ============================================================
-- §6  Multiple KOs and Prize Taking
-- ============================================================

/-- When multiple Pokémon are KO'd in one attack, take all prizes simultaneously. -/
def simultaneousPrizes (koCount : List Nat) : Nat :=
  koCount.foldl (· + ·) 0

/-- A player's remaining prize count after taking prizes. -/
def remainingPrizes (current : Nat) (taken : Nat) : Nat :=
  current - taken

-- ============================================================
-- §7  Sudden Death
-- ============================================================

/-- Sudden death occurs when both players reach 0 prizes simultaneously.
    Also can occur when both players deck out, or other simultaneous
    win/loss conditions. -/
def isSuddenDeath (p1Prizes : Nat) (p2Prizes : Nat)
    (p1TakenThisTurn : Nat) (p2TakenThisTurn : Nat) : Bool :=
  let p1After := p1Prizes - p1TakenThisTurn
  let p2After := p2Prizes - p2TakenThisTurn
  p1After == 0 && p2After == 0

/-- In sudden death: each player sets up with 1 prize card. -/
def suddenDeathPrizes : Nat := 1

-- ============================================================
-- §8  First Turn Rules
-- ============================================================

/-- First turn restrictions (player going first). -/
structure FirstTurnRules where
  canAttack       : Bool := false
  canPlaySupporter : Bool := false
  canPlayItem     : Bool := true
  canAttachEnergy : Bool := true
  canEvolve       : Bool := false  -- (nobody can evolve turn 1)
  canRetreat      : Bool := true
deriving Repr, Inhabited

/-- Standard first-turn rules for the player going first (SV era). -/
def standardFirstTurnRules : FirstTurnRules where
  canAttack := false
  canPlaySupporter := false
  canPlayItem := true
  canAttachEnergy := true
  canEvolve := false
  canRetreat := true

/-- Second player (going second) first turn rules — can attack. -/
def secondPlayerFirstTurnRules : FirstTurnRules where
  canAttack := true
  canPlaySupporter := true
  canPlayItem := true
  canAttachEnergy := true
  canEvolve := false
  canRetreat := true

-- ============================================================
-- §9  Bench Size Limit
-- ============================================================

/-- Standard bench size in TCG. -/
def benchSizeLimit : Nat := 5

/-- Whether adding a Pokémon to bench is legal. -/
def canAddToBench (currentBench : Nat) : Bool :=
  currentBench < benchSizeLimit

/-- Some effects expand bench (Sky Field: 8 bench). -/
def expandedBenchLimit (hasSkyfField : Bool) : Nat :=
  if hasSkyfField then 8 else benchSizeLimit

-- ============================================================
-- §10  Retreat Cost Rules
-- ============================================================

/-- Retreat cost must be paid in full by discarding energy. -/
def canRetreat (attachedEnergy : Nat) (retreatCost : Nat) : Bool :=
  attachedEnergy ≥ retreatCost

/-- Energy remaining after retreat. -/
def energyAfterRetreat (attached : Nat) (cost : Nat) : Nat :=
  attached - cost

-- ============================================================
-- §11  Theorems: Weakness doubles FINAL damage
-- ============================================================

theorem weakness_doubles_damage (d : Nat) :
    applyWeakness d true = d * 2 := by
  simp [applyWeakness]

theorem no_weakness_no_change (d : Nat) :
    applyWeakness d false = d := by
  simp [applyWeakness]

theorem weakness_doubles_60 : applyWeakness 60 true = 120 := by
  simp [applyWeakness]

theorem weakness_doubles_100 : applyWeakness 100 true = 200 := by
  simp [applyWeakness]

-- ============================================================
-- §12  Theorems: Resistance subtracts 30
-- ============================================================

theorem resistance_subtracts_30 (d : Nat) (_h : d ≥ 30) :
    applyResistance d true = d - 30 := by
  simp [applyResistance]

theorem no_resistance_no_change (d : Nat) :
    applyResistance d false = d := by
  simp [applyResistance]

theorem resistance_floor_zero :
    applyResistance 20 true = 0 := by
  simp [applyResistance]

theorem resistance_from_100 :
    applyResistance 100 true = 70 := by
  simp [applyResistance]

-- ============================================================
-- §13  Theorems: Damage counters ≠ damage
-- ============================================================

theorem damage_counters_bypass_weakness :
    damageCounterHP 3 = 30 := by
  simp [damageCounterHP]

theorem damage_counters_no_pipeline :
    damageCounterHP 5 = 50 := by
  simp [damageCounterHP]

theorem damage_counter_is_10hp (n : Nat) :
    damageCounterHP n = n * 10 := by
  simp [damageCounterHP]

-- The key distinction: attack damage goes through the pipeline,
-- damage counters do NOT.
theorem attack_damage_uses_weakness :
    attackDamageHP 60 0 true false = 120 := by
  simp [attackDamageHP, calcDamage, applyWeakness, applyResistance]

theorem damage_counters_ignore_weakness :
    damageCounterHP 6 = 60 := by
  simp [damageCounterHP]

-- ============================================================
-- §14  Theorems: KO check after attack resolution
-- ============================================================

theorem ko_when_damage_equals_hp :
    isKOd 100 100 = true := by
  simp [isKOd]

theorem ko_when_damage_exceeds_hp :
    isKOd 100 150 = true := by
  simp [isKOd]

theorem no_ko_when_damage_less :
    isKOd 100 90 = false := by
  simp [isKOd]

theorem ko_check_after_attack :
    koCheckAfterAttack 120 120 = true := by
  simp [koCheckAfterAttack, isKOd]

-- ============================================================
-- §15  Theorems: Simultaneous KO = sudden death
-- ============================================================

theorem sudden_death_both_zero :
    isSuddenDeath 1 1 1 1 = true := by
  simp [isSuddenDeath]

theorem no_sudden_death_one_remaining :
    isSuddenDeath 2 1 1 1 = false := by
  simp [isSuddenDeath]

theorem sudden_death_prizes : suddenDeathPrizes = 1 := by rfl

theorem simultaneous_prizes_two_kos :
    simultaneousPrizes [2, 1] = 3 := by
  simp [simultaneousPrizes, List.foldl]

theorem simultaneous_prizes_three_kos :
    simultaneousPrizes [1, 1, 1] = 3 := by
  simp [simultaneousPrizes, List.foldl]

-- ============================================================
-- §16  Theorems: First player restrictions
-- ============================================================

theorem first_player_cant_attack :
    standardFirstTurnRules.canAttack = false := by rfl

theorem first_player_cant_supporter :
    standardFirstTurnRules.canPlaySupporter = false := by rfl

theorem first_player_can_item :
    standardFirstTurnRules.canPlayItem = true := by rfl

theorem first_player_can_attach :
    standardFirstTurnRules.canAttachEnergy = true := by rfl

theorem second_player_can_attack :
    secondPlayerFirstTurnRules.canAttack = true := by rfl

theorem second_player_can_supporter :
    secondPlayerFirstTurnRules.canPlaySupporter = true := by rfl

-- ============================================================
-- §17  Theorems: Bench size limit
-- ============================================================

theorem bench_limit_is_five : benchSizeLimit = 5 := by rfl

theorem can_add_to_empty_bench : canAddToBench 0 = true := by
  simp [canAddToBench, benchSizeLimit]

theorem cannot_add_to_full_bench : canAddToBench 5 = false := by
  simp [canAddToBench, benchSizeLimit]

theorem can_add_at_four : canAddToBench 4 = true := by
  simp [canAddToBench, benchSizeLimit]

theorem sky_field_expands : expandedBenchLimit true = 8 := by
  simp [expandedBenchLimit]

theorem no_sky_field_standard : expandedBenchLimit false = 5 := by
  simp [expandedBenchLimit, benchSizeLimit]

-- ============================================================
-- §18  Theorems: Retreat cost
-- ============================================================

theorem can_retreat_with_enough :
    canRetreat 3 2 = true := by
  simp [canRetreat]

theorem cannot_retreat_without_enough :
    canRetreat 1 2 = false := by
  simp [canRetreat]

theorem retreat_removes_energy :
    energyAfterRetreat 5 2 = 3 := by
  simp [energyAfterRetreat]

theorem retreat_cost_paid_in_full (a c : Nat) (h : a ≥ c) :
    energyAfterRetreat a c + c = a := by
  simp [energyAfterRetreat]
  omega

-- ============================================================
-- §19  Theorems: Ability from bench
-- ============================================================

theorem default_ability_works_from_bench :
    abilityUsable { worksFromBench := true, requiresActive := false } .bench = true := by
  simp [abilityUsable]

theorem active_only_ability_fails_bench :
    abilityUsable { worksFromBench := false, requiresActive := false } .bench = false := by
  simp [abilityUsable]

theorem any_ability_works_active :
    abilityUsable { worksFromBench := false, requiresActive := true } .active = true := by
  simp [abilityUsable]

theorem requires_active_blocks_bench :
    abilityUsable { worksFromBench := true, requiresActive := true } .bench = false := by
  simp [abilityUsable]

-- ============================================================
-- §20  Theorems: Full damage pipeline
-- ============================================================

/-- 60 base + 30 modifier + weakness = (60+30)*2 = 180, no resist -/
theorem full_pipeline_weak :
    calcDamage 60 30 true false = 180 := by
  simp [calcDamage, applyWeakness, applyResistance]

/-- 100 base, no modifier, resistance only = 100 - 30 = 70 -/
theorem full_pipeline_resist :
    calcDamage 100 0 false true = 70 := by
  simp [calcDamage, applyWeakness, applyResistance]

/-- 60 base, weak + resist = 60*2 - 30 = 90 -/
theorem full_pipeline_weak_and_resist :
    calcDamage 60 0 true true = 90 := by
  simp [calcDamage, applyWeakness, applyResistance]

/-- 10 base, resist, floor at 0 -/
theorem full_pipeline_resist_floor :
    calcDamage 10 0 false true = 0 := by
  simp [calcDamage, applyWeakness, applyResistance]

-- ============================================================
-- §21  Theorems: No evolving first turn
-- ============================================================

theorem no_evolve_first_turn_p1 :
    standardFirstTurnRules.canEvolve = false := by rfl

theorem no_evolve_first_turn_p2 :
    secondPlayerFirstTurnRules.canEvolve = false := by rfl

end PokemonLean.Core.RulingEdgeCases
