/-
  PokemonLean / Core / AttackResolution.lean

  Pokémon TCG attack resolution pipeline formalised in Lean 4.
  Self-contained: defines the 12-step attack resolution pipeline
  from declaration through energy check, status check, damage
  calculation, weakness/resistance, modifiers, KO detection,
  and prize collection.

  Pipeline:
    1. Declare attack on active Pokémon
    2. Check energy cost satisfied
    3. Check status: Paralyzed/Asleep = can't attack, Confused = flip
    4. Calculate base damage
    5. Apply weakness (×2)
    6. Apply resistance (−30, floor 0)
    7. Apply modifiers (Choice Band +30, etc.)
    8. Apply damage to defending Pokémon
    9. Check KO: damage ≥ remaining HP
    10. If KO: take prizes (1/2/3 based on rule box)
    11. If KO: defender promotes from bench (if no bench = game over)
    12. End attack phase

  All proofs are sorry-free.  32 theorems.
-/

namespace PokemonLean.Core.AttackResolution

-- ============================================================
-- §1  Core Types
-- ============================================================

/-- Coin flip. -/
inductive Coin where
  | heads | tails
  deriving DecidableEq, Repr

/-- Pokémon type for weakness/resistance. -/
inductive PType where
  | fire | water | grass | electric | psychic | fighting
  | dark | steel | dragon | fairy | normal
  deriving DecidableEq, Repr

/-- Rule box classification for prize values. -/
inductive RuleBox where
  | none        -- 1 prize
  | ex          -- 2 prizes
  | gx          -- 2 prizes
  | v           -- 2 prizes
  | vmax        -- 3 prizes
  | vstar       -- 2 prizes
  | tagTeam     -- 3 prizes
  deriving DecidableEq, Repr

/-- Prize count for a rule box. -/
def RuleBox.prizeCount : RuleBox → Nat
  | .none    => 1
  | .ex      => 2
  | .gx      => 2
  | .v       => 2
  | .vmax    => 3
  | .vstar   => 2
  | .tagTeam => 3

/-- Special condition status of the active Pokémon. -/
inductive StatusCondition where
  | healthy
  | paralyzed
  | asleep
  | confused
  | poisoned
  | burned
  deriving DecidableEq, Repr

/-- Attack modifier tool. -/
inductive AttackModifier where
  | none
  | choiceBand     -- +30 vs V/GX/EX
  | muscleBand     -- +20 to all
  deriving DecidableEq, Repr

def AttackModifier.bonus : AttackModifier → Nat
  | .none       => 0
  | .choiceBand => 30
  | .muscleBand => 20

-- ============================================================
-- §2  Pokémon in Play
-- ============================================================

/-- Energy cost: list of required energy types. -/
structure EnergyCost where
  required : List PType
  colorless : Nat      -- number of any-type energy needed
  deriving DecidableEq, Repr

/-- An attack on a Pokémon card. -/
structure Attack where
  name       : String
  cost       : EnergyCost
  baseDamage : Nat
  deriving DecidableEq, Repr

/-- Pokémon in play (active or bench). -/
structure Pokemon where
  name        : String
  ptype       : PType
  maxHP       : Nat
  damage      : Nat       -- current damage counters
  attacks     : List Attack
  ruleBox     : RuleBox
  weakness    : Option PType
  resistance  : Option PType
  attachedEnergy : List PType
  status      : StatusCondition
  tool        : AttackModifier
  deriving DecidableEq, Repr

/-- Remaining HP. -/
def Pokemon.remainingHP (p : Pokemon) : Nat :=
  if p.maxHP > p.damage then p.maxHP - p.damage else 0

/-- Whether KO'd. -/
def Pokemon.isKO (p : Pokemon) : Bool :=
  p.damage ≥ p.maxHP

-- ============================================================
-- §3  Step 1–2: Attack Declaration & Energy Check
-- ============================================================

/-- Count energy of a specific type in the attached list. -/
def countEnergy (attached : List PType) (t : PType) : Nat :=
  (attached.filter (· == t)).length

/-- Check if energy requirements are met.
    For simplicity: check each required type has at least 1 matching energy,
    plus total attached ≥ total required + colorless. -/
def energySatisfied (attached : List PType) (cost : EnergyCost) : Bool :=
  cost.required.all (fun t => countEnergy attached t > 0) &&
  attached.length ≥ cost.required.length + cost.colorless

-- ============================================================
-- §4  Step 3: Status Check
-- ============================================================

/-- Whether the Pokémon can attack given its status. -/
def canAttackWithStatus (status : StatusCondition) : Bool :=
  match status with
  | .paralyzed => false
  | .asleep    => false
  | _          => true

/-- Confused attack resolution. -/
inductive ConfusedResult where
  | attackNormally
  | selfDamage (amount : Nat)
  deriving DecidableEq, Repr

/-- Resolve confusion check. -/
def resolveConfusion (status : StatusCondition) (flip : Coin) : ConfusedResult :=
  match status with
  | .confused =>
    match flip with
    | .heads => .attackNormally
    | .tails => .selfDamage 30
  | _ => .attackNormally

-- ============================================================
-- §5  Steps 4–7: Damage Calculation Pipeline
-- ============================================================

/-- Step 4: Base damage from the attack. -/
def baseDamage (attack : Attack) : Nat :=
  attack.baseDamage

/-- Step 5: Apply weakness (×2). -/
def applyWeakness (damage : Nat) (attackerType : PType) (defenderWeakness : Option PType) : Nat :=
  match defenderWeakness with
  | some w => if attackerType == w then damage * 2 else damage
  | none   => damage

/-- Step 6: Apply resistance (−30, floor 0). -/
def applyResistance (damage : Nat) (attackerType : PType) (defenderResistance : Option PType) : Nat :=
  match defenderResistance with
  | some r => if attackerType == r then (if damage ≥ 30 then damage - 30 else 0) else damage
  | none   => damage

/-- Step 7: Apply modifier bonus. -/
def applyModifier (damage : Nat) (modifier : AttackModifier) : Nat :=
  damage + modifier.bonus

/-- Full damage pipeline. -/
def calculateDamage (attack : Attack) (attackerType : PType)
    (defenderWeakness defenderResistance : Option PType)
    (modifier : AttackModifier) : Nat :=
  let d1 := baseDamage attack
  let d2 := applyWeakness d1 attackerType defenderWeakness
  let d3 := applyResistance d2 attackerType defenderResistance
  applyModifier d3 modifier

-- ============================================================
-- §6  Steps 8–9: Apply Damage & KO Check
-- ============================================================

/-- Apply damage to a Pokémon. -/
def applyDamage (p : Pokemon) (dmg : Nat) : Pokemon :=
  { p with damage := p.damage + dmg }

/-- Check if a Pokémon is knocked out after taking damage. -/
def isKnockedOut (p : Pokemon) (dmg : Nat) : Bool :=
  p.damage + dmg ≥ p.maxHP

-- ============================================================
-- §7  Steps 10–11: Prize Collection & Promotion
-- ============================================================

/-- Prizes to take on KO. -/
def prizesToTake (ko : Pokemon) : Nat :=
  ko.ruleBox.prizeCount

/-- Whether the game ends because the defender has no bench to promote. -/
def gameOverNoBench (benchCount : Nat) : Bool :=
  benchCount == 0

-- ============================================================
-- §8  Full Attack Resolution
-- ============================================================

/-- Result of attack resolution. -/
inductive AttackResult where
  | blocked (reason : String)         -- paralyzed, asleep, not enough energy
  | confusedSelfDamage (dmg : Nat)    -- confused, tails
  | damage (dealt : Nat) (ko : Bool) (prizesTaken : Nat) (gameOver : Bool)
  deriving DecidableEq, Repr

/-- Full attack resolution pipeline. -/
def resolveAttack (attacker defender : Pokemon) (attackIdx : Nat)
    (confusionFlip : Coin) (defenderBenchCount : Nat) : AttackResult :=
  -- Step 1: Get the attack
  match attacker.attacks[attackIdx]? with
  | none => .blocked "Invalid attack index"
  | some attack =>
    -- Step 2: Check energy
    if !energySatisfied attacker.attachedEnergy attack.cost then
      .blocked "Not enough energy"
    -- Step 3: Check status
    else if !canAttackWithStatus attacker.status then
      .blocked "Status condition prevents attack"
    else
      -- Confusion check
      match resolveConfusion attacker.status confusionFlip with
      | .selfDamage dmg => .confusedSelfDamage dmg
      | .attackNormally =>
        -- Steps 4–7: Calculate damage
        let dmg := calculateDamage attack attacker.ptype defender.weakness defender.resistance attacker.tool
        -- Steps 8–9: Apply damage, check KO
        let ko := isKnockedOut defender dmg
        -- Steps 10–11: Prizes and game end
        let prizes := if ko then prizesToTake defender else 0
        let gameEnd := ko && gameOverNoBench defenderBenchCount
        .damage dmg ko prizes gameEnd

-- ============================================================
-- §9  Theorems — Status Blocking
-- ============================================================

/-- Theorem 1: Paralyzed Pokémon can't attack. -/
theorem paralyzed_cant_attack : canAttackWithStatus .paralyzed = false := by rfl

/-- Theorem 2: Asleep Pokémon can't attack. -/
theorem asleep_cant_attack : canAttackWithStatus .asleep = false := by rfl

/-- Theorem 3: Healthy Pokémon can attack. -/
theorem healthy_can_attack : canAttackWithStatus .healthy = true := by rfl

/-- Theorem 4: Confused Pokémon can attempt to attack. -/
theorem confused_can_attack : canAttackWithStatus .confused = true := by rfl

/-- Theorem 5: Poisoned Pokémon can attack. -/
theorem poisoned_can_attack : canAttackWithStatus .poisoned = true := by rfl

/-- Theorem 6: Burned Pokémon can attack. -/
theorem burned_can_attack : canAttackWithStatus .burned = true := by rfl

-- ============================================================
-- §10  Theorems — Confusion
-- ============================================================

/-- Theorem 7: Confused + tails = 30 self-damage. -/
theorem confused_tails_self_damage :
    resolveConfusion .confused .tails = .selfDamage 30 := by rfl

/-- Theorem 8: Confused + heads = normal attack. -/
theorem confused_heads_normal :
    resolveConfusion .confused .heads = .attackNormally := by rfl

/-- Theorem 9: Non-confused Pokémon always attacks normally. -/
theorem healthy_always_normal (flip : Coin) :
    resolveConfusion .healthy flip = .attackNormally := by rfl

-- ============================================================
-- §11  Theorems — Weakness and Resistance
-- ============================================================

/-- Theorem 10: Weakness doubles damage. -/
theorem weakness_doubles (dmg : Nat) (t : PType) :
    applyWeakness dmg t (some t) = dmg * 2 := by
  simp [applyWeakness]

/-- Theorem 11: No weakness = no change. -/
theorem no_weakness_id (dmg : Nat) (t : PType) :
    applyWeakness dmg t none = dmg := by rfl

/-- Theorem 12: Resistance subtracts 30 when damage ≥ 30. -/
theorem resistance_sub30 (dmg : Nat) (t : PType) (h : dmg ≥ 30) :
    applyResistance dmg t (some t) = dmg - 30 := by
  simp [applyResistance, h]

/-- Theorem 13: Resistance floors at 0 for small damage. -/
theorem resistance_floor (dmg : Nat) (t : PType) (h : dmg < 30) :
    applyResistance dmg t (some t) = 0 := by
  simp [applyResistance]
  omega

/-- Theorem 14: No resistance = no change. -/
theorem no_resistance_id (dmg : Nat) (t : PType) :
    applyResistance dmg t none = dmg := by rfl

-- ============================================================
-- §12  Theorems — Modifiers
-- ============================================================

/-- Theorem 15: Choice Band adds 30. -/
theorem choice_band_adds_30 (dmg : Nat) :
    applyModifier dmg .choiceBand = dmg + 30 := by rfl

/-- Theorem 16: Muscle Band adds 20. -/
theorem muscle_band_adds_20 (dmg : Nat) :
    applyModifier dmg .muscleBand = dmg + 20 := by rfl

/-- Theorem 17: No modifier = identity. -/
theorem no_modifier_id (dmg : Nat) :
    applyModifier dmg .none = dmg := by
  simp [applyModifier, AttackModifier.bonus]

-- ============================================================
-- §13  Theorems — KO Detection
-- ============================================================

/-- Theorem 18: Damage ≥ HP means KO. -/
theorem damage_ge_hp_ko (p : Pokemon) (dmg : Nat) (h : p.damage + dmg ≥ p.maxHP) :
    isKnockedOut p dmg = true := by
  simp [isKnockedOut, h]

/-- Theorem 19: Zero damage on full HP = not KO (assuming HP > 0). -/
theorem zero_damage_not_ko (p : Pokemon) (h : p.damage = 0) (hpos : p.maxHP > 0) :
    isKnockedOut p 0 = false := by
  simp [isKnockedOut, h]
  omega

/-- Theorem 20: Remaining HP of undamaged Pokémon equals max HP. -/
theorem undamaged_full_hp (p : Pokemon) (h : p.damage = 0) :
    p.remainingHP = p.maxHP := by
  simp [Pokemon.remainingHP, h]
  omega

/-- Theorem 21: KO'd Pokémon has 0 remaining HP. -/
theorem ko_zero_hp (p : Pokemon) (h : p.damage ≥ p.maxHP) :
    p.remainingHP = 0 := by
  simp [Pokemon.remainingHP]
  omega

-- ============================================================
-- §14  Theorems — Prize Collection
-- ============================================================

/-- Theorem 22: Regular Pokémon gives 1 prize on KO. -/
theorem regular_one_prize : RuleBox.none.prizeCount = 1 := by rfl

/-- Theorem 23: EX gives 2 prizes. -/
theorem ex_two_prizes : RuleBox.ex.prizeCount = 2 := by rfl

/-- Theorem 24: VMAX gives 3 prizes. -/
theorem vmax_three_prizes : RuleBox.vmax.prizeCount = 3 := by rfl

/-- Theorem 25: Tag Team gives 3 prizes. -/
theorem tag_team_three_prizes : RuleBox.tagTeam.prizeCount = 3 := by rfl

/-- Theorem 26: Prize count is always ≥ 1. -/
theorem prize_at_least_one (rb : RuleBox) : rb.prizeCount ≥ 1 := by
  cases rb <;> simp [RuleBox.prizeCount]

/-- Theorem 27: Prize count is always ≤ 3. -/
theorem prize_at_most_three (rb : RuleBox) : rb.prizeCount ≤ 3 := by
  cases rb <;> simp [RuleBox.prizeCount]

-- ============================================================
-- §15  Theorems — Game Over
-- ============================================================

/-- Theorem 28: No bench after KO = game over. -/
theorem no_bench_game_over : gameOverNoBench 0 = true := by rfl

/-- Theorem 29: Having bench means not game over. -/
theorem bench_not_game_over (n : Nat) (h : n > 0) : gameOverNoBench n = false := by
  simp [gameOverNoBench]
  omega

-- ============================================================
-- §16  Theorems — Pipeline Properties
-- ============================================================

/-- Theorem 30: Damage pipeline with no weakness/resistance/modifier is base damage. -/
theorem pipeline_neutral (attack : Attack) (t : PType) :
    calculateDamage attack t none none .none = attack.baseDamage := by
  simp [calculateDamage, baseDamage, applyWeakness, applyResistance, applyModifier,
        AttackModifier.bonus]

/-- Theorem 31: applyDamage increases damage counter. -/
theorem apply_damage_adds (p : Pokemon) (dmg : Nat) :
    (applyDamage p dmg).damage = p.damage + dmg := by rfl

/-- Theorem 32: Weakness is monotone: more base damage → more after weakness. -/
theorem weakness_monotone (a b : Nat) (t : PType) (w : Option PType)
    (h : a ≤ b) :
    applyWeakness a t w ≤ applyWeakness b t w := by
  simp [applyWeakness]
  split
  · split <;> omega
  · omega

end PokemonLean.Core.AttackResolution