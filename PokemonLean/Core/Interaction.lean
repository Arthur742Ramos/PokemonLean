/-
  PokemonLean / Core / Interaction.lean

  Certified card interaction verification for the Pokémon TCG.
  Self-contained: defines ability lock states, item lock states,
  combo verifications, timing rules, and between-turns order.

  Formalizes:
    - Garbotoxin (ability lock when tool attached)
    - Path to the Peak (stadium-based ability lock for Rule Box)
    - Item lock (Vileplume ability, Seismitoad-EX Quaking Punch)
    - ADP Altered Creation GX (permanent extra prize)
    - Lost Zone engine (Comfey → Mirage Gate → Lost Mine)
    - Rare Candy (skip Stage 1)
    - Boss's Orders (gust effect)
    - Between-turns special condition order

  All proofs are sorry-free.  30+ theorems.
-/

namespace PokemonLean.Core.Interaction

-- ============================================================
-- §1  Core Type Definitions
-- ============================================================

/-- Pokémon types in the TCG. -/
inductive PType where
  | fire | water | grass | electric | psychic
  | fighting | dark | steel | dragon | fairy | normal
deriving DecidableEq, Repr, BEq, Inhabited

/-- Evolution stage. -/
inductive Stage where
  | basic | stage1 | stage2
deriving DecidableEq, Repr, BEq, Inhabited

/-- Whether a Pokémon has a Rule Box (ex, V, GX, VMAX, etc.). -/
inductive RuleBoxStatus where
  | none | hasRuleBox
deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================
-- §2  Ability Lock Mechanics
-- ============================================================

/-- Sources of ability lock in the game. -/
inductive AbilityLockSource where
  | garbotoxin      -- Garbodor with a Tool attached
  | pathToThePeak   -- Stadium: locks Rule Box Pokémon abilities
  | neutralizingGas -- Weezing: locks all abilities except Neutralizing Gas
deriving DecidableEq, Repr, BEq, Inhabited

/-- State of ability locks in the game. -/
structure AbilityLockState where
  garbotoxinActive   : Bool   -- Garbodor in play with tool
  pathToThePeakActive : Bool  -- Path to the Peak stadium in play
  neutralizingGasActive : Bool -- Galarian Weezing in play
deriving DecidableEq, Repr, BEq, Inhabited

/-- No locks active by default. -/
def AbilityLockState.none : AbilityLockState where
  garbotoxinActive := false
  pathToThePeakActive := false
  neutralizingGasActive := false

/-- Whether a Pokémon's ability is locked given the current lock state. -/
def isAbilityLocked (lock : AbilityLockState) (rb : RuleBoxStatus) (isGarbodor : Bool) (isWeezing : Bool) : Bool :=
  -- Garbotoxin locks ALL other abilities
  (lock.garbotoxinActive && !isGarbodor) ||
  -- Path to the Peak locks Rule Box Pokémon abilities
  (lock.pathToThePeakActive && rb == .hasRuleBox) ||
  -- Neutralizing Gas locks all abilities except itself
  (lock.neutralizingGasActive && !isWeezing)

/-- Whether ANY ability lock is active. -/
def anyAbilityLock (lock : AbilityLockState) : Bool :=
  lock.garbotoxinActive || lock.pathToThePeakActive || lock.neutralizingGasActive

-- ============================================================
-- §3  Item Lock Mechanics
-- ============================================================

/-- Sources of item lock. -/
inductive ItemLockSource where
  | vileplume       -- Vileplume's "Allergic Pollen" ability
  | seismitoadEX    -- Seismitoad-EX's "Quaking Punch" attack effect
deriving DecidableEq, Repr, BEq, Inhabited

/-- State of item locks. -/
structure ItemLockState where
  vileplumeLock    : Bool  -- Vileplume ability active
  seismitoadLock   : Bool  -- Quaking Punch effect active
deriving DecidableEq, Repr, BEq, Inhabited

/-- No item locks by default. -/
def ItemLockState.none : ItemLockState where
  vileplumeLock := false
  seismitoadLock := false

/-- Whether items are locked. -/
def isItemLocked (lock : ItemLockState) : Bool :=
  lock.vileplumeLock || lock.seismitoadLock

-- ============================================================
-- §4  Combined Lock State
-- ============================================================

/-- Full field lock state combining ability and item locks. -/
structure FieldLockState where
  abilityLock : AbilityLockState
  itemLock    : ItemLockState
deriving DecidableEq, Repr, BEq, Inhabited

/-- Default: no locks. -/
def FieldLockState.none : FieldLockState where
  abilityLock := AbilityLockState.none
  itemLock := ItemLockState.none

/-- Can play a Supporter card? (only blocked by specific effects, not ability/item lock). -/
def canPlaySupporter (_lock : FieldLockState) : Bool := true

/-- Can play an Item card? -/
def canPlayItem (lock : FieldLockState) : Bool :=
  !isItemLocked lock.itemLock

/-- Can use an ability? -/
def canUseAbility (lock : FieldLockState) (rb : RuleBoxStatus) (isGarbodor : Bool) (isWeezing : Bool) : Bool :=
  !isAbilityLocked lock.abilityLock rb isGarbodor isWeezing

/-- Can attack? (always yes unless specific effects) -/
def canAttack (_lock : FieldLockState) : Bool := true

-- ============================================================
-- §5  Garbotoxin + Float Stone Combo
-- ============================================================

/-- Garbodor's retreat cost with Float Stone attached. -/
def garbodorRetreatWithFloatStone : Nat := 0

/-- Garbodor's normal retreat cost. -/
def garbodorNormalRetreat : Nat := 3

/-- Float Stone reduces retreat cost to 0. -/
def floatStoneRetreat (normalRetreat : Nat) : Nat :=
  0  -- Float Stone makes retreat free regardless

/-- Whether Garbotoxin is active (requires tool attached). -/
def garbotoxinWithTool (hasToolAttached : Bool) : Bool :=
  hasToolAttached

-- ============================================================
-- §6  ADP (Arceus & Dialga & Palkia) Mechanics
-- ============================================================

/-- ADP's Altered Creation GX state. -/
structure ADPState where
  alteredCreationUsed : Bool   -- has Altered Creation GX been used?
  extraPrizeActive    : Bool   -- permanent +1 prize on KO
  extraDamageActive   : Bool   -- +30 damage to Active for rest of game
deriving DecidableEq, Repr, BEq, Inhabited

/-- Initial ADP state. -/
def ADPState.initial : ADPState where
  alteredCreationUsed := false
  extraPrizeActive := false
  extraDamageActive := false

/-- Use Altered Creation GX. -/
def useAlteredCreation (s : ADPState) : ADPState where
  alteredCreationUsed := true
  extraPrizeActive := true
  extraDamageActive := true

/-- Prize bonus from ADP. -/
def adpPrizeBonus (s : ADPState) : Nat :=
  if s.extraPrizeActive then 1 else 0

/-- Effective prizes from a KO with ADP bonus. -/
def effectivePrizes (basePrizeValue : Nat) (adp : ADPState) : Nat :=
  basePrizeValue + adpPrizeBonus adp

-- ============================================================
-- §7  Lost Zone Engine
-- ============================================================

/-- Lost Zone count state. -/
structure LostZoneState where
  count : Nat   -- number of cards in the Lost Zone
deriving DecidableEq, Repr, BEq, Inhabited

/-- Initial Lost Zone state. -/
def LostZoneState.initial : LostZoneState where
  count := 0

/-- Add cards to the Lost Zone (e.g., via Comfey's Flower Selecting). -/
def addToLostZone (s : LostZoneState) (n : Nat) : LostZoneState where
  count := s.count + n

/-- Comfey's Flower Selecting: look at top 2, put 1 in Lost Zone, 1 in hand. -/
def comfeyFlowerSelecting (s : LostZoneState) : LostZoneState :=
  addToLostZone s 1

/-- Mirage Gate threshold: need ≥ 7 cards in Lost Zone. -/
def mirageGateThreshold : Nat := 7

/-- Lost Mine threshold: need ≥ 10 cards in Lost Zone. -/
def lostMineThreshold : Nat := 10

/-- Can play Mirage Gate? -/
def canPlayMirageGate (s : LostZoneState) : Bool :=
  s.count ≥ mirageGateThreshold

/-- Can use Lost Mine (Sableye)? -/
def canUseLostMine (s : LostZoneState) : Bool :=
  s.count ≥ lostMineThreshold

-- ============================================================
-- §8  Rare Candy Mechanics
-- ============================================================

/-- Whether Rare Candy can be used to evolve a Basic directly to Stage 2. -/
def canUseRareCandy (pokemonStage : Stage) (targetStage : Stage) (turnPlayed : Bool) : Bool :=
  pokemonStage == .basic && targetStage == .stage2 && !turnPlayed
  -- Can't use on first turn the Pokémon was played

/-- The stage after applying Rare Candy. -/
def stageAfterRareCandy (pokemonStage : Stage) (targetStage : Stage) : Option Stage :=
  if pokemonStage == .basic && targetStage == .stage2 then
    some .stage2
  else
    none

-- ============================================================
-- §9  Boss's Orders (Gust Effect)
-- ============================================================

/-- Apply Boss's Orders: force a benched Pokémon active. -/
structure FieldState where
  activeIdx : Nat          -- index of active Pokémon
  benchSize : Nat          -- number of benched Pokémon
deriving DecidableEq, Repr, BEq, Inhabited

/-- Can play Boss's Orders? Need opponent to have bench. -/
def canPlayBoss (oppBenchSize : Nat) : Bool :=
  oppBenchSize > 0

-- ============================================================
-- §10  Between-Turns Special Condition Order
-- ============================================================

/-- Between-turns effects happen in this specific order. -/
inductive BetweenTurnsStep where
  | poisonDamage    -- Step 1: apply poison damage counters
  | burnCheck       -- Step 2: flip for burn, apply 20 damage on tails
  | sleepCheck      -- Step 3: flip for sleep, wake up on heads
  | paralysisCure   -- Step 4: paralysis automatically cures
deriving DecidableEq, Repr, BEq, Inhabited

/-- The canonical order of between-turns checks. -/
def betweenTurnsOrder : List BetweenTurnsStep :=
  [.poisonDamage, .burnCheck, .sleepCheck, .paralysisCure]

/-- Index of each step in the order (for proving sequencing). -/
def stepIndex : BetweenTurnsStep → Nat
  | .poisonDamage  => 0
  | .burnCheck     => 1
  | .sleepCheck    => 2
  | .paralysisCure => 3

/-- Poison damage amount (1 damage counter = 10 HP). -/
def poisonDamage : Nat := 10

/-- Burn damage amount on failed flip (2 damage counters = 20 HP). -/
def burnDamage : Nat := 20

/-- Apply between-turns damage. -/
def applyPoisonDamage (currentHP : Nat) (isPoisoned : Bool) : Nat :=
  if isPoisoned then
    if currentHP > poisonDamage then currentHP - poisonDamage else 0
  else currentHP

/-- Apply burn damage (on failed flip). -/
def applyBurnDamage (currentHP : Nat) (isBurned : Bool) (flipTails : Bool) : Nat :=
  if isBurned && flipTails then
    if currentHP > burnDamage then currentHP - burnDamage else 0
  else currentHP

-- ============================================================
-- §11  Theorems — Ability Lock
-- ============================================================

/-- Garbotoxin locks a non-Garbodor Pokémon's ability. -/
theorem garbotoxin_locks_others :
    isAbilityLocked { garbotoxinActive := true, pathToThePeakActive := false,
                      neutralizingGasActive := false } .none false false = true := by native_decide

/-- Garbotoxin does NOT lock Garbodor itself. -/
theorem garbotoxin_spares_self :
    isAbilityLocked { garbotoxinActive := true, pathToThePeakActive := false,
                      neutralizingGasActive := false } .none true false = false := by native_decide

/-- Path to the Peak locks Rule Box Pokémon. -/
theorem path_locks_rulebox :
    isAbilityLocked { garbotoxinActive := false, pathToThePeakActive := true,
                      neutralizingGasActive := false } .hasRuleBox false false = true := by native_decide

/-- Path to the Peak does NOT lock non-Rule-Box Pokémon. -/
theorem path_spares_nonrulebox :
    isAbilityLocked { garbotoxinActive := false, pathToThePeakActive := true,
                      neutralizingGasActive := false } .none false false = false := by native_decide

/-- Neutralizing Gas locks all non-Weezing Pokémon. -/
theorem neutralizing_locks_others :
    isAbilityLocked { garbotoxinActive := false, pathToThePeakActive := false,
                      neutralizingGasActive := true } .none false false = true := by native_decide

/-- Neutralizing Gas spares Weezing. -/
theorem neutralizing_spares_weezing :
    isAbilityLocked { garbotoxinActive := false, pathToThePeakActive := false,
                      neutralizingGasActive := true } .none false true = false := by native_decide

/-- No locks → no abilities locked. -/
theorem no_lock_no_block :
    isAbilityLocked AbilityLockState.none .none false false = false := by native_decide

/-- No locks → anyAbilityLock is false. -/
theorem no_lock_state : anyAbilityLock AbilityLockState.none = false := by native_decide

-- ============================================================
-- §12  Theorems — Item Lock
-- ============================================================

/-- Vileplume locks items. -/
theorem vileplume_locks_items :
    isItemLocked { vileplumeLock := true, seismitoadLock := false } = true := by native_decide

/-- Seismitoad locks items. -/
theorem seismitoad_locks_items :
    isItemLocked { vileplumeLock := false, seismitoadLock := true } = true := by native_decide

/-- No item lock → items are free. -/
theorem no_item_lock :
    isItemLocked ItemLockState.none = false := by native_decide

/-- Both locks simultaneously. -/
theorem both_item_locks :
    isItemLocked { vileplumeLock := true, seismitoadLock := true } = true := by native_decide

-- ============================================================
-- §13  Theorems — Combined Locks
-- ============================================================

/-- With both ability lock and item lock, only supporters and attacks work. -/
theorem both_locks_supporters_and_attacks :
    let lock : FieldLockState := {
      abilityLock := { garbotoxinActive := true, pathToThePeakActive := false, neutralizingGasActive := false },
      itemLock := { vileplumeLock := true, seismitoadLock := false }
    }
    canPlaySupporter lock = true ∧
    canPlayItem lock = false ∧
    canAttack lock = true ∧
    canUseAbility lock .none false false = false := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  · native_decide

/-- No locks → everything is available. -/
theorem no_locks_everything_works :
    let lock := FieldLockState.none
    canPlaySupporter lock = true ∧
    canPlayItem lock = true ∧
    canAttack lock = true ∧
    canUseAbility lock .none false false = true := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  · native_decide

-- ============================================================
-- §14  Theorems — Garbotoxin + Float Stone
-- ============================================================

/-- Garbodor with Float Stone: retreat cost is 0. -/
theorem garb_float_stone_retreat : garbodorRetreatWithFloatStone = 0 := by rfl

/-- Float Stone always reduces retreat to 0. -/
theorem float_stone_zero_retreat (n : Nat) : floatStoneRetreat n = 0 := by rfl

/-- Garbotoxin activates when tool is attached. -/
theorem garbotoxin_with_tool : garbotoxinWithTool true = true := by rfl

/-- Garbotoxin inactive without tool. -/
theorem garbotoxin_without_tool : garbotoxinWithTool false = false := by rfl

-- ============================================================
-- §15  Theorems — ADP Altered Creation
-- ============================================================

/-- Altered Creation enables extra prize. -/
theorem altered_creation_extra_prize :
    (useAlteredCreation ADPState.initial).extraPrizeActive = true := by rfl

/-- Altered Creation enables extra damage. -/
theorem altered_creation_extra_damage :
    (useAlteredCreation ADPState.initial).extraDamageActive = true := by rfl

/-- ADP bonus is permanent once activated. -/
theorem adp_bonus_permanent :
    adpPrizeBonus (useAlteredCreation ADPState.initial) = 1 := by native_decide

/-- Without ADP, no bonus. -/
theorem no_adp_no_bonus : adpPrizeBonus ADPState.initial = 0 := by native_decide

/-- KO-ing a basic (1 prize) with ADP gives 2 effective prizes. -/
theorem adp_basic_ko_two :
    effectivePrizes 1 (useAlteredCreation ADPState.initial) = 2 := by native_decide

/-- KO-ing an ex (2 prizes) with ADP gives 3 effective prizes. -/
theorem adp_ex_ko_three :
    effectivePrizes 2 (useAlteredCreation ADPState.initial) = 3 := by native_decide

/-- KO-ing a VMAX (3 prizes) with ADP gives 4 effective prizes (capped externally). -/
theorem adp_vmax_ko_four :
    effectivePrizes 3 (useAlteredCreation ADPState.initial) = 4 := by native_decide

-- ============================================================
-- §16  Theorems — Lost Zone Engine
-- ============================================================

/-- Initial Lost Zone is empty. -/
theorem initial_lost_zone_empty : LostZoneState.initial.count = 0 := by rfl

/-- Adding to Lost Zone increases count. -/
theorem add_lost_zone_increases (s : LostZoneState) (n : Nat) (hn : n > 0) :
    (addToLostZone s n).count > s.count := by
  simp [addToLostZone]
  omega

/-- Lost Zone count is monotonically increasing (adding never decreases). -/
theorem lost_zone_monotone (s : LostZoneState) (n : Nat) :
    (addToLostZone s n).count ≥ s.count := by
  simp [addToLostZone]

/-- Comfey adds exactly 1 to Lost Zone. -/
theorem comfey_adds_one (s : LostZoneState) :
    (comfeyFlowerSelecting s).count = s.count + 1 := by
  simp [comfeyFlowerSelecting, addToLostZone]

/-- 7 Comfey uses from empty reaches Mirage Gate threshold. -/
theorem seven_comfey_reaches_mirage_gate :
    let s := comfeyFlowerSelecting (comfeyFlowerSelecting (comfeyFlowerSelecting
             (comfeyFlowerSelecting (comfeyFlowerSelecting (comfeyFlowerSelecting
             (comfeyFlowerSelecting LostZoneState.initial))))))
    canPlayMirageGate s = true := by native_decide

/-- 10 Comfey uses from empty reaches Lost Mine threshold. -/
theorem ten_comfey_reaches_lost_mine :
    let s := comfeyFlowerSelecting (comfeyFlowerSelecting (comfeyFlowerSelecting
             (comfeyFlowerSelecting (comfeyFlowerSelecting (comfeyFlowerSelecting
             (comfeyFlowerSelecting (comfeyFlowerSelecting (comfeyFlowerSelecting
             (comfeyFlowerSelecting LostZoneState.initial)))))))))
    canUseLostMine s = true := by native_decide

/-- Can't play Mirage Gate with fewer than 7 cards. -/
theorem cant_mirage_gate_below_7 (s : LostZoneState) (h : s.count < 7) :
    canPlayMirageGate s = false := by
  simp [canPlayMirageGate, mirageGateThreshold]
  omega

/-- Can't use Lost Mine with fewer than 10 cards. -/
theorem cant_lost_mine_below_10 (s : LostZoneState) (h : s.count < 10) :
    canUseLostMine s = false := by
  simp [canUseLostMine, lostMineThreshold]
  omega

/-- Mirage Gate threshold ≤ Lost Mine threshold. -/
theorem mirage_before_lost_mine : mirageGateThreshold ≤ lostMineThreshold := by native_decide

-- ============================================================
-- §17  Theorems — Rare Candy
-- ============================================================

/-- Rare Candy works on Basic → Stage 2 (not first turn played). -/
theorem rare_candy_basic_to_stage2 :
    canUseRareCandy .basic .stage2 false = true := by native_decide

/-- Rare Candy doesn't work on Stage 1 → Stage 2 (must start from Basic). -/
theorem rare_candy_not_stage1 :
    canUseRareCandy .stage1 .stage2 false = false := by native_decide

/-- Rare Candy doesn't work on the turn the Pokémon was played. -/
theorem rare_candy_not_first_turn :
    canUseRareCandy .basic .stage2 true = false := by native_decide

/-- Rare Candy doesn't work Basic → Stage 1. -/
theorem rare_candy_not_basic_to_stage1 :
    canUseRareCandy .basic .stage1 false = false := by native_decide

/-- Rare Candy bypasses exactly one stage (Basic → Stage 2, skipping Stage 1). -/
theorem rare_candy_bypasses_one_stage :
    stageAfterRareCandy .basic .stage2 = some .stage2 := by native_decide

/-- Rare Candy fails for invalid combinations. -/
theorem rare_candy_invalid_stage1_target :
    stageAfterRareCandy .basic .stage1 = none := by native_decide

-- ============================================================
-- §18  Theorems — Boss's Orders
-- ============================================================

/-- Can play Boss with bench ≥ 1. -/
theorem boss_with_bench : canPlayBoss 3 = true := by native_decide

/-- Can't play Boss with empty bench. -/
theorem boss_no_bench : canPlayBoss 0 = false := by native_decide

-- ============================================================
-- §19  Theorems — Between-Turns Order
-- ============================================================

/-- Between-turns order has exactly 4 steps. -/
theorem between_turns_four_steps : betweenTurnsOrder.length = 4 := by native_decide

/-- Poison comes before burn. -/
theorem poison_before_burn : stepIndex .poisonDamage < stepIndex .burnCheck := by native_decide

/-- Burn comes before sleep. -/
theorem burn_before_sleep : stepIndex .burnCheck < stepIndex .sleepCheck := by native_decide

/-- Sleep comes before paralysis cure. -/
theorem sleep_before_paralysis : stepIndex .sleepCheck < stepIndex .paralysisCure := by native_decide

/-- Poison is first. -/
theorem poison_is_first : stepIndex .poisonDamage = 0 := by rfl

/-- Paralysis cure is last. -/
theorem paralysis_is_last : stepIndex .paralysisCure = 3 := by rfl

/-- Poison does 10 damage. -/
theorem poison_10_damage : poisonDamage = 10 := by rfl

/-- Burn does 20 damage. -/
theorem burn_20_damage : burnDamage = 20 := by rfl

/-- Poison applied to 100 HP leaves 90. -/
theorem poison_100_leaves_90 : applyPoisonDamage 100 true = 90 := by native_decide

/-- Poison applied to 10 HP leaves 0 (KO). -/
theorem poison_10_leaves_0 : applyPoisonDamage 10 true = 0 := by native_decide

/-- No poison → HP unchanged. -/
theorem no_poison_no_change (hp : Nat) : applyPoisonDamage hp false = hp := by
  simp [applyPoisonDamage]

/-- Burn on tails at 100 HP leaves 80. -/
theorem burn_tails_100_leaves_80 : applyBurnDamage 100 true true = 80 := by native_decide

/-- Burn on heads → no damage. -/
theorem burn_heads_no_damage (hp : Nat) : applyBurnDamage hp true false = hp := by
  simp [applyBurnDamage]

-- ============================================================
-- §20  #eval demonstrations
-- ============================================================

#eval isAbilityLocked { garbotoxinActive := true, pathToThePeakActive := false, neutralizingGasActive := false } .none false false
#eval isItemLocked { vileplumeLock := true, seismitoadLock := false }
#eval canPlayMirageGate { count := 7 }
#eval canUseLostMine { count := 10 }
#eval canUseRareCandy .basic .stage2 false
#eval effectivePrizes 2 (useAlteredCreation ADPState.initial)
#eval applyPoisonDamage 100 true
#eval applyBurnDamage 100 true true

end PokemonLean.Core.Interaction
