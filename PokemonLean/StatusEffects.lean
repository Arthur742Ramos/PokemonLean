import PokemonLean.Basic

namespace PokemonLean.StatusEffects

open PokemonLean

-- ============================================================================
-- COIN FLIP ABSTRACTION
-- ============================================================================

/-- Result of a coin flip: heads = true, tails = false -/
abbrev CoinFlip := Bool

-- ============================================================================
-- STATUS EFFECT RESOLUTION RESULTS
-- ============================================================================

/-- The outcome of resolving a status condition between turns -/
structure StatusResolution where
  newStatus : Option StatusCondition
  damageCounters : Nat          -- damage counters to place (each = 10 damage)
  selfDamageCounters : Nat      -- self-damage (confusion)
  skipNextAttack : Bool         -- whether the Pokémon skips next attack
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- INDIVIDUAL STATUS RESOLUTION FUNCTIONS
-- ============================================================================

/-- Sleep: flip a coin. Heads → wake up (status = none). Tails → stay asleep. -/
def resolveSleep (flip : CoinFlip) : StatusResolution :=
  { newStatus := if flip then none else some .asleep
    damageCounters := 0
    selfDamageCounters := 0
    skipNextAttack := false
  }

/-- Burn: place 2 damage counters (20 damage), then flip a coin. Heads → heal burn. -/
def resolveBurn (flip : CoinFlip) : StatusResolution :=
  { newStatus := if flip then none else some .burned
    damageCounters := 2
    selfDamageCounters := 0
    skipNextAttack := false
  }

/-- Poison: place 1 damage counter (10 damage) between turns. Status persists. -/
def resolvePoison : StatusResolution :=
  { newStatus := some .poisoned
    damageCounters := 1
    selfDamageCounters := 0
    skipNextAttack := false
  }

/-- Paralysis: skip next attack, then auto-heal after one turn. -/
def resolveParalysis : StatusResolution :=
  { newStatus := none           -- auto-heals after one turn
    damageCounters := 0
    selfDamageCounters := 0
    skipNextAttack := true
  }

/-- Confusion: when attacking, flip a coin. Tails → 3 damage counters to self.
    Between turns, confusion itself does not deal damage or wear off.
    The coin flip occurs at attack time, but we model the between-turns check here. -/
def resolveConfusion : StatusResolution :=
  { newStatus := some .confused
    damageCounters := 0
    selfDamageCounters := 0
    skipNextAttack := false
  }

/-- Resolve confusion at attack time: flip determines outcome -/
def resolveConfusionAttack (flip : CoinFlip) : StatusResolution :=
  { newStatus := some .confused
    damageCounters := 0
    selfDamageCounters := if flip then 0 else 3   -- 3 damage counters = 30 damage on tails
    skipNextAttack := false
  }

-- ============================================================================
-- MAIN resolveStatus FUNCTION
-- ============================================================================

/-- Resolve a status condition between turns given a coin flip -/
def resolveStatus (status : StatusCondition) (flip : CoinFlip) : StatusResolution :=
  match status with
  | .asleep    => resolveSleep flip
  | .burned    => resolveBurn flip
  | .poisoned  => resolvePoison
  | .paralyzed => resolveParalysis
  | .confused  => resolveConfusion

-- ============================================================================
-- APPLYING STATUS RESOLUTION TO A POKÉMON
-- ============================================================================

def applyResolution (pokemon : PokemonInPlay) (resolution : StatusResolution) : PokemonInPlay :=
  let totalDamage := resolution.damageCounters * 10 + resolution.selfDamageCounters * 10
  let newDmg := Nat.min (pokemon.damage + totalDamage) pokemon.card.hp
  { pokemon with
    damage := newDmg
    status := resolution.newStatus
  }

/-- Full between-turns status processing -/
def processBetweenTurns (pokemon : PokemonInPlay) (flip : CoinFlip) : PokemonInPlay :=
  match pokemon.status with
  | none => pokemon
  | some condition => applyResolution pokemon (resolveStatus condition flip)

-- ============================================================================
-- STATUS STACKING RULES: ONLY ONE SPECIAL CONDITION AT A TIME
-- ============================================================================

/-- Applying a new status replaces the old one -/
def applyNewStatus (pokemon : PokemonInPlay) (newCondition : StatusCondition) : PokemonInPlay :=
  { pokemon with status := some newCondition }

theorem applyNewStatus_replaces (pokemon : PokemonInPlay) (_oldCondition newCondition : StatusCondition)
    (_hOld : pokemon.status = some _oldCondition) :
    (applyNewStatus pokemon newCondition).status = some newCondition := by
  simp [applyNewStatus]

theorem applyNewStatus_always_sets (pokemon : PokemonInPlay) (newCondition : StatusCondition) :
    (applyNewStatus pokemon newCondition).status = some newCondition := by
  simp [applyNewStatus]

theorem applyNewStatus_preserves_energy (pokemon : PokemonInPlay) (condition : StatusCondition) :
    (applyNewStatus pokemon condition).energy = pokemon.energy := by
  simp [applyNewStatus]

theorem applyNewStatus_preserves_damage (pokemon : PokemonInPlay) (condition : StatusCondition) :
    (applyNewStatus pokemon condition).damage = pokemon.damage := by
  simp [applyNewStatus]

theorem applyNewStatus_preserves_card (pokemon : PokemonInPlay) (condition : StatusCondition) :
    (applyNewStatus pokemon condition).card = pokemon.card := by
  simp [applyNewStatus]

-- Only one status at a time: applying new status overwrites any previous
theorem status_no_stacking (pokemon : PokemonInPlay) (c1 c2 : StatusCondition) :
    (applyNewStatus (applyNewStatus pokemon c1) c2).status = some c2 := by
  simp [applyNewStatus]

-- ============================================================================
-- SLEEP THEOREMS
-- ============================================================================

theorem sleep_heads_wakes_up (flip : CoinFlip) (hHeads : flip = true) :
    (resolveSleep flip).newStatus = none := by
  simp [resolveSleep, hHeads]

theorem sleep_tails_stays_asleep (flip : CoinFlip) (hTails : flip = false) :
    (resolveSleep flip).newStatus = some .asleep := by
  simp [resolveSleep, hTails]

theorem sleep_no_damage (flip : CoinFlip) :
    (resolveSleep flip).damageCounters = 0 := by
  simp [resolveSleep]

theorem sleep_no_self_damage (flip : CoinFlip) :
    (resolveSleep flip).selfDamageCounters = 0 := by
  simp [resolveSleep]

theorem sleep_no_skip (flip : CoinFlip) :
    (resolveSleep flip).skipNextAttack = false := by
  simp [resolveSleep]

-- ============================================================================
-- BURN THEOREMS
-- ============================================================================

theorem burn_deals_two_counters (flip : CoinFlip) :
    (resolveBurn flip).damageCounters = 2 := by
  simp [resolveBurn]

theorem burn_heads_heals (flip : CoinFlip) (hHeads : flip = true) :
    (resolveBurn flip).newStatus = none := by
  simp [resolveBurn, hHeads]

theorem burn_tails_persists (flip : CoinFlip) (hTails : flip = false) :
    (resolveBurn flip).newStatus = some .burned := by
  simp [resolveBurn, hTails]

theorem burn_no_self_damage (flip : CoinFlip) :
    (resolveBurn flip).selfDamageCounters = 0 := by
  simp [resolveBurn]

theorem burn_no_skip (flip : CoinFlip) :
    (resolveBurn flip).skipNextAttack = false := by
  simp [resolveBurn]

-- ============================================================================
-- POISON THEOREMS
-- ============================================================================

theorem poison_deals_one_counter :
    resolvePoison.damageCounters = 1 := by
  simp [resolvePoison]

theorem poison_persists :
    resolvePoison.newStatus = some .poisoned := by
  simp [resolvePoison]

theorem poison_no_self_damage :
    resolvePoison.selfDamageCounters = 0 := by
  simp [resolvePoison]

theorem poison_no_skip :
    resolvePoison.skipNextAttack = false := by
  simp [resolvePoison]

theorem poison_no_flip_dependency (f1 f2 : CoinFlip) :
    resolveStatus .poisoned f1 = resolveStatus .poisoned f2 := by
  simp [resolveStatus]

-- ============================================================================
-- PARALYSIS THEOREMS
-- ============================================================================

theorem paralysis_auto_heals :
    resolveParalysis.newStatus = none := by
  simp [resolveParalysis]

theorem paralysis_skips_attack :
    resolveParalysis.skipNextAttack = true := by
  simp [resolveParalysis]

theorem paralysis_no_damage :
    resolveParalysis.damageCounters = 0 := by
  simp [resolveParalysis]

theorem paralysis_no_self_damage :
    resolveParalysis.selfDamageCounters = 0 := by
  simp [resolveParalysis]

theorem paralysis_no_flip_dependency (f1 f2 : CoinFlip) :
    resolveStatus .paralyzed f1 = resolveStatus .paralyzed f2 := by
  simp [resolveStatus, resolveParalysis]

-- ============================================================================
-- CONFUSION THEOREMS
-- ============================================================================

theorem confusion_persists_between_turns :
    resolveConfusion.newStatus = some .confused := by
  simp [resolveConfusion]

theorem confusion_no_damage_between_turns :
    resolveConfusion.damageCounters = 0 := by
  simp [resolveConfusion]

theorem confusion_no_self_damage_between_turns :
    resolveConfusion.selfDamageCounters = 0 := by
  simp [resolveConfusion]

theorem confusion_attack_heads_no_self_damage (flip : CoinFlip) (hHeads : flip = true) :
    (resolveConfusionAttack flip).selfDamageCounters = 0 := by
  simp [resolveConfusionAttack, hHeads]

theorem confusion_attack_tails_self_damage (flip : CoinFlip) (hTails : flip = false) :
    (resolveConfusionAttack flip).selfDamageCounters = 3 := by
  simp [resolveConfusionAttack, hTails]

-- ============================================================================
-- resolveStatus DISPATCH THEOREMS
-- ============================================================================

@[simp] theorem resolveStatus_asleep (flip : CoinFlip) :
    resolveStatus .asleep flip = resolveSleep flip := by
  rfl

@[simp] theorem resolveStatus_burned (flip : CoinFlip) :
    resolveStatus .burned flip = resolveBurn flip := by
  rfl

@[simp] theorem resolveStatus_poisoned (flip : CoinFlip) :
    resolveStatus .poisoned flip = resolvePoison := by
  rfl

@[simp] theorem resolveStatus_paralyzed (flip : CoinFlip) :
    resolveStatus .paralyzed flip = resolveParalysis := by
  rfl

@[simp] theorem resolveStatus_confused (flip : CoinFlip) :
    resolveStatus .confused flip = resolveConfusion := by
  rfl

-- ============================================================================
-- processBetweenTurns THEOREMS
-- ============================================================================

theorem processBetweenTurns_none (pokemon : PokemonInPlay) (flip : CoinFlip)
    (hNone : pokemon.status = none) :
    processBetweenTurns pokemon flip = pokemon := by
  simp [processBetweenTurns, hNone]

theorem processBetweenTurns_preserves_card (pokemon : PokemonInPlay) (flip : CoinFlip) :
    (processBetweenTurns pokemon flip).card = pokemon.card := by
  cases hStatus : pokemon.status with
  | none => simp [processBetweenTurns, hStatus]
  | some condition => simp [processBetweenTurns, hStatus, applyResolution]

theorem processBetweenTurns_preserves_energy (pokemon : PokemonInPlay) (flip : CoinFlip) :
    (processBetweenTurns pokemon flip).energy = pokemon.energy := by
  cases hStatus : pokemon.status with
  | none => simp [processBetweenTurns, hStatus]
  | some condition => simp [processBetweenTurns, hStatus, applyResolution]

-- ============================================================================
-- DAMAGE BOUNDS
-- ============================================================================

theorem applyResolution_damage_le_hp (pokemon : PokemonInPlay) (resolution : StatusResolution) :
    (applyResolution pokemon resolution).damage ≤ pokemon.card.hp := by
  simp [applyResolution, Nat.min_le_right]

theorem processBetweenTurns_damage_le_hp (pokemon : PokemonInPlay) (flip : CoinFlip)
    (hBound : pokemon.damage ≤ pokemon.card.hp) :
    (processBetweenTurns pokemon flip).damage ≤ pokemon.card.hp := by
  cases hStatus : pokemon.status with
  | none => simp [processBetweenTurns, hStatus]; exact hBound
  | some condition =>
    simp [processBetweenTurns, hStatus]
    exact applyResolution_damage_le_hp pokemon (resolveStatus condition flip)

theorem applyResolution_damage_ge (pokemon : PokemonInPlay) (resolution : StatusResolution)
    (hBound : pokemon.damage ≤ pokemon.card.hp) :
    pokemon.damage ≤ (applyResolution pokemon resolution).damage := by
  simp [applyResolution]
  exact (Nat.le_min).2 ⟨Nat.le_add_right _ _, hBound⟩

-- ============================================================================
-- POISON DAMAGE IS EXACTLY 10 (when within HP)
-- ============================================================================

theorem poison_between_turns_damage (pokemon : PokemonInPlay) (flip : CoinFlip)
    (hStatus : pokemon.status = some .poisoned)
    (hBound : pokemon.damage + 10 ≤ pokemon.card.hp) :
    (processBetweenTurns pokemon flip).damage = pokemon.damage + 10 := by
  simp [processBetweenTurns, hStatus, resolveStatus, resolvePoison, applyResolution]
  exact Nat.min_eq_left hBound

-- ============================================================================
-- BURN DAMAGE IS EXACTLY 20 (when within HP)
-- ============================================================================

theorem burn_between_turns_damage (pokemon : PokemonInPlay) (flip : CoinFlip)
    (hStatus : pokemon.status = some .burned)
    (hBound : pokemon.damage + 20 ≤ pokemon.card.hp) :
    (processBetweenTurns pokemon flip).damage = pokemon.damage + 20 := by
  simp [processBetweenTurns, hStatus, resolveStatus, resolveBurn, applyResolution]
  exact Nat.min_eq_left hBound

-- ============================================================================
-- PARALYSIS CLEARS AFTER PROCESSING
-- ============================================================================

theorem paralysis_clears_after_processing (pokemon : PokemonInPlay) (flip : CoinFlip)
    (hStatus : pokemon.status = some .paralyzed) :
    (processBetweenTurns pokemon flip).status = none := by
  simp [processBetweenTurns, hStatus, resolveStatus, resolveParalysis, applyResolution]

-- ============================================================================
-- CONFUSION PERSISTS AFTER PROCESSING
-- ============================================================================

theorem confusion_persists_after_processing (pokemon : PokemonInPlay) (flip : CoinFlip)
    (hStatus : pokemon.status = some .confused) :
    (processBetweenTurns pokemon flip).status = some .confused := by
  simp [processBetweenTurns, hStatus, resolveStatus, resolveConfusion, applyResolution]

-- ============================================================================
-- POISON PERSISTS AFTER PROCESSING
-- ============================================================================

theorem poison_persists_after_processing (pokemon : PokemonInPlay) (flip : CoinFlip)
    (hStatus : pokemon.status = some .poisoned) :
    (processBetweenTurns pokemon flip).status = some .poisoned := by
  simp [processBetweenTurns, hStatus, resolveStatus, resolvePoison, applyResolution]

-- ============================================================================
-- NO STATUS → NO DAMAGE FROM BETWEEN TURNS
-- ============================================================================

theorem no_status_no_between_turn_damage (pokemon : PokemonInPlay) (flip : CoinFlip)
    (hNone : pokemon.status = none) :
    (processBetweenTurns pokemon flip).damage = pokemon.damage := by
  simp [processBetweenTurns, hNone]

-- ============================================================================
-- CONFUSION BETWEEN TURNS DOES NO DAMAGE
-- ============================================================================

theorem confusion_between_turns_no_damage (pokemon : PokemonInPlay) (flip : CoinFlip)
    (hStatus : pokemon.status = some .confused)
    (hBound : pokemon.damage ≤ pokemon.card.hp) :
    (processBetweenTurns pokemon flip).damage = pokemon.damage := by
  simp [processBetweenTurns, hStatus, resolveStatus, resolveConfusion, applyResolution]
  exact Nat.min_eq_left hBound

-- ============================================================================
-- PARALYSIS BETWEEN TURNS DOES NO DAMAGE
-- ============================================================================

theorem paralysis_between_turns_no_damage (pokemon : PokemonInPlay) (flip : CoinFlip)
    (hStatus : pokemon.status = some .paralyzed)
    (hBound : pokemon.damage ≤ pokemon.card.hp) :
    (processBetweenTurns pokemon flip).damage = pokemon.damage := by
  simp [processBetweenTurns, hStatus, resolveStatus, resolveParalysis, applyResolution]
  exact Nat.min_eq_left hBound

-- ============================================================================
-- DAMAGE COUNTER CONVERSION
-- ============================================================================

def damageCountersToHP (counters : Nat) : Nat := counters * 10

@[simp] theorem damageCountersToHP_zero : damageCountersToHP 0 = 0 := by rfl
@[simp] theorem damageCountersToHP_one : damageCountersToHP 1 = 10 := by rfl
@[simp] theorem damageCountersToHP_two : damageCountersToHP 2 = 20 := by rfl
@[simp] theorem damageCountersToHP_three : damageCountersToHP 3 = 30 := by rfl

theorem damageCountersToHP_mono {a b : Nat} (h : a ≤ b) :
    damageCountersToHP a ≤ damageCountersToHP b := by
  simp [damageCountersToHP]
  exact Nat.mul_le_mul_right 10 h

-- ============================================================================
-- STATUS CONDITION TOTALITY
-- ============================================================================

theorem status_condition_cases (s : StatusCondition) :
    s = .asleep ∨ s = .burned ∨ s = .confused ∨ s = .paralyzed ∨ s = .poisoned := by
  cases s <;> simp

-- ============================================================================
-- resolveStatus DAMAGE IS BOUNDED
-- ============================================================================

theorem resolveStatus_damageCounters_le_two (condition : StatusCondition) (flip : CoinFlip) :
    (resolveStatus condition flip).damageCounters ≤ 2 := by
  cases condition <;> simp [resolveStatus, resolveSleep, resolveBurn, resolvePoison,
    resolveParalysis, resolveConfusion]

theorem resolveStatus_selfDamageCounters_le_three (condition : StatusCondition) (flip : CoinFlip) :
    (resolveStatus condition flip).selfDamageCounters ≤ 3 := by
  cases condition <;> simp [resolveStatus, resolveSleep, resolveBurn, resolvePoison,
    resolveParalysis, resolveConfusion]

-- ============================================================================
-- SKIP ATTACK ONLY FOR PARALYSIS
-- ============================================================================

theorem resolveStatus_skip_iff_paralyzed (condition : StatusCondition) (flip : CoinFlip) :
    (resolveStatus condition flip).skipNextAttack = true ↔ condition = .paralyzed := by
  cases condition <;> simp [resolveStatus, resolveSleep, resolveBurn, resolvePoison,
    resolveParalysis, resolveConfusion]

end PokemonLean.StatusEffects
