import PokemonLean.Basic

namespace PokemonLean.DamageCounters

open PokemonLean

-- ============================================================================
-- DAMAGE COUNTER FUNDAMENTALS
-- ============================================================================

/-- Damage counters are placed in 10-point increments in the Pokémon TCG. -/
def damageCounterValue : Nat := 10

/-- Number of damage counters on a Pokémon (damage / 10). -/
def damageCounters (pokemon : PokemonInPlay) : Nat :=
  pokemon.damage / damageCounterValue

/-- Remaining HP after damage (floored at 0 via Nat subtraction). -/
def remainingHP (pokemon : PokemonInPlay) : Nat :=
  pokemon.card.hp - pokemon.damage

/-- A Pokémon is knocked out when its damage ≥ its HP. -/
def isKnockedOut (pokemon : PokemonInPlay) : Bool :=
  pokemon.damage ≥ pokemon.card.hp

/-- Place a specific number of damage counters (each worth 10). -/
def placeDamageCounters (pokemon : PokemonInPlay) (counters : Nat) : PokemonInPlay :=
  { pokemon with damage := pokemon.damage + counters * damageCounterValue }

/-- Remove damage counters (healing). Cannot reduce damage below 0. -/
def removeDamageCounters (pokemon : PokemonInPlay) (counters : Nat) : PokemonInPlay :=
  { pokemon with damage := pokemon.damage - counters * damageCounterValue }

/-- Heal a specific amount of damage (not in counter increments). -/
def healDamage (pokemon : PokemonInPlay) (amount : Nat) : PokemonInPlay :=
  { pokemon with damage := pokemon.damage - amount }

/-- Transfer damage counters from one Pokémon to another. -/
def transferDamageCounters (source target : PokemonInPlay) (counters : Nat) :
    PokemonInPlay × PokemonInPlay :=
  let actualCounters := Nat.min counters (damageCounters source)
  let amount := actualCounters * damageCounterValue
  ( { source with damage := source.damage - amount }
  , { target with damage := target.damage + amount } )

/-- Apply damage counters (in 10-point increments) preserving status, energy, and card. -/
def applyDamageCounters (pokemon : PokemonInPlay) (counters : Nat) : PokemonInPlay :=
  { pokemon with damage := pokemon.damage + counters * damageCounterValue }

/-- Maximum number of damage counters before KO. -/
def maxDamageCounters (pokemon : PokemonInPlay) : Nat :=
  pokemon.card.hp / damageCounterValue

-- ============================================================================
-- REMAINING HP THEOREMS
-- ============================================================================

theorem remainingHP_le_hp (pokemon : PokemonInPlay) :
    remainingHP pokemon ≤ pokemon.card.hp := by
  simp [remainingHP, Nat.sub_le]

theorem remainingHP_zero_of_ko (pokemon : PokemonInPlay)
    (hKO : isKnockedOut pokemon = true) :
    remainingHP pokemon = 0 := by
  simp [isKnockedOut] at hKO
  simp [remainingHP, Nat.sub_eq_zero_of_le hKO]

theorem remainingHP_pos_of_not_ko (pokemon : PokemonInPlay)
    (hNotKO : isKnockedOut pokemon = false) :
    0 < remainingHP pokemon := by
  simp [isKnockedOut] at hNotKO
  simp [remainingHP]; omega


theorem remainingHP_zero_damage (pokemon : PokemonInPlay)
    (hZero : pokemon.damage = 0) :
    remainingHP pokemon = pokemon.card.hp := by
  simp [remainingHP, hZero]

theorem remainingHP_full_damage (pokemon : PokemonInPlay)
    (hFull : pokemon.damage ≥ pokemon.card.hp) :
    remainingHP pokemon = 0 := by
  simp [remainingHP, Nat.sub_eq_zero_of_le hFull]

-- ============================================================================
-- KNOCKED OUT THEOREMS
-- ============================================================================

theorem isKnockedOut_iff (pokemon : PokemonInPlay) :
    isKnockedOut pokemon = true ↔ pokemon.damage ≥ pokemon.card.hp := by
  simp [isKnockedOut]

theorem isKnockedOut_false_iff (pokemon : PokemonInPlay) :
    isKnockedOut pokemon = false ↔ pokemon.damage < pokemon.card.hp := by
  constructor
  · intro h; simp [isKnockedOut] at h; omega
  · intro h; simp [isKnockedOut]; omega

theorem isKnockedOut_of_damage_ge_hp (pokemon : PokemonInPlay)
    (h : pokemon.damage ≥ pokemon.card.hp) :
    isKnockedOut pokemon = true := by
  simp [isKnockedOut, h]

theorem not_ko_of_zero_damage (pokemon : PokemonInPlay)
    (hHP : 0 < pokemon.card.hp) (hZero : pokemon.damage = 0) :
    isKnockedOut pokemon = false := by
  simp [isKnockedOut, hZero]; omega

/-- Overkill doesn't matter: KO at exactly hp or at 10× hp is the same. -/
theorem overkill_same_ko (pokemon : PokemonInPlay) (d1 d2 : Nat)
    (h1 : d1 ≥ pokemon.card.hp) (h2 : d2 ≥ pokemon.card.hp) :
    isKnockedOut { pokemon with damage := d1 } =
    isKnockedOut { pokemon with damage := d2 } := by
  simp [isKnockedOut, h1, h2]

theorem ko_remainingHP_equiv (pokemon : PokemonInPlay) :
    isKnockedOut pokemon = true ↔ remainingHP pokemon = 0 := by
  constructor
  · intro h; exact remainingHP_zero_of_ko pokemon h
  · intro h; simp [remainingHP] at h; simp [isKnockedOut]; omega

-- ============================================================================
-- DAMAGE COUNTER ARITHMETIC
-- ============================================================================

@[simp] theorem damageCounterValue_eq : damageCounterValue = 10 := rfl

theorem damageCounters_zero (pokemon : PokemonInPlay)
    (h : pokemon.damage = 0) :
    damageCounters pokemon = 0 := by
  simp [damageCounters, h]

theorem damageCounters_le_maxCounters (pokemon : PokemonInPlay)
    (hBound : pokemon.damage ≤ pokemon.card.hp) :
    damageCounters pokemon ≤ maxDamageCounters pokemon := by
  simp [damageCounters, maxDamageCounters, damageCounterValue]
  omega

theorem placeDamageCounters_zero (pokemon : PokemonInPlay) :
    placeDamageCounters pokemon 0 = pokemon := by
  simp [placeDamageCounters, damageCounterValue]

theorem placeDamageCounters_damage (pokemon : PokemonInPlay) (n : Nat) :
    (placeDamageCounters pokemon n).damage = pokemon.damage + n * damageCounterValue := by
  simp [placeDamageCounters]

theorem placeDamageCounters_status (pokemon : PokemonInPlay) (n : Nat) :
    (placeDamageCounters pokemon n).status = pokemon.status := by
  simp [placeDamageCounters]

theorem placeDamageCounters_energy (pokemon : PokemonInPlay) (n : Nat) :
    (placeDamageCounters pokemon n).energy = pokemon.energy := by
  simp [placeDamageCounters]

theorem placeDamageCounters_card (pokemon : PokemonInPlay) (n : Nat) :
    (placeDamageCounters pokemon n).card = pokemon.card := by
  simp [placeDamageCounters]

-- ============================================================================
-- HEALING THEOREMS
-- ============================================================================

theorem healDamage_zero (pokemon : PokemonInPlay) :
    healDamage pokemon 0 = pokemon := by
  simp [healDamage]

theorem healDamage_damage_le (pokemon : PokemonInPlay) (amount : Nat) :
    (healDamage pokemon amount).damage ≤ pokemon.damage := by
  simp [healDamage, Nat.sub_le]

theorem healDamage_status (pokemon : PokemonInPlay) (amount : Nat) :
    (healDamage pokemon amount).status = pokemon.status := by
  simp [healDamage]

theorem healDamage_energy (pokemon : PokemonInPlay) (amount : Nat) :
    (healDamage pokemon amount).energy = pokemon.energy := by
  simp [healDamage]

theorem healDamage_card (pokemon : PokemonInPlay) (amount : Nat) :
    (healDamage pokemon amount).card = pokemon.card := by
  simp [healDamage]

theorem healDamage_cannot_go_negative (pokemon : PokemonInPlay) (amount : Nat) :
    (healDamage pokemon amount).damage = pokemon.damage - amount := by
  simp [healDamage]

theorem healDamage_full (pokemon : PokemonInPlay) (amount : Nat)
    (h : amount ≥ pokemon.damage) :
    (healDamage pokemon amount).damage = 0 := by
  simp [healDamage, Nat.sub_eq_zero_of_le h]

theorem healDamage_remainingHP_ge (pokemon : PokemonInPlay) (amount : Nat) :
    remainingHP pokemon ≤ remainingHP (healDamage pokemon amount) := by
  simp [remainingHP, healDamage]; omega

-- ============================================================================
-- REMOVE DAMAGE COUNTERS THEOREMS
-- ============================================================================

theorem removeDamageCounters_zero (pokemon : PokemonInPlay) :
    removeDamageCounters pokemon 0 = pokemon := by
  simp [removeDamageCounters, damageCounterValue]

theorem removeDamageCounters_damage_le (pokemon : PokemonInPlay) (n : Nat) :
    (removeDamageCounters pokemon n).damage ≤ pokemon.damage := by
  simp [removeDamageCounters, Nat.sub_le]

theorem removeDamageCounters_status (pokemon : PokemonInPlay) (n : Nat) :
    (removeDamageCounters pokemon n).status = pokemon.status := by
  simp [removeDamageCounters]

theorem removeDamageCounters_energy (pokemon : PokemonInPlay) (n : Nat) :
    (removeDamageCounters pokemon n).energy = pokemon.energy := by
  simp [removeDamageCounters]

theorem removeDamageCounters_card (pokemon : PokemonInPlay) (n : Nat) :
    (removeDamageCounters pokemon n).card = pokemon.card := by
  simp [removeDamageCounters]

-- ============================================================================
-- DAMAGE COUNTER TRANSFER THEOREMS
-- ============================================================================

theorem transferDamageCounters_source_damage_le (source target : PokemonInPlay) (n : Nat) :
    (transferDamageCounters source target n).1.damage ≤ source.damage := by
  simp [transferDamageCounters, Nat.sub_le]

theorem transferDamageCounters_target_damage_ge (source target : PokemonInPlay) (n : Nat) :
    target.damage ≤ (transferDamageCounters source target n).2.damage := by
  simp [transferDamageCounters, Nat.le_add_right]

theorem transferDamageCounters_zero (source target : PokemonInPlay) :
    transferDamageCounters source target 0 =
      (source, target) := by
  simp [transferDamageCounters, damageCounters, damageCounterValue]

theorem transferDamageCounters_source_status (source target : PokemonInPlay) (n : Nat) :
    (transferDamageCounters source target n).1.status = source.status := by
  simp [transferDamageCounters]

theorem transferDamageCounters_target_status (source target : PokemonInPlay) (n : Nat) :
    (transferDamageCounters source target n).2.status = target.status := by
  simp [transferDamageCounters]

theorem transferDamageCounters_source_card (source target : PokemonInPlay) (n : Nat) :
    (transferDamageCounters source target n).1.card = source.card := by
  simp [transferDamageCounters]

theorem transferDamageCounters_target_card (source target : PokemonInPlay) (n : Nat) :
    (transferDamageCounters source target n).2.card = target.card := by
  simp [transferDamageCounters]

-- ============================================================================
-- APPLY DAMAGE COUNTERS (PRESERVING STATE) THEOREMS
-- ============================================================================

theorem applyDamageCounters_status (pokemon : PokemonInPlay) (n : Nat) :
    (applyDamageCounters pokemon n).status = pokemon.status := by
  simp [applyDamageCounters]

theorem applyDamageCounters_energy (pokemon : PokemonInPlay) (n : Nat) :
    (applyDamageCounters pokemon n).energy = pokemon.energy := by
  simp [applyDamageCounters]

theorem applyDamageCounters_card (pokemon : PokemonInPlay) (n : Nat) :
    (applyDamageCounters pokemon n).card = pokemon.card := by
  simp [applyDamageCounters]

theorem applyDamageCounters_damage (pokemon : PokemonInPlay) (n : Nat) :
    (applyDamageCounters pokemon n).damage = pokemon.damage + n * damageCounterValue := by
  simp [applyDamageCounters]

theorem applyDamageCounters_zero (pokemon : PokemonInPlay) :
    applyDamageCounters pokemon 0 = pokemon := by
  simp [applyDamageCounters, damageCounterValue]

theorem applyDamageCounters_damage_ge (pokemon : PokemonInPlay) (n : Nat) :
    pokemon.damage ≤ (applyDamageCounters pokemon n).damage := by
  simp [applyDamageCounters, Nat.le_add_right]

theorem applyDamageCounters_ko_of_enough (pokemon : PokemonInPlay) (n : Nat)
    (hEnough : pokemon.damage + n * damageCounterValue ≥ pokemon.card.hp) :
    isKnockedOut (applyDamageCounters pokemon n) = true := by
  simp [isKnockedOut, applyDamageCounters, damageCounterValue] at hEnough ⊢
  omega

-- ============================================================================
-- DAMAGE COUNTER VALUE THEOREMS
-- ============================================================================

theorem damage_is_counter_multiple (pokemon : PokemonInPlay)
    (hMul : pokemon.damage % damageCounterValue = 0) :
    pokemon.damage = damageCounters pokemon * damageCounterValue := by
  simp [damageCounters, damageCounterValue] at *
  omega

theorem place_then_remove_id (pokemon : PokemonInPlay) (n : Nat) :
    removeDamageCounters (placeDamageCounters pokemon n) n = pokemon := by
  cases pokemon
  simp [removeDamageCounters, placeDamageCounters, damageCounterValue]

theorem remove_then_place_ge (pokemon : PokemonInPlay) (n : Nat) :
    pokemon.damage ≤ (placeDamageCounters (removeDamageCounters pokemon n) n).damage := by
  simp [placeDamageCounters, removeDamageCounters, damageCounterValue]
  omega

-- ============================================================================
-- MAX DAMAGE COUNTERS THEOREMS
-- ============================================================================


theorem ko_if_counters_ge_max (pokemon : PokemonInPlay) (n : Nat)
    (hZero : pokemon.damage = 0)
    (hGe : n * damageCounterValue ≥ pokemon.card.hp) :
    isKnockedOut (placeDamageCounters pokemon n) = true := by
  simp [isKnockedOut, placeDamageCounters, damageCounterValue] at hGe ⊢
  omega

theorem not_ko_if_counters_lt_max (pokemon : PokemonInPlay) (n : Nat)
    (hZero : pokemon.damage = 0)
    (hLt : n * damageCounterValue < pokemon.card.hp) :
    isKnockedOut (placeDamageCounters pokemon n) = false := by
  simp [isKnockedOut, placeDamageCounters, damageCounterValue] at hLt ⊢
  omega

-- ============================================================================
-- HEAL THEN KO / KO THEN HEAL INTERACTION THEOREMS
-- ============================================================================

theorem heal_can_prevent_ko (pokemon : PokemonInPlay) (healAmount : Nat)
    (hNotTooMuch : pokemon.damage - healAmount < pokemon.card.hp) :
    isKnockedOut (healDamage pokemon healAmount) = false := by
  simp [isKnockedOut, healDamage]; omega

theorem heal_preserves_ko_if_not_enough (pokemon : PokemonInPlay) (healAmount : Nat)
    (hNotEnough : pokemon.damage - healAmount ≥ pokemon.card.hp) :
    isKnockedOut (healDamage pokemon healAmount) = true := by
  simp [isKnockedOut, healDamage, hNotEnough]

-- ============================================================================
-- COMPOSITE OPERATION THEOREMS
-- ============================================================================

theorem place_damage_monotone (pokemon : PokemonInPlay) (m n : Nat)
    (h : m ≤ n) :
    (placeDamageCounters pokemon m).damage ≤ (placeDamageCounters pokemon n).damage := by
  simp [placeDamageCounters, damageCounterValue]; omega

theorem heal_monotone (pokemon : PokemonInPlay) (m n : Nat)
    (h : m ≤ n) :
    (healDamage pokemon n).damage ≤ (healDamage pokemon m).damage := by
  simp [healDamage]; omega

theorem remainingHP_plus_damage_le_hp (pokemon : PokemonInPlay) :
    remainingHP pokemon + pokemon.damage ≥ pokemon.card.hp := by
  simp [remainingHP]; omega

theorem remainingHP_add_damage_eq_hp (pokemon : PokemonInPlay)
    (hBound : pokemon.damage ≤ pokemon.card.hp) :
    remainingHP pokemon + pokemon.damage = pokemon.card.hp := by
  simp [remainingHP]; omega

end PokemonLean.DamageCounters
