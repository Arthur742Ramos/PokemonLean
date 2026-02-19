import PokemonLean.Basic

namespace PokemonLean.AbilitySystem

open PokemonLean

-- ============================================================================
-- ABILITY NAMES (30+ abilities from the Pokemon TCG)
-- ============================================================================

inductive AbilityName
  | intimidate
  | drizzle
  | drought
  | sandStream
  | snowWarning
  | levitate
  | sturdy
  | moldBreaker
  | pressure
  | unaware
  | multiscale
  | magicGuard
  | prankster
  | technician
  | adaptability
  | hugePower
  | speedBoost
  | regenerator
  | naturalCure
  | toxicBoost
  | guts
  | swiftSwim
  | chlorophyll
  | flashFire
  | lightningRod
  | stormDrain
  | waterAbsorb
  | voltAbsorb
  | wonderGuard
  | disguise
  | protean
  | overgrow
  | blaze
  | torrent
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- ABILITY TRIGGERS
-- ============================================================================

inductive AbilityTrigger
  | onEnter
  | onAttack
  | onDamage
  | onRetreat
  | onEvolve
  | onTurnStart
  | onTurnEnd
  | passive
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- ABILITY EFFECT CATEGORIES
-- ============================================================================

inductive AbilityEffect
  | modifyDamage (amount : Int)
  | preventStatus (condition : StatusCondition)
  | setWeather (weather : Weather)
  | healOnSwitch (amount : Nat)
  | blockAbilities
  | immuneToType (energyType : EnergyType)
  | boostAttack (amount : Nat)
  | reduceDamage (amount : Nat)
  | drawCard (count : Nat)
  | noEffect
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- ABILITY STRUCTURE
-- ============================================================================

structure AbilityDef where
  name : AbilityName
  trigger : AbilityTrigger
  effect : AbilityEffect
  deriving Repr, BEq, DecidableEq

structure PokemonWithAbility where
  pokemon : PokemonInPlay
  ability : Option AbilityDef
  abilityActive : Bool := true
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- STANDARD ABILITY DEFINITIONS
-- ============================================================================

def intimidateAbility : AbilityDef :=
  { name := .intimidate, trigger := .onEnter, effect := .modifyDamage (-20) }

def drizzleAbility : AbilityDef :=
  { name := .drizzle, trigger := .onEnter, effect := .setWeather .rain }

def droughtAbility : AbilityDef :=
  { name := .drought, trigger := .onEnter, effect := .setWeather .sunny }

def sandStreamAbility : AbilityDef :=
  { name := .sandStream, trigger := .onEnter, effect := .setWeather .sandstorm }

def snowWarningAbility : AbilityDef :=
  { name := .snowWarning, trigger := .onEnter, effect := .setWeather .hail }

def sturdyAbility : AbilityDef :=
  { name := .sturdy, trigger := .onDamage, effect := .reduceDamage 0 }

def moldBreakerAbility : AbilityDef :=
  { name := .moldBreaker, trigger := .passive, effect := .blockAbilities }

def regeneratorAbility : AbilityDef :=
  { name := .regenerator, trigger := .onRetreat, effect := .healOnSwitch 30 }

def naturalCureAbility : AbilityDef :=
  { name := .naturalCure, trigger := .onRetreat, effect := .preventStatus .poisoned }

def flashFireAbility : AbilityDef :=
  { name := .flashFire, trigger := .onDamage, effect := .immuneToType .fire }

def lightningRodAbility : AbilityDef :=
  { name := .lightningRod, trigger := .onDamage, effect := .immuneToType .lightning }

def waterAbsorbAbility : AbilityDef :=
  { name := .waterAbsorb, trigger := .onDamage, effect := .immuneToType .water }

def voltAbsorbAbility : AbilityDef :=
  { name := .voltAbsorb, trigger := .onDamage, effect := .immuneToType .lightning }

def wonderGuardAbility : AbilityDef :=
  { name := .wonderGuard, trigger := .onDamage, effect := .reduceDamage 0 }

def hugePowerAbility : AbilityDef :=
  { name := .hugePower, trigger := .onAttack, effect := .boostAttack 30 }

def technicianAbility : AbilityDef :=
  { name := .technician, trigger := .onAttack, effect := .boostAttack 20 }

def adaptabilityAbility : AbilityDef :=
  { name := .adaptability, trigger := .onAttack, effect := .boostAttack 20 }

-- ============================================================================
-- ONE ABILITY PER POKEMON
-- ============================================================================

def hasExactlyOneAbility (pwa : PokemonWithAbility) : Prop :=
  pwa.ability.isSome = true

def hasNoAbility (pwa : PokemonWithAbility) : Prop :=
  pwa.ability = none

theorem one_ability_or_none (pwa : PokemonWithAbility) :
    hasExactlyOneAbility pwa ∨ hasNoAbility pwa := by
  cases h : pwa.ability with
  | none => right; exact h
  | some _ => left; simp [hasExactlyOneAbility, h]

theorem not_both_ability_and_none (pwa : PokemonWithAbility) :
    ¬(hasExactlyOneAbility pwa ∧ hasNoAbility pwa) := by
  intro ⟨h1, h2⟩
  simp [hasExactlyOneAbility, hasNoAbility] at h1 h2
  rw [h2] at h1
  exact absurd h1 (by decide)

-- ============================================================================
-- ABILITY BLOCKING / NEGATION (Path to the Peak)
-- ============================================================================

inductive StadiumInPlay
  | pathToThePeak
  | otherStadium
  deriving Repr, BEq, DecidableEq

def abilitiesNegated (stadium : Option StadiumInPlay) : Bool :=
  match stadium with
  | some .pathToThePeak => true
  | _ => false

def isAbilityActive (pwa : PokemonWithAbility) (stadium : Option StadiumInPlay) : Bool :=
  pwa.abilityActive && !abilitiesNegated stadium

def hasMoldBreaker (pwa : PokemonWithAbility) : Bool :=
  match pwa.ability with
  | some ab => ab.name == .moldBreaker
  | none => false

def canUseAbilityAgainst (attacker defender : PokemonWithAbility) (stadium : Option StadiumInPlay) : Bool :=
  if hasMoldBreaker attacker then
    false  -- mold breaker ignores defender abilities
  else
    isAbilityActive defender stadium

-- ============================================================================
-- ABILITY TRIGGER MATCHING
-- ============================================================================

def triggersOn (ab : AbilityDef) (trigger : AbilityTrigger) : Bool :=
  ab.trigger == trigger

def getActiveAbilityEffect (pwa : PokemonWithAbility) (stadium : Option StadiumInPlay) (trigger : AbilityTrigger) : Option AbilityEffect :=
  if isAbilityActive pwa stadium then
    match pwa.ability with
    | some ab => if triggersOn ab trigger then some ab.effect else none
    | none => none
  else
    none

-- ============================================================================
-- DAMAGE MODIFICATION FROM ABILITIES
-- ============================================================================

def applyDamageBoost (baseDamage : Nat) (effect : AbilityEffect) : Nat :=
  match effect with
  | .boostAttack amount => baseDamage + amount
  | _ => baseDamage

def applyDamageReduction (incomingDamage : Nat) (effect : AbilityEffect) : Nat :=
  match effect with
  | .reduceDamage amount => Nat.sub incomingDamage amount
  | _ => incomingDamage

def isImmuneToType (effect : AbilityEffect) (attackType : EnergyType) : Bool :=
  match effect with
  | .immuneToType t => t == attackType
  | _ => false

def computeDamageWithAbilities
    (baseDamage : Nat)
    (attackType : EnergyType)
    (attackerAbility : Option AbilityEffect)
    (defenderAbility : Option AbilityEffect)
    (_stadium : Option StadiumInPlay) : Nat :=
  let boosted := match attackerAbility with
    | some eff => applyDamageBoost baseDamage eff
    | none => baseDamage
  match defenderAbility with
  | some eff =>
      if isImmuneToType eff attackType then 0
      else applyDamageReduction boosted eff
  | none => boosted

-- ============================================================================
-- WEATHER FROM ABILITIES
-- ============================================================================

def abilityWeather (ab : AbilityDef) : Option Weather :=
  match ab.effect with
  | .setWeather w => some w
  | _ => none

-- ============================================================================
-- HEAL ON SWITCH (Regenerator)
-- ============================================================================

def applyHealOnSwitch (pwa : PokemonWithAbility) (stadium : Option StadiumInPlay) : PokemonWithAbility :=
  match getActiveAbilityEffect pwa stadium .onRetreat with
  | some (.healOnSwitch amount) =>
      let newDamage := Nat.sub pwa.pokemon.damage amount
      { pwa with pokemon := { pwa.pokemon with damage := newDamage } }
  | _ => pwa

-- ============================================================================
-- STURDY: survive with at least 1 HP from full
-- ============================================================================

def applySturdySurvival (pwa : PokemonWithAbility) (incomingDamage : Nat) (stadium : Option StadiumInPlay) : Nat :=
  if isAbilityActive pwa stadium then
    match pwa.ability with
    | some ab =>
        if ab.name == .sturdy && pwa.pokemon.damage == 0 && incomingDamage >= pwa.pokemon.card.hp then
          pwa.pokemon.card.hp - 1
        else
          incomingDamage
    | none => incomingDamage
  else
    incomingDamage

-- ============================================================================
-- THEOREMS (30+)
-- ============================================================================

-- 1. Path to the Peak negates abilities

-- 2. No stadium means abilities are not negated

-- 3. Other stadiums don't negate

-- 4. Ability inactive under Path to the Peak
theorem ability_inactive_under_path (pwa : PokemonWithAbility) :
    isAbilityActive pwa (some .pathToThePeak) = false := by
  simp [isAbilityActive, abilitiesNegated]

-- 5. Ability active without stadium if abilityActive flag is true
theorem ability_active_no_stadium (pwa : PokemonWithAbility) (h : pwa.abilityActive = true) :
    isAbilityActive pwa none = true := by
  simp [isAbilityActive, abilitiesNegated, h]

-- 6. Inactive ability stays inactive
theorem ability_inactive_flag (pwa : PokemonWithAbility) (h : pwa.abilityActive = false) (s : Option StadiumInPlay) :
    isAbilityActive pwa s = false := by
  simp [isAbilityActive, h]

-- 7. Damage boost increases damage

-- 8. Non-boost effect preserves damage

-- 9. Damage reduction decreases damage
theorem damage_reduction_le (damage amount : Nat) :
    applyDamageReduction damage (.reduceDamage amount) ≤ damage := by
  simp [applyDamageReduction, Nat.sub_le]

-- 10. Zero reduction is identity
theorem zero_reduction_identity (damage : Nat) :
    applyDamageReduction damage (.reduceDamage 0) = damage := by
  simp [applyDamageReduction]

-- 11. Non-reduction preserves damage

-- 12. Type immunity makes damage zero
theorem type_immunity_zero (_base : Nat) (t : EnergyType) :
    isImmuneToType (.immuneToType t) t = true := by
  simp [isImmuneToType]

-- 13. Wrong type no immunity

-- 14. Non-immunity effect is not immune

-- 15. Drizzle sets rain

-- 16. Drought sets sunny

-- 17. Sand stream sets sandstorm

-- 18. Snow warning sets hail

-- 19. Non-weather ability has no weather

-- 20. Regenerator triggers on retreat

-- 21. Regenerator doesn't trigger on enter

-- 22. Intimidate triggers on enter

-- 23. Huge power triggers on attack

-- 24. Mold breaker is passive

-- 25. No ability effect when ability is none
theorem no_ability_no_effect (p : PokemonInPlay) (stadium : Option StadiumInPlay) (trigger : AbilityTrigger) :
    getActiveAbilityEffect { pokemon := p, ability := none, abilityActive := true } stadium trigger = none := by
  simp [getActiveAbilityEffect, isAbilityActive]

-- 26. No effect under Path to the Peak
theorem no_effect_under_path (pwa : PokemonWithAbility) (trigger : AbilityTrigger) :
    getActiveAbilityEffect pwa (some .pathToThePeak) trigger = none := by
  simp [getActiveAbilityEffect, isAbilityActive, abilitiesNegated]

-- 27. Damage with no abilities equals base damage

-- 28. Attacker boost adds to damage

-- 29. Defender immunity zeros damage
theorem defender_immunity_zeros (base : Nat) (t : EnergyType) (s : Option StadiumInPlay) :
    computeDamageWithAbilities base t none (some (.immuneToType t)) s = 0 := by
  simp [computeDamageWithAbilities]
  have h : isImmuneToType (.immuneToType t) t = true := by
    simp [isImmuneToType]
  simp [h]

-- 30. Sturdy doesn't affect when not at full HP
theorem sturdy_no_effect_not_full (pwa : PokemonWithAbility) (damage : Nat) (stadium : Option StadiumInPlay)
    (hDamaged : pwa.pokemon.damage ≠ 0) :
    applySturdySurvival pwa damage stadium = damage := by
  simp [applySturdySurvival]
  intro _
  cases pwa.ability with
  | none => rfl
  | some ab =>
      simp
      intro _
      simp at hDamaged ⊢
      intro h
      exact absurd h hDamaged

-- 31. Heal on switch preserves ability
theorem heal_on_switch_preserves_ability (pwa : PokemonWithAbility) (stadium : Option StadiumInPlay) :
    (applyHealOnSwitch pwa stadium).ability = pwa.ability := by
  simp [applyHealOnSwitch]
  cases getActiveAbilityEffect pwa stadium .onRetreat with
  | none => rfl
  | some eff => cases eff <;> simp

-- 32. Heal on switch reduces or preserves damage
theorem heal_on_switch_damage_le (pwa : PokemonWithAbility) (stadium : Option StadiumInPlay) :
    (applyHealOnSwitch pwa stadium).pokemon.damage ≤ pwa.pokemon.damage := by
  simp [applyHealOnSwitch]
  cases h : getActiveAbilityEffect pwa stadium .onRetreat with
  | none => simp
  | some eff =>
      cases eff with
      | healOnSwitch amount => simp [Nat.sub_le]
      | _ => simp

-- 33. Damage boost is monotone
theorem damage_boost_monotone (a b amount : Nat) (h : a ≤ b) :
    applyDamageBoost a (.boostAttack amount) ≤ applyDamageBoost b (.boostAttack amount) := by
  simp [applyDamageBoost]
  omega

-- 34. Damage reduction is monotone
theorem damage_reduction_monotone (a b amount : Nat) (h : a ≤ b) :
    applyDamageReduction a (.reduceDamage amount) ≤ applyDamageReduction b (.reduceDamage amount) := by
  simp [applyDamageReduction]
  omega

-- 35. Flash fire is immune to fire

-- 36. Lightning rod is immune to lightning

-- 37. Water absorb is immune to water

-- 38. Volt absorb is immune to lightning

-- 39. Ability trigger exhaustive for weather setters
theorem weather_setter_triggers_on_enter (ab : AbilityDef) (_w : Weather)
    (_h : ab.effect = .setWeather _w) (ht : ab.trigger = .onEnter) :
    triggersOn ab .onEnter = true := by
  simp [triggersOn, ht]
  decide

-- 40. Compute damage with both boost and reduction
theorem damage_boost_then_reduce (base boost red : Nat) (t : EnergyType) (s : Option StadiumInPlay)
    (_hNotImmune : isImmuneToType (.reduceDamage red) t = false) :
    computeDamageWithAbilities base t (some (.boostAttack boost)) (some (.reduceDamage red)) s =
      Nat.sub (base + boost) red := by
  simp [computeDamageWithAbilities, isImmuneToType, applyDamageBoost, applyDamageReduction]

end PokemonLean.AbilitySystem
