/-
  PokemonLean / AbilityInteractions.lean

  Complex ability interactions formalised in Lean 4.
  Covers: ability stacking rules, ability negation (Garbodor's Garbotoxin),
  ability copying (Ditto's Transform), weather-setting abilities,
  damage-modifying abilities (Intimidate), ability chaining (trigger order).

  All proofs are sorry-free.  Uses computational paths for state transitions.
-/

namespace PokemonLean.AbilityInteractions

-- ============================================================
-- §1  Core types
-- ============================================================

inductive PType where
  | fire | water | grass | electric | psychic | fighting
  | dark | metal | dragon | fairy | normal
  deriving DecidableEq, Repr

inductive Weather where
  | none | rain | sun | sandstorm | hail
  deriving DecidableEq, Repr

/-- Ability identifiers for interaction modelling. -/
inductive Ability where
  | garbotoxin       -- Garbodor: negate all other abilities while active with tool
  | transform        -- Ditto: copy opponent's ability
  | intimidate       -- On entry: reduce opponent damage by 20
  | drizzle          -- On entry: set rain
  | drought          -- On entry: set sun
  | sandStream       -- On entry: set sandstorm
  | snowWarning      -- On entry: set hail
  | beastBoost       -- On KO: boost highest stat
  | moldBreaker      -- Ignore target ability
  | neutralizingGas  -- Suppress all other abilities
  | multiscale       -- Halve damage at full HP
  | shadowTag        -- Prevent switching
  | trace            -- Copy opponent's ability on entry
  | imposter         -- Transform into opponent on entry
  | noAbility
  deriving DecidableEq, Repr

/-- Ability categories for stacking/interaction rules. -/
inductive AbilityCategory where
  | weatherSetter | damageModifier | entryTrigger
  | negation | copying | passive | switching
  deriving DecidableEq, Repr

def classifyAbility : Ability → AbilityCategory
  | .drizzle         => .weatherSetter
  | .drought         => .weatherSetter
  | .sandStream      => .weatherSetter
  | .snowWarning     => .weatherSetter
  | .intimidate      => .damageModifier
  | .multiscale      => .damageModifier
  | .beastBoost      => .entryTrigger
  | .garbotoxin      => .negation
  | .neutralizingGas => .negation
  | .moldBreaker     => .negation
  | .transform       => .copying
  | .trace           => .copying
  | .imposter        => .copying
  | .shadowTag       => .switching
  | .noAbility       => .passive

/-- Simple Pokémon structure for interactions. -/
structure Pokemon where
  name     : String
  ability  : Ability
  ptype    : PType
  hp       : Nat
  maxHp    : Nat
  damage   : Nat
  hasItem  : Bool   -- for Garbotoxin (needs tool attached)
  isActive : Bool
  deriving Repr

def Pokemon.currentHp (p : Pokemon) : Nat := p.maxHp - p.damage
def Pokemon.atFullHp (p : Pokemon) : Bool := p.damage == 0

-- ============================================================
-- §2  Game state
-- ============================================================

structure GameState where
  weather         : Weather
  playerActive    : Pokemon
  opponentActive  : Pokemon
  playerBench     : List Pokemon
  opponentBench   : List Pokemon
  damageModifier  : Int
  abilitiesLocked : Bool  -- global negation active
  turnCount       : Nat
  deriving Repr

-- ============================================================
-- §3  Computational paths infrastructure
-- ============================================================

inductive Step : GameState → GameState → Type where
  | weatherSet   : (gs : GameState) → (w : Weather) → Step gs { gs with weather := w }
  | intimidateApply : (gs : GameState) → Step gs { gs with damageModifier := gs.damageModifier - 20 }
  | garbotoxinOn : (gs : GameState) → Step gs { gs with abilitiesLocked := true }
  | garbotoxinOff : (gs : GameState) → Step gs { gs with abilitiesLocked := false }
  | transformCopy : (gs : GameState) → (a : Ability) →
      Step gs { gs with playerActive := { gs.playerActive with ability := a } }
  | multiscaleReduce : (gs : GameState) → (dmg : Nat) →
      Step gs { gs with opponentActive := { gs.opponentActive with damage := gs.opponentActive.damage + dmg / 2 } }
  | beastBoostTrigger : (gs : GameState) →
      Step gs { gs with damageModifier := gs.damageModifier + 10 }
  | advanceTurn : (gs : GameState) → Step gs { gs with turnCount := gs.turnCount + 1 }

inductive AbilPath : GameState → GameState → Type where
  | refl : (gs : GameState) → AbilPath gs gs
  | step : Step a b → AbilPath b c → AbilPath a c

def AbilPath.trans : AbilPath a b → AbilPath b c → AbilPath a c
  | .refl _, q => q
  | .step s p, q => .step s (p.trans q)

def AbilPath.single (s : Step a b) : AbilPath a b := .step s (.refl _)

def AbilPath.length : AbilPath a b → Nat
  | .refl _ => 0
  | .step _ p => 1 + p.length

def Step.symDesc : Step a b → String
  | .weatherSet _ w => s!"weatherSet→{repr w}"
  | .intimidateApply _ => "intimidateApply"
  | .garbotoxinOn _ => "garbotoxinOn"
  | .garbotoxinOff _ => "garbotoxinOff"
  | .transformCopy _ a => s!"transformCopy→{repr a}"
  | .multiscaleReduce _ d => s!"multiscale({d})"
  | .beastBoostTrigger _ => "beastBoost"
  | .advanceTurn _ => "advanceTurn"

-- ============================================================
-- §4  Ability negation: Garbotoxin
-- ============================================================

/-- Whether Garbotoxin is active: Garbodor with tool, active. -/
def garbotoxinActive (p : Pokemon) : Bool :=
  p.ability == .garbotoxin && p.hasItem && p.isActive

/-- Whether an ability is usable given game state. -/
def abilityUsable (gs : GameState) (p : Pokemon) : Bool :=
  if gs.abilitiesLocked then
    p.ability == .garbotoxin || p.ability == .neutralizingGas
  else
    true

/-- Theorem 1: Garbotoxin requires a tool. -/
theorem garbotoxin_needs_tool (p : Pokemon)
    (hab : p.ability = .garbotoxin) (hno : p.hasItem = false) :
    garbotoxinActive p = false := by
  simp [garbotoxinActive, hab, hno]

/-- Theorem 2: Garbotoxin requires being active. -/
theorem garbotoxin_needs_active (p : Pokemon)
    (hab : p.ability = .garbotoxin) (hna : p.isActive = false) :
    garbotoxinActive p = false := by
  simp [garbotoxinActive, hab, hna]

/-- Theorem 3: With Garbotoxin fully active, others are locked. -/
theorem garbotoxin_locks_others (gs : GameState)
    (hlocked : gs.abilitiesLocked = true) (p : Pokemon)
    (hne1 : p.ability ≠ .garbotoxin)
    (hne2 : p.ability ≠ .neutralizingGas) :
    abilityUsable gs p = false := by
  simp [abilityUsable, hlocked]
  exact ⟨hne1, hne2⟩

/-- Theorem 4: Garbotoxin itself remains usable under lock. -/
theorem garbotoxin_self_usable (gs : GameState) (p : Pokemon)
    (hab : p.ability = .garbotoxin) :
    abilityUsable gs p = true := by
  simp [abilityUsable]
  right; left; exact hab

-- ============================================================
-- §5  Ability copying: Transform / Trace / Imposter
-- ============================================================

/-- Ditto's Transform: copy the opponent's ability. -/
def applyTransform (gs : GameState) : GameState :=
  { gs with playerActive := { gs.playerActive with ability := gs.opponentActive.ability } }

/-- Theorem 5: Transform copies the opponent's ability. -/
theorem transform_copies_ability (gs : GameState) :
    (applyTransform gs).playerActive.ability = gs.opponentActive.ability := by
  simp [applyTransform]

/-- Theorem 6: Transform preserves player HP. -/
theorem transform_preserves_hp (gs : GameState) :
    (applyTransform gs).playerActive.hp = gs.playerActive.hp := by
  simp [applyTransform]

/-- Theorem 7: Transform doesn't change weather. -/
theorem transform_preserves_weather (gs : GameState) :
    (applyTransform gs).weather = gs.weather := by
  simp [applyTransform]

/-- Trace copies on entry – same mechanics as transform for our model. -/
def applyTrace := applyTransform

/-- Theorem 8: If opponent has no ability, transform gives noAbility. -/
theorem transform_no_ability (gs : GameState)
    (hna : gs.opponentActive.ability = .noAbility) :
    (applyTransform gs).playerActive.ability = .noAbility := by
  simp [applyTransform, hna]

-- ============================================================
-- §6  Weather-setting abilities
-- ============================================================

def applyWeatherAbility (gs : GameState) (p : Pokemon) : GameState :=
  match p.ability with
  | .drizzle    => { gs with weather := .rain }
  | .drought    => { gs with weather := .sun }
  | .sandStream => { gs with weather := .sandstorm }
  | .snowWarning => { gs with weather := .hail }
  | _ => gs

/-- Theorem 9: Drizzle sets rain. -/
theorem drizzle_sets_rain (gs : GameState) (p : Pokemon)
    (hab : p.ability = .drizzle) :
    (applyWeatherAbility gs p).weather = .rain := by
  simp [applyWeatherAbility, hab]

/-- Theorem 10: Drought sets sun. -/
theorem drought_sets_sun (gs : GameState) (p : Pokemon)
    (hab : p.ability = .drought) :
    (applyWeatherAbility gs p).weather = .sun := by
  simp [applyWeatherAbility, hab]

/-- Theorem 11: Weather ability of last entry wins (last writer wins). -/
theorem weather_last_writer_wins (gs : GameState) (p1 p2 : Pokemon)
    (h1 : p1.ability = .drizzle) (h2 : p2.ability = .drought) :
    (applyWeatherAbility (applyWeatherAbility gs p1) p2).weather = .sun := by
  simp [applyWeatherAbility, h1, h2]

/-- Theorem 12: Weather ability is idempotent (applying twice = once). -/
theorem weather_ability_idempotent (gs : GameState) (p : Pokemon)
    (hab : p.ability = .drizzle) :
    applyWeatherAbility (applyWeatherAbility gs p) p =
    applyWeatherAbility gs p := by
  simp [applyWeatherAbility, hab]

-- ============================================================
-- §7  Damage-modifying abilities: Intimidate, Multiscale
-- ============================================================

def applyIntimidate (gs : GameState) : GameState :=
  { gs with damageModifier := gs.damageModifier - 20 }

/-- Theorem 13: Intimidate reduces damage modifier by 20. -/
theorem intimidate_reduces (gs : GameState) :
    (applyIntimidate gs).damageModifier = gs.damageModifier - 20 := by
  simp [applyIntimidate]

/-- Multiscale halves damage at full HP. -/
def multiscaleDamage (p : Pokemon) (baseDmg : Nat) : Nat :=
  if p.ability == .multiscale && p.atFullHp then baseDmg / 2 else baseDmg

/-- Theorem 14: Multiscale at full HP halves damage. -/
theorem multiscale_halves (p : Pokemon) (d : Nat)
    (hab : p.ability = .multiscale) (hfull : p.atFullHp = true) :
    multiscaleDamage p d = d / 2 := by
  simp [multiscaleDamage, hab, hfull]

/-- Theorem 15: Multiscale not at full HP does nothing. -/
theorem multiscale_not_full (p : Pokemon) (d : Nat)
    (hab : p.ability = .multiscale) (hnotfull : p.atFullHp = false) :
    multiscaleDamage p d = d := by
  simp [multiscaleDamage, hab, hnotfull]

-- ============================================================
-- §8  Ability chaining: trigger order
-- ============================================================

/-- Priority for ability resolution order. -/
def abilityPriority : Ability → Nat
  | .neutralizingGas => 100
  | .garbotoxin      => 95
  | .moldBreaker     => 90
  | .intimidate      => 50
  | .drizzle         => 40
  | .drought         => 40
  | .sandStream      => 40
  | .snowWarning     => 40
  | .beastBoost      => 30
  | .multiscale      => 20
  | .shadowTag       => 15
  | .transform       => 10
  | .trace           => 10
  | .imposter        => 10
  | .noAbility       => 0

/-- Theorem 16: Negation abilities always resolve before others. -/
theorem negation_resolves_first (a : Ability)
    (hcat : classifyAbility a ≠ .negation) :
    abilityPriority a ≤ abilityPriority .garbotoxin := by
  cases a <;> simp_all [classifyAbility, abilityPriority] <;> omega

/-- Theorem 17: NeutralizingGas has highest priority of all. -/
theorem neutralizing_gas_max (a : Ability) :
    abilityPriority a ≤ abilityPriority .neutralizingGas := by
  cases a <;> simp [abilityPriority] <;> omega

/-- Theorem 18: All weather setters have equal priority. -/
theorem weather_setters_equal_priority :
    abilityPriority .drizzle = abilityPriority .drought ∧
    abilityPriority .drought = abilityPriority .sandStream ∧
    abilityPriority .sandStream = abilityPriority .snowWarning := by
  simp [abilityPriority]

-- ============================================================
-- §9  Ability stacking rules
-- ============================================================

/-- Two abilities stack if they're in different categories. -/
def abilitiesStack (a1 a2 : Ability) : Bool :=
  classifyAbility a1 != classifyAbility a2

/-- Theorem 19: Intimidate and Drizzle stack (different categories). -/
theorem intimidate_drizzle_stack :
    abilitiesStack .intimidate .drizzle = true := by
  simp [abilitiesStack, classifyAbility]

/-- Theorem 20: Two weather setters don't stack. -/
theorem weather_setters_dont_stack :
    abilitiesStack .drizzle .drought = false := by
  simp [abilitiesStack, classifyAbility]

/-- Theorem 21: Negation and damage modifier stack. -/
theorem negation_damage_stack :
    abilitiesStack .garbotoxin .intimidate = true := by
  simp [abilitiesStack, classifyAbility]

-- ============================================================
-- §10  Path-based interaction sequences
-- ============================================================

/-- Build a weather → intimidate chain. -/
def weatherThenIntimidate (gs : GameState) :
    AbilPath gs { { gs with weather := .rain } with damageModifier := gs.damageModifier - 20 } :=
  .step (.weatherSet gs .rain)
    (.single (.intimidateApply { gs with weather := .rain }))

/-- Theorem 22: Weather-then-intimidate is a 2-step path. -/
theorem weather_intimidate_length (gs : GameState) :
    (weatherThenIntimidate gs).length = 2 := rfl

/-- Build a Garbotoxin-on → turn advance chain. -/
def lockThenAdvance (gs : GameState) :
    AbilPath gs { { gs with abilitiesLocked := true } with turnCount := gs.turnCount + 1 } :=
  .step (.garbotoxinOn gs)
    (.single (.advanceTurn { gs with abilitiesLocked := true }))

/-- Theorem 23: Lock-then-advance is a 2-step path. -/
theorem lock_advance_length (gs : GameState) :
    (lockThenAdvance gs).length = 2 := rfl

-- ============================================================
-- §11  Transport along ability paths
-- ============================================================

/-- Transport a property along an ability path. -/
def transportAbilPath {P : GameState → Prop}
    (preserve : ∀ a b, Step a b → P a → P b)
    {a b : GameState} (path : AbilPath a b) (pa : P a) : P b := by
  induction path with
  | refl _ => exact pa
  | step s _ ih => exact ih (preserve _ _ s pa)

/-- Theorem 24: Transport along refl is identity. -/
theorem transport_refl {P : GameState → Prop}
    (preserve : ∀ a b, Step a b → P a → P b)
    (gs : GameState) (pa : P gs) :
    transportAbilPath preserve (.refl gs) pa = pa := rfl

theorem abilPath_length_trans : (p : AbilPath a b) → (q : AbilPath b c) →
    (p.trans q).length = p.length + q.length
  | .refl _, q => by simp [AbilPath.trans, AbilPath.length]
  | .step _ p, q => by
    simp [AbilPath.trans, AbilPath.length]; rw [abilPath_length_trans p q]; omega

/-- Theorem 25: Trans with refl is identity. -/
theorem abilPath_trans_refl : (p : AbilPath a b) → p.trans (.refl b) = p
  | .refl _ => rfl
  | .step s p => by
    show AbilPath.step s (p.trans (.refl _)) = AbilPath.step s p
    rw [abilPath_trans_refl p]

/-- Theorem 26: Trans is associative. -/
theorem abilPath_trans_assoc : (p : AbilPath a b) → (q : AbilPath b c) → (r : AbilPath c d) →
    (p.trans q).trans r = p.trans (q.trans r)
  | .refl _, _, _ => rfl
  | .step s p, q, r => by
    show AbilPath.step s ((p.trans q).trans r) = AbilPath.step s (p.trans (q.trans r))
    rw [abilPath_trans_assoc p q r]

-- ============================================================
-- §12  MoldBreaker interaction
-- ============================================================

/-- Mold Breaker lets an attacker ignore a defender's ability. -/
def moldBreakerIgnores (attacker defender : Pokemon) (baseDmg : Nat) : Nat :=
  if attacker.ability == .moldBreaker then
    baseDmg  -- ignore defender's damage reduction
  else
    multiscaleDamage defender baseDmg

/-- Theorem 27: Mold Breaker ignores Multiscale. -/
theorem mold_breaker_ignores_multiscale (atk def_ : Pokemon) (d : Nat)
    (hmb : atk.ability = .moldBreaker)
    (hms : def_.ability = .multiscale) (hfull : def_.atFullHp = true) :
    moldBreakerIgnores atk def_ d = d := by
  simp [moldBreakerIgnores, hmb]

/-- Theorem 28: Without Mold Breaker, Multiscale applies at full HP. -/
theorem no_mold_breaker_multiscale_applies (atk def_ : Pokemon) (d : Nat)
    (hnmb : atk.ability ≠ .moldBreaker)
    (hms : def_.ability = .multiscale) (hfull : def_.atFullHp = true) :
    moldBreakerIgnores atk def_ d = d / 2 := by
  simp [moldBreakerIgnores]
  split
  · next h => exact absurd h hnmb
  · simp [multiscaleDamage, hms, hfull]

end PokemonLean.AbilityInteractions
