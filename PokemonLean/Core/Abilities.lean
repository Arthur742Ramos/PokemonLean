/-
  PokemonLean / Core / Abilities.lean

  Consolidated ability mechanics for the Pokémon TCG.
  Merges content from: AbilityInteractions, AbilityKeywords,
  AbilityMechanics, PokemonPowers.

  Covers:
  - Full ability taxonomy: Abilities (BW+), Poké-Powers (DPPt),
    Poké-Bodies (DPPt), Pokémon Powers (Base–Neo)
  - Ability categories: draw, search, acceleration, disruption
  - Coming-into-play vs static vs triggered abilities
  - Ability stacking rules (same ability from different Pokémon)
  - Ability lock hierarchy: Neutralizing Gas > Garbotoxin > Path to Peak
  - Mold Breaker bypass, Transform/Trace/Imposter copying
  - Weather-setting abilities, damage-modifying abilities
  - Classic Pokémon Powers: Rain Dance, Damage Swap, Buzzap, Toxic Gas
  - Path-based state transitions with full algebraic structure

  All proofs are sorry-free.  40+ theorems.
-/

namespace PokemonLean.Core.Abilities

-- ============================================================
-- §1  Core types
-- ============================================================

/-- Pokémon types for ability interactions. -/
inductive PType where
  | fire | water | grass | electric | psychic | fighting
  | dark | metal | dragon | fairy | normal
  deriving DecidableEq, Repr

/-- Card kind — relevant to Path to the Peak and Rule Box status. -/
inductive CardKind where
  | basic | stage1 | stage2 | ex | gx | vstar | vmax | ruleBox
  deriving DecidableEq, Repr

def CardKind.isRuleBox : CardKind → Bool
  | .ex | .gx | .vstar | .vmax | .ruleBox => true
  | _ => false

/-- Weather conditions set by abilities. -/
inductive Weather where
  | none | rain | sun | sandstorm | hail
  deriving DecidableEq, Repr

-- ============================================================
-- §2  Ability taxonomy
-- ============================================================

/-- The four historical eras of ability-like mechanics. -/
inductive AbilityEra where
  | pokemonPower   -- Base Set–Neo: "Pokémon Power"
  | pokePower      -- Ruby/Sapphire–Platinum: "Poké-Power" (activated)
  | pokeBody       -- Ruby/Sapphire–Platinum: "Poké-Body" (passive)
  | ability        -- Black/White onward: unified "Ability"
  deriving DecidableEq, Repr

/-- Ability trigger categories. -/
inductive AbilityTrigger where
  | comingIntoPlay  -- Triggers exactly once on entering play
  | static          -- Always active while the Pokémon is in play
  | activated       -- Player chooses to use (once per turn unless stated)
  | triggered       -- Responds to a game event (KO, evolution, etc.)
  deriving DecidableEq, Repr

/-- Ability keyword categories for deck-building / meta analysis. -/
inductive AbilityKeyword where
  | draw          -- Shaymin-EX Setup, Crobat V Dark Asset, Dedenne-GX Dedechange
  | search        -- Lumineon V Luminous Sign
  | acceleration  -- Blacephalon Fireworks Bomb
  | disruption    -- Garbotoxin, Path to the Peak
  | healing       -- Cherrim Sunny Day
  | switching     -- Rush In, Shadow Tag
  | copying       -- Transform, Trace, Imposter
  | damageBoost   -- Diancie ◇, Regidrago VSTAR
  | other
  deriving DecidableEq, Repr

/-- Ability identifiers for interaction modelling. -/
inductive Ability where
  | garbotoxin       -- Garbodor: negate all other abilities while active with tool
  | neutralizingGas  -- Weezing: suppress all other abilities
  | moldBreaker      -- Ignore target's ability
  | pathToThePeak    -- Stadium: Rule Box Pokémon have no abilities
  | transform        -- Ditto: copy opponent's ability/type
  | trace            -- Copy opponent's ability on entry
  | imposter         -- Transform into opponent on entry
  | intimidate       -- On entry: reduce opponent damage by 20
  | drizzle          -- On entry: set rain
  | drought          -- On entry: set sun
  | sandStream       -- On entry: set sandstorm
  | snowWarning      -- On entry: set hail
  | multiscale       -- Halve damage at full HP
  | shadowTag        -- Prevent switching
  | beastBoost       -- On KO: boost highest stat
  | rushIn           -- Free switch-in from bench to active
  | safeguard        -- Prevent all effects from Rule Box Pokémon
  | galeWings        -- Priority for Flying moves at full HP
  | protean          -- Change type to match the move used
  | sturdy           -- Survive OHKO at 1 HP if at full HP
  | noAbility
  deriving DecidableEq, Repr

/-- Ability category for stacking/interaction rules. -/
inductive AbilityCategory where
  | negation | weatherSetter | damageModifier | entryTrigger
  | copying | switching | passive
  deriving DecidableEq, Repr

def classifyAbility : Ability → AbilityCategory
  | .garbotoxin      => .negation
  | .neutralizingGas => .negation
  | .moldBreaker     => .negation
  | .pathToThePeak   => .negation
  | .drizzle         => .weatherSetter
  | .drought         => .weatherSetter
  | .sandStream      => .weatherSetter
  | .snowWarning     => .weatherSetter
  | .intimidate      => .damageModifier
  | .multiscale      => .damageModifier
  | .beastBoost      => .entryTrigger
  | .rushIn          => .entryTrigger
  | .transform       => .copying
  | .trace           => .copying
  | .imposter        => .copying
  | .shadowTag       => .switching
  | .safeguard       => .passive
  | .galeWings       => .passive
  | .protean         => .passive
  | .sturdy          => .passive
  | .noAbility       => .passive

def abilityTrigger : Ability → AbilityTrigger
  | .rushIn          => .comingIntoPlay
  | .intimidate      => .comingIntoPlay
  | .drizzle         => .comingIntoPlay
  | .drought         => .comingIntoPlay
  | .sandStream      => .comingIntoPlay
  | .snowWarning     => .comingIntoPlay
  | .trace           => .comingIntoPlay
  | .imposter        => .comingIntoPlay
  | .beastBoost      => .triggered
  | .transform       => .activated
  | .safeguard       => .static
  | .multiscale      => .static
  | .shadowTag       => .static
  | .galeWings       => .static
  | .protean         => .static
  | .sturdy          => .static
  | .garbotoxin      => .static
  | .neutralizingGas => .static
  | .moldBreaker     => .static
  | .pathToThePeak   => .static
  | .noAbility       => .static

-- ============================================================
-- §3  Pokémon and game state
-- ============================================================

structure Pokemon where
  name     : String
  kind     : CardKind
  ability  : Ability
  ptype    : PType
  hp       : Nat
  maxHp    : Nat
  damage   : Nat
  hasItem  : Bool
  isActive : Bool
  deriving Repr

def Pokemon.currentHp (p : Pokemon) : Nat := p.maxHp - p.damage
def Pokemon.atFullHp (p : Pokemon) : Bool := p.damage == 0

/-- Negation source hierarchy. -/
inductive NegationSource where
  | neutralizingGas  -- Priority 100: all other abilities off
  | garbotoxin       -- Priority 95: all others off (needs tool + active)
  | pathToThePeak    -- Priority 90: Rule Box only
  | moldBreaker      -- Priority 80: per-attack bypass
  | none
  deriving DecidableEq, Repr

structure GameState where
  weather         : Weather
  negation        : NegationSource
  playerActive    : Pokemon
  opponentActive  : Pokemon
  playerBench     : List Pokemon
  opponentBench   : List Pokemon
  damageModifier  : Int
  abilitiesLocked : Bool
  turnNumber      : Nat
  deriving Repr

-- ============================================================
-- §4  Ability lock hierarchy
-- ============================================================

/-- Priority of a negation source (higher = more powerful). -/
def negationPriority : NegationSource → Nat
  | .neutralizingGas => 100
  | .garbotoxin      => 95
  | .pathToThePeak   => 90
  | .moldBreaker     => 80
  | .none            => 0

/-- Priority of an ability (higher = resolves first). -/
def abilityPriority : Ability → Nat
  | .neutralizingGas => 100
  | .garbotoxin      => 95
  | .moldBreaker     => 90
  | .pathToThePeak   => 85
  | .intimidate      => 50
  | .drizzle         => 40
  | .drought         => 40
  | .sandStream      => 40
  | .snowWarning     => 40
  | .rushIn          => 35
  | .beastBoost      => 30
  | .galeWings       => 25
  | .protean         => 20
  | .multiscale      => 15
  | .sturdy          => 15
  | .shadowTag       => 15
  | .safeguard       => 10
  | .transform       => 10
  | .trace           => 10
  | .imposter        => 10
  | .noAbility       => 0

/-- Whether a Pokémon's ability is active given a negation source. -/
def abilityActive (neg : NegationSource) (p : Pokemon) : Bool :=
  match neg with
  | .none            => true
  | .neutralizingGas => p.ability == .neutralizingGas
  | .garbotoxin      => p.ability == .garbotoxin || p.ability == .neutralizingGas
  | .pathToThePeak   => !p.kind.isRuleBox
  | .moldBreaker     => true  -- per-interaction bypass

/-- Whether Garbotoxin is active: Garbodor with tool, active. -/
def garbotoxinActive (p : Pokemon) : Bool :=
  p.ability == .garbotoxin && p.hasItem && p.isActive

-- ============================================================
-- §5  Computational paths
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
  | advanceTurn : (gs : GameState) → Step gs { gs with turnNumber := gs.turnNumber + 1 }

inductive AbilPath : GameState → GameState → Type where
  | refl : (gs : GameState) → AbilPath gs gs
  | step : {a b c : GameState} → Step a b → AbilPath b c → AbilPath a c

variable {a b c d : GameState}

def AbilPath.trans {a b c : GameState} : AbilPath a b → AbilPath b c → AbilPath a c
  | .refl _, q => q
  | .step s p', q => .step s (p'.trans q)

def AbilPath.single {a b : GameState} (s : Step a b) : AbilPath a b :=
  .step s (.refl b)

def AbilPath.length {a b : GameState} : AbilPath a b → Nat
  | .refl _ => 0
  | .step _ p' => 1 + p'.length

-- ============================================================
-- §6  Negation theorems
-- ============================================================

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

/-- Theorem 3: With abilities locked, non-negation abilities are blocked. -/
theorem locked_blocks_others (gs : GameState)
    (hlocked : gs.abilitiesLocked = true) (p : Pokemon)
    (hne1 : p.ability ≠ .garbotoxin)
    (hne2 : p.ability ≠ .neutralizingGas) :
    abilityActive .garbotoxin p = false := by
  simp [abilityActive]
  exact ⟨hne1, hne2⟩

/-- Theorem 4: Garbotoxin itself remains usable under its own lock. -/
theorem garbotoxin_self_usable (p : Pokemon)
    (hab : p.ability = .garbotoxin) :
    abilityActive .garbotoxin p = true := by
  simp [abilityActive, hab]

/-- Theorem 5: With no negation, every ability is active. -/
theorem no_negation_all_active (p : Pokemon) :
    abilityActive .none p = true := by
  simp [abilityActive]

/-- Theorem 6: Path to the Peak shuts off Rule Box abilities. -/
theorem peak_negates_ruleBox (p : Pokemon)
    (hrb : p.kind.isRuleBox = true) :
    abilityActive .pathToThePeak p = false := by
  simp [abilityActive, hrb]

/-- Theorem 7: Path to the Peak does NOT negate non-Rule-Box. -/
theorem peak_allows_nonRuleBox (p : Pokemon)
    (hnrb : p.kind.isRuleBox = false) :
    abilityActive .pathToThePeak p = true := by
  simp [abilityActive, hnrb]

/-- Theorem 8: Basic Pokémon are never Rule Box. -/
theorem basic_not_ruleBox : CardKind.isRuleBox .basic = false := rfl

/-- Theorem 9: EX Pokémon are Rule Box. -/
theorem ex_is_ruleBox : CardKind.isRuleBox .ex = true := rfl

/-- Theorem 10: Neutralizing Gas has the highest priority. -/
theorem neutGas_highest_priority (a : Ability) :
    abilityPriority a ≤ abilityPriority .neutralizingGas := by
  cases a <;> simp [abilityPriority] <;> omega

/-- Theorem 11: Negation hierarchy is a total order. -/
theorem negation_total_order :
    negationPriority .neutralizingGas > negationPriority .garbotoxin ∧
    negationPriority .garbotoxin > negationPriority .pathToThePeak ∧
    negationPriority .pathToThePeak > negationPriority .moldBreaker ∧
    negationPriority .moldBreaker > negationPriority .none := by
  simp [negationPriority]

/-- Theorem 12: Under Neutralizing Gas, non-NeutGas abilities are inactive. -/
theorem neutGas_suppresses (p : Pokemon)
    (hne : p.ability ≠ .neutralizingGas) :
    abilityActive .neutralizingGas p = false := by
  simp [abilityActive]
  intro h; exact absurd h hne

/-- Theorem 13: Under Neutralizing Gas, the NeutGas holder stays active. -/
theorem neutGas_self_active (p : Pokemon)
    (hab : p.ability = .neutralizingGas) :
    abilityActive .neutralizingGas p = true := by
  simp [abilityActive, hab]

-- ============================================================
-- §7  Ability copying: Transform / Trace / Imposter
-- ============================================================

def applyTransform (gs : GameState) : GameState :=
  { gs with playerActive := { gs.playerActive with ability := gs.opponentActive.ability } }

/-- Theorem 14: Transform copies the opponent's ability. -/
theorem transform_copies_ability (gs : GameState) :
    (applyTransform gs).playerActive.ability = gs.opponentActive.ability := by
  simp [applyTransform]

/-- Theorem 15: Transform preserves player HP. -/
theorem transform_preserves_hp (gs : GameState) :
    (applyTransform gs).playerActive.hp = gs.playerActive.hp := by
  simp [applyTransform]

/-- Theorem 16: Transform doesn't change weather. -/
theorem transform_preserves_weather (gs : GameState) :
    (applyTransform gs).weather = gs.weather := by
  simp [applyTransform]

/-- Theorem 17: If opponent has no ability, transform gives noAbility. -/
theorem transform_no_ability (gs : GameState)
    (hna : gs.opponentActive.ability = .noAbility) :
    (applyTransform gs).playerActive.ability = .noAbility := by
  simp [applyTransform, hna]

-- ============================================================
-- §8  Weather-setting abilities
-- ============================================================

def applyWeatherAbility (gs : GameState) (p : Pokemon) : GameState :=
  match p.ability with
  | .drizzle    => { gs with weather := .rain }
  | .drought    => { gs with weather := .sun }
  | .sandStream => { gs with weather := .sandstorm }
  | .snowWarning => { gs with weather := .hail }
  | _ => gs

/-- Theorem 18: Drizzle sets rain. -/
theorem drizzle_sets_rain (gs : GameState) (p : Pokemon)
    (hab : p.ability = .drizzle) :
    (applyWeatherAbility gs p).weather = .rain := by
  simp [applyWeatherAbility, hab]

/-- Theorem 19: Drought sets sun. -/
theorem drought_sets_sun (gs : GameState) (p : Pokemon)
    (hab : p.ability = .drought) :
    (applyWeatherAbility gs p).weather = .sun := by
  simp [applyWeatherAbility, hab]

/-- Theorem 20: Weather ability of last entry wins. -/
theorem weather_last_writer_wins (gs : GameState) (p1 p2 : Pokemon)
    (h1 : p1.ability = .drizzle) (h2 : p2.ability = .drought) :
    (applyWeatherAbility (applyWeatherAbility gs p1) p2).weather = .sun := by
  simp [applyWeatherAbility, h1, h2]

/-- Theorem 21: Weather ability is idempotent. -/
theorem weather_ability_idempotent (gs : GameState) (p : Pokemon)
    (hab : p.ability = .drizzle) :
    applyWeatherAbility (applyWeatherAbility gs p) p =
    applyWeatherAbility gs p := by
  simp [applyWeatherAbility, hab]

/-- Theorem 22: All weather setters have equal priority. -/
theorem weather_setters_equal_priority :
    abilityPriority .drizzle = abilityPriority .drought ∧
    abilityPriority .drought = abilityPriority .sandStream ∧
    abilityPriority .sandStream = abilityPriority .snowWarning := by
  simp [abilityPriority]

-- ============================================================
-- §9  Damage-modifying abilities
-- ============================================================

def applyIntimidate (gs : GameState) : GameState :=
  { gs with damageModifier := gs.damageModifier - 20 }

/-- Theorem 23: Intimidate reduces damage modifier by 20. -/
theorem intimidate_reduces (gs : GameState) :
    (applyIntimidate gs).damageModifier = gs.damageModifier - 20 := by
  simp [applyIntimidate]

def multiscaleDamage (p : Pokemon) (baseDmg : Nat) : Nat :=
  if p.ability == .multiscale && p.atFullHp then baseDmg / 2 else baseDmg

/-- Theorem 24: Multiscale at full HP halves damage. -/
theorem multiscale_halves (p : Pokemon) (d : Nat)
    (hab : p.ability = .multiscale) (hfull : p.atFullHp = true) :
    multiscaleDamage p d = d / 2 := by
  simp [multiscaleDamage, hab, hfull]

/-- Theorem 25: Multiscale not at full HP does nothing. -/
theorem multiscale_not_full (p : Pokemon) (d : Nat)
    (hab : p.ability = .multiscale) (hnotfull : p.atFullHp = false) :
    multiscaleDamage p d = d := by
  simp [multiscaleDamage, hab, hnotfull]

/-- Mold Breaker lets an attacker ignore defender's ability. -/
def moldBreakerIgnores (attacker defender : Pokemon) (baseDmg : Nat) : Nat :=
  if attacker.ability == .moldBreaker then
    baseDmg
  else
    multiscaleDamage defender baseDmg

/-- Theorem 26: Mold Breaker ignores Multiscale. -/
theorem mold_breaker_ignores_multiscale (atk def_ : Pokemon) (d : Nat)
    (hmb : atk.ability = .moldBreaker) :
    moldBreakerIgnores atk def_ d = d := by
  simp [moldBreakerIgnores, hmb]

/-- Theorem 27: Without Mold Breaker, Multiscale applies at full HP. -/
theorem no_mold_breaker_multiscale_applies (atk def_ : Pokemon) (d : Nat)
    (hnmb : atk.ability ≠ .moldBreaker)
    (hms : def_.ability = .multiscale) (hfull : def_.atFullHp = true) :
    moldBreakerIgnores atk def_ d = d / 2 := by
  simp [moldBreakerIgnores]
  split
  · next h => exact absurd h hnmb
  · simp [multiscaleDamage, hms, hfull]

-- ============================================================
-- §10  Safeguard — prevent effects from Rule Box
-- ============================================================

def hasSafeguard (p : Pokemon) : Bool :=
  p.ability == .safeguard

def safeguardBlocks (attacker defender : Pokemon) : Bool :=
  hasSafeguard defender && attacker.kind.isRuleBox

/-- Theorem 28: Safeguard blocks Rule Box attackers. -/
theorem safeguard_blocks_ruleBox (attacker defender : Pokemon)
    (hsafe : defender.ability = .safeguard)
    (hrb : attacker.kind.isRuleBox = true) :
    safeguardBlocks attacker defender = true := by
  simp [safeguardBlocks, hasSafeguard, hsafe, hrb]

/-- Theorem 29: Safeguard allows non-Rule Box attackers. -/
theorem safeguard_allows_basic (attacker defender : Pokemon)
    (hsafe : defender.ability = .safeguard)
    (hnrb : attacker.kind.isRuleBox = false) :
    safeguardBlocks attacker defender = false := by
  simp [safeguardBlocks, hasSafeguard, hsafe, hnrb]

-- ============================================================
-- §11  Ability stacking rules
-- ============================================================

/-- Two abilities stack if they're in different categories. -/
def abilitiesStack (a1 a2 : Ability) : Bool :=
  classifyAbility a1 != classifyAbility a2

/-- Theorem 30: Intimidate and Drizzle stack (different categories). -/
theorem intimidate_drizzle_stack :
    abilitiesStack .intimidate .drizzle = true := by
  simp [abilitiesStack, classifyAbility]

/-- Theorem 31: Two weather setters don't stack. -/
theorem weather_setters_dont_stack :
    abilitiesStack .drizzle .drought = false := by
  simp [abilitiesStack, classifyAbility]

/-- Theorem 32: Negation and damage modifier stack. -/
theorem negation_damage_stack :
    abilitiesStack .garbotoxin .intimidate = true := by
  simp [abilitiesStack, classifyAbility]

-- ============================================================
-- §12  Coming-into-play triggers
-- ============================================================

/-- Theorem 33: Rush In is a coming-into-play trigger. -/
theorem rushIn_comingIntoPlay :
    abilityTrigger .rushIn = .comingIntoPlay := rfl

/-- Theorem 34: Intimidate is a coming-into-play trigger. -/
theorem intimidate_comingIntoPlay :
    abilityTrigger .intimidate = .comingIntoPlay := rfl

/-- Theorem 35: Safeguard is a static ability. -/
theorem safeguard_is_static :
    abilityTrigger .safeguard = .static := rfl

/-- Theorem 36: Beast Boost is a triggered ability. -/
theorem beastBoost_is_triggered :
    abilityTrigger .beastBoost = .triggered := rfl

-- ============================================================
-- §13  Classic Pokémon Powers
-- ============================================================

/-- Classic Pokémon Power identifiers (Base–Neo era). -/
inductive PowerId where
  | rainDance     -- Blastoise: attach extra Water energy
  | damageSwap    -- Alakazam: move damage counters
  | buzzap        -- Electrode: KO self to become energy
  | energyTrans   -- Venusaur: move Grass energy
  | toxicGas      -- Muk: disable all other Powers
  | healingWind   -- Vileplume: heal when evolved
  | noPower
  deriving DecidableEq, Repr

/-- Power classification. -/
inductive PowerClass where
  | triggered | ongoing | activated
  deriving DecidableEq, Repr

def classifyPower : PowerId → PowerClass
  | .rainDance   => .activated
  | .damageSwap  => .activated
  | .buzzap      => .activated
  | .energyTrans => .activated
  | .toxicGas    => .ongoing
  | .healingWind => .triggered
  | .noPower     => .activated

structure PowerState where
  mukInPlay  : Bool
  powerUsed  : List PowerId
  turnNumber : Nat
  deriving Repr

def isLocked (gs : PowerState) (pid : PowerId) : Bool :=
  gs.mukInPlay && pid != .toxicGas

def mukEnters (gs : PowerState) : PowerState :=
  { gs with mukInPlay := true }

def mukLeaves (gs : PowerState) : PowerState :=
  { gs with mukInPlay := false }

def endTurnReset (gs : PowerState) : PowerState :=
  { gs with powerUsed := [], turnNumber := gs.turnNumber + 1 }

/-- Theorem 37: Muk locks all non-Toxic-Gas powers. -/
theorem muk_locks_all (gs : PowerState) (pid : PowerId) (hpid : pid ≠ .toxicGas) :
    isLocked (mukEnters gs) pid = true := by
  simp [isLocked, mukEnters]
  cases pid <;> simp_all

/-- Theorem 38: Muk entering sets mukInPlay. -/
theorem muk_locks (gs : PowerState) : (mukEnters gs).mukInPlay = true := rfl

/-- Theorem 39: Muk leaving clears mukInPlay. -/
theorem muk_unlocks (gs : PowerState) : (mukLeaves gs).mukInPlay = false := rfl

/-- Theorem 40: End turn clears power usage. -/
theorem endTurn_clears (gs : PowerState) :
    (endTurnReset gs).powerUsed = [] := rfl

/-- Theorem 41: End turn increments turn number. -/
theorem endTurn_increments (gs : PowerState) :
    (endTurnReset gs).turnNumber = gs.turnNumber + 1 := rfl

-- ============================================================
-- §14  Path algebra
-- ============================================================

theorem abilPath_length_trans {a b c : GameState} : (p : AbilPath a b) → (q : AbilPath b c) →
    (p.trans q).length = p.length + q.length
  | .refl _, _ => by simp [AbilPath.trans, AbilPath.length]
  | .step _ p', q => by
    simp only [AbilPath.trans, AbilPath.length]
    rw [abilPath_length_trans p' q]; omega

/-- Theorem 42: Trans with refl is identity. -/
theorem abilPath_trans_refl {a b : GameState} : (p : AbilPath a b) → p.trans (.refl b) = p
  | .refl _ => by simp [AbilPath.trans]
  | .step s p' => by
    simp only [AbilPath.trans]
    rw [abilPath_trans_refl p']

/-- Theorem 43: Trans is associative. -/
theorem abilPath_trans_assoc {a b c d : GameState} : (p : AbilPath a b) → (q : AbilPath b c) → (r : AbilPath c d) →
    (p.trans q).trans r = p.trans (q.trans r)
  | .refl _, _, _ => by simp [AbilPath.trans]
  | .step s p', q, r => by
    simp only [AbilPath.trans]
    rw [abilPath_trans_assoc p' q r]

/-- Build a weather → intimidate chain. -/
def weatherThenIntimidate (gs : GameState) :
    AbilPath gs { { gs with weather := .rain } with damageModifier := gs.damageModifier - 20 } :=
  .step (.weatherSet gs .rain)
    (.step (.intimidateApply { gs with weather := .rain }) (.refl _))

/-- Theorem 44: Weather-then-intimidate is a 2-step path. -/
theorem weather_intimidate_length (gs : GameState) :
    (weatherThenIntimidate gs).length = 2 := by
  rfl

/-- Transport a property along an ability path. -/
def transportAbilPath {P : GameState → Prop}
    (preserve : ∀ a b, Step a b → P a → P b)
    {a b : GameState} (path : AbilPath a b) (pa : P a) : P b := by
  induction path with
  | refl _ => exact pa
  | step s _ ih => exact ih (preserve _ _ s pa)

/-- Theorem 45: Transport along refl is identity. -/
theorem transport_refl {P : GameState → Prop}
    (preserve : ∀ a b, Step a b → P a → P b)
    (gs : GameState) (pa : P gs) :
    transportAbilPath preserve (.refl gs) pa = pa := rfl

-- ============================================================
-- §15  Era interaction theorems
-- ============================================================

/-- Whether Muk's Toxic Gas affects a mechanic by era. -/
def toxicGasAffects : AbilityEra → Bool
  | .pokemonPower  => true
  | .pokePower     => false
  | .pokeBody      => false
  | .ability       => false

/-- Theorem 46: Toxic Gas only affects classic Pokémon Power era. -/
theorem toxicGas_classic_only :
    toxicGasAffects .pokemonPower = true ∧
    toxicGasAffects .ability = false :=
  ⟨rfl, rfl⟩

/-- Theorem 47: Categories are exhaustive (every ability maps to a category). -/
theorem ability_categories_exhaustive (a : Ability) :
    classifyAbility a = .negation ∨
    classifyAbility a = .weatherSetter ∨
    classifyAbility a = .damageModifier ∨
    classifyAbility a = .entryTrigger ∨
    classifyAbility a = .copying ∨
    classifyAbility a = .switching ∨
    classifyAbility a = .passive := by
  cases a <;> simp [classifyAbility]

end PokemonLean.Core.Abilities
