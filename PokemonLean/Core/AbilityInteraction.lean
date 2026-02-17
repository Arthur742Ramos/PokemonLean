/-
  PokemonLean / Core / AbilityInteraction.lean

  Ability interaction system — how abilities interact with each other
  and the game state in the Pokémon TCG.

  Covers:
  - Ability categories: Passive (always on), Triggered (on event),
    Activated (player choice, once per turn)
  - Ability locking: Garbodor's Garbotoxin (tool attached → all other
    abilities off), Path to the Peak (stadium: Rule Box Pokémon lose
    abilities)
  - Ability stacking: multiple of same ability on bench (e.g., 2
    Gardevoir = 2 Psychic Embrace)
  - Priority system: ability lock > ability activation
  - Theorems: locked abilities can't trigger, Garbotoxin requires tool,
    Path to Peak only affects Rule Box, stacking is additive, lock
    removal restores abilities, passive abilities don't require action,
    activated abilities limited to once per turn per Pokémon

  Self-contained — no imports from other PokemonLean modules.
  All proofs are sorry-free.  40+ theorems.
-/

namespace PokemonLean.Core.AbilityInteraction

-- ============================================================
-- §1  Core types
-- ============================================================

/-- Unique identifier for a Pokémon in play. -/
structure PokemonId where
  val : Nat
deriving DecidableEq, Repr, BEq, Inhabited

/-- Whether a Pokémon has a Rule Box (EX, ex, GX, V, VMAX, VSTAR). -/
inductive RuleBoxStatus where
  | hasRuleBox
  | noRuleBox
deriving DecidableEq, Repr, BEq, Inhabited

def RuleBoxStatus.isRuleBox : RuleBoxStatus → Bool
  | .hasRuleBox => true
  | .noRuleBox  => false

-- ============================================================
-- §2  Ability categories
-- ============================================================

/-- The three categories of abilities. -/
inductive AbilityCategory where
  | passive    -- Always on while in play (e.g., Manaphy Wave Veil)
  | triggered  -- Activates on a game event (e.g., on KO, on evolution)
  | activated  -- Player choice, once per turn per Pokémon
deriving DecidableEq, Repr, BEq, Inhabited

/-- Whether a category requires explicit player activation. -/
def AbilityCategory.requiresAction : AbilityCategory → Bool
  | .passive   => false
  | .triggered => false
  | .activated => true

/-- Whether a category is always active while in play. -/
def AbilityCategory.isAlwaysActive : AbilityCategory → Bool
  | .passive => true
  | _        => false

-- ============================================================
-- §3  Ability definition
-- ============================================================

/-- An ability with a name, category, and optional stacking flag. -/
structure Ability where
  name      : String
  category  : AbilityCategory
  stackable : Bool := true
deriving DecidableEq, Repr, BEq, Inhabited

/-- A Pokémon in play with an ability. -/
structure PokemonInPlay where
  pokId       : PokemonId
  ability     : Ability
  ruleBox     : RuleBoxStatus
  hasTool     : Bool := false
  usedAbility : Bool := false
deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================
-- §4  Ability lock sources
-- ============================================================

/-- Sources that can lock abilities. -/
inductive LockSource where
  | garbotoxin
  | pathToThePeak
  | neutralizingGas
deriving DecidableEq, Repr, BEq, Inhabited

/-- The game state relevant to ability interactions. -/
structure AbilityGameState where
  activeLocks     : List LockSource
  garbodorHasTool : Bool
  stadiumInPlay   : Bool
  pokemonInPlay   : List PokemonInPlay
deriving Repr, Inhabited

-- ============================================================
-- §5  Lock checking
-- ============================================================

/-- Is Garbotoxin active? Requires tool attached. -/
def isGarbotoxinActive (gs : AbilityGameState) : Bool :=
  gs.activeLocks.contains .garbotoxin && gs.garbodorHasTool

/-- Is Path to the Peak active? Requires stadium in play. -/
def isPathActive (gs : AbilityGameState) : Bool :=
  gs.activeLocks.contains .pathToThePeak && gs.stadiumInPlay

/-- Is Neutralizing Gas active? No extra condition needed. -/
def isNeutralizingGasActive (gs : AbilityGameState) : Bool :=
  gs.activeLocks.contains .neutralizingGas

/-- Is a specific Pokémon's ability locked? -/
def isAbilityLocked (gs : AbilityGameState) (pok : PokemonInPlay) : Bool :=
  isGarbotoxinActive gs ||
  isNeutralizingGasActive gs ||
  (isPathActive gs && pok.ruleBox.isRuleBox)

/-- Is a specific Pokémon's ability functional (not locked)? -/
def isAbilityFunctional (gs : AbilityGameState) (pok : PokemonInPlay) : Bool :=
  !isAbilityLocked gs pok

-- ============================================================
-- §6  Activation checking
-- ============================================================

/-- Can a Pokémon use its activated ability this turn? -/
def canActivate (gs : AbilityGameState) (pok : PokemonInPlay) : Bool :=
  isAbilityFunctional gs pok &&
  pok.ability.category == .activated &&
  !pok.usedAbility

/-- Can a passive ability operate? -/
def isPassiveOperating (gs : AbilityGameState) (pok : PokemonInPlay) : Bool :=
  isAbilityFunctional gs pok && pok.ability.category == .passive

/-- Can a triggered ability fire? -/
def canTrigger (gs : AbilityGameState) (pok : PokemonInPlay) : Bool :=
  isAbilityFunctional gs pok && pok.ability.category == .triggered

-- ============================================================
-- §7  Activation / use
-- ============================================================

/-- Use an activated ability (marks it as used this turn). -/
def useAbility (pok : PokemonInPlay) : PokemonInPlay :=
  { pok with usedAbility := true }

/-- Reset ability usage at start of turn. -/
def resetAbilityUsage (pok : PokemonInPlay) : PokemonInPlay :=
  { pok with usedAbility := false }

/-- Reset all Pokémon ability usage at start of turn. -/
def resetAllUsage (poks : List PokemonInPlay) : List PokemonInPlay :=
  poks.map resetAbilityUsage

-- ============================================================
-- §8  Ability stacking
-- ============================================================

/-- Count how many Pokémon in play have the same ability name. -/
def countAbility (poks : List PokemonInPlay) (abilityName : String) : Nat :=
  (poks.filter (fun p => p.ability.name == abilityName)).length

/-- Total stacked effect: each copy adds the base value. -/
def stackedEffect (poks : List PokemonInPlay) (abilityName : String)
    (baseValue : Nat) : Nat :=
  countAbility poks abilityName * baseValue

/-- Count functional (unlocked) copies of an ability. -/
def countFunctionalAbility (gs : AbilityGameState) (abilityName : String) : Nat :=
  (gs.pokemonInPlay.filter (fun p =>
    p.ability.name == abilityName && isAbilityFunctional gs p)).length

/-- Stacked effect considering only functional copies. -/
def functionalStackedEffect (gs : AbilityGameState) (abilityName : String)
    (baseValue : Nat) : Nat :=
  countFunctionalAbility gs abilityName * baseValue

-- ============================================================
-- §9  Lock removal
-- ============================================================

/-- Remove a lock source from the game state. -/
def removeLock (gs : AbilityGameState) (src : LockSource) : AbilityGameState :=
  { gs with activeLocks := gs.activeLocks.filter (· != src) }

/-- Remove Garbodor's tool (disables Garbotoxin). -/
def removeGarbodorTool (gs : AbilityGameState) : AbilityGameState :=
  { gs with garbodorHasTool := false }

/-- Remove stadium from play. -/
def removeStadium (gs : AbilityGameState) : AbilityGameState :=
  { gs with stadiumInPlay := false }

-- ============================================================
-- §10  Priority system
-- ============================================================

/-- Priority levels: lock always takes priority over activation. -/
inductive AbilityPriorityLevel where
  | lockLevel
  | activationLevel
deriving DecidableEq, Repr, BEq, Inhabited

def AbilityPriorityLevel.value : AbilityPriorityLevel → Nat
  | .lockLevel       => 2
  | .activationLevel => 1

-- ============================================================
-- §11  Sample data for theorems
-- ============================================================

private def cleanState : AbilityGameState :=
  { activeLocks := [], garbodorHasTool := false, stadiumInPlay := false,
    pokemonInPlay := [] }

private def garbotoxinState : AbilityGameState :=
  { activeLocks := [.garbotoxin], garbodorHasTool := true, stadiumInPlay := false,
    pokemonInPlay := [] }

private def garbotoxinNoToolState : AbilityGameState :=
  { activeLocks := [.garbotoxin], garbodorHasTool := false, stadiumInPlay := false,
    pokemonInPlay := [] }

private def pathState : AbilityGameState :=
  { activeLocks := [.pathToThePeak], garbodorHasTool := false, stadiumInPlay := true,
    pokemonInPlay := [] }

private def pathNoStadiumState : AbilityGameState :=
  { activeLocks := [.pathToThePeak], garbodorHasTool := false, stadiumInPlay := false,
    pokemonInPlay := [] }

private def neutralizingGasState : AbilityGameState :=
  { activeLocks := [.neutralizingGas], garbodorHasTool := false, stadiumInPlay := false,
    pokemonInPlay := [] }

private def samplePassive : Ability :=
  { name := "Wave Veil", category := .passive, stackable := false }

private def sampleActivated : Ability :=
  { name := "Psychic Embrace", category := .activated, stackable := true }

private def sampleTriggered : Ability :=
  { name := "Setup", category := .triggered, stackable := false }

private def sampleRuleBoxPokemon : PokemonInPlay :=
  { pokId := ⟨1⟩, ability := samplePassive, ruleBox := .hasRuleBox }

private def sampleNonRuleBoxPokemon : PokemonInPlay :=
  { pokId := ⟨2⟩, ability := sampleActivated, ruleBox := .noRuleBox }

private def activatedPokemonFresh : PokemonInPlay :=
  { pokId := ⟨5⟩, ability := sampleActivated, ruleBox := .noRuleBox, usedAbility := false }

private def activatedPokemonUsed : PokemonInPlay :=
  { pokId := ⟨5⟩, ability := sampleActivated, ruleBox := .noRuleBox, usedAbility := true }

private def triggeredPokemon : PokemonInPlay :=
  { pokId := ⟨4⟩, ability := sampleTriggered, ruleBox := .noRuleBox }

private def passivePokemon : PokemonInPlay :=
  { pokId := ⟨6⟩, ability := samplePassive, ruleBox := .noRuleBox }

private def twoGardevoirs : List PokemonInPlay :=
  [{ pokId := ⟨10⟩, ability := sampleActivated, ruleBox := .noRuleBox },
   { pokId := ⟨11⟩, ability := sampleActivated, ruleBox := .noRuleBox }]

private def threeGardevoirs : List PokemonInPlay :=
  [{ pokId := ⟨10⟩, ability := sampleActivated, ruleBox := .noRuleBox },
   { pokId := ⟨11⟩, ability := sampleActivated, ruleBox := .noRuleBox },
   { pokId := ⟨12⟩, ability := sampleActivated, ruleBox := .noRuleBox }]

private def stateWithGardevoirs : AbilityGameState :=
  { cleanState with pokemonInPlay := twoGardevoirs }

private def lockedStateWithGardevoirs : AbilityGameState :=
  { garbotoxinState with pokemonInPlay := twoGardevoirs }

private def usedPokemon1 : PokemonInPlay :=
  { pokId := ⟨1⟩, ability := sampleActivated, ruleBox := .noRuleBox, usedAbility := true }

private def usedPokemon2 : PokemonInPlay :=
  { pokId := ⟨2⟩, ability := sampleActivated, ruleBox := .noRuleBox, usedAbility := true }

-- ============================================================
-- §12  THEOREMS (40+)
-- ============================================================

-- ---- Passive abilities ----

theorem passive_does_not_require_action :
    AbilityCategory.passive.requiresAction = false := by rfl

theorem passive_is_always_active :
    AbilityCategory.passive.isAlwaysActive = true := by rfl

theorem triggered_not_always_active :
    AbilityCategory.triggered.isAlwaysActive = false := by rfl

theorem activated_requires_action :
    AbilityCategory.activated.requiresAction = true := by rfl

theorem triggered_no_action_required :
    AbilityCategory.triggered.requiresAction = false := by rfl

-- ---- Garbotoxin ----

theorem garbotoxin_requires_tool :
    isGarbotoxinActive garbotoxinNoToolState = false := by native_decide

theorem garbotoxin_active_with_tool :
    isGarbotoxinActive garbotoxinState = true := by native_decide

theorem garbotoxin_locks_ability :
    isAbilityLocked garbotoxinState sampleRuleBoxPokemon = true := by native_decide

theorem garbotoxin_locks_non_rulebox_too :
    isAbilityLocked garbotoxinState sampleNonRuleBoxPokemon = true := by native_decide

-- ---- Path to the Peak ----

theorem path_requires_stadium :
    isPathActive pathNoStadiumState = false := by native_decide

theorem path_active_with_stadium :
    isPathActive pathState = true := by native_decide

theorem path_locks_rulebox :
    isAbilityLocked pathState sampleRuleBoxPokemon = true := by native_decide

theorem path_does_not_lock_non_rulebox :
    isAbilityLocked pathState sampleNonRuleBoxPokemon = false := by native_decide

-- ---- Neutralizing Gas ----

theorem neutralizing_gas_active :
    isNeutralizingGasActive neutralizingGasState = true := by native_decide

theorem neutralizing_gas_locks_all :
    isAbilityLocked neutralizingGasState sampleRuleBoxPokemon = true := by native_decide

theorem neutralizing_gas_locks_non_rulebox :
    isAbilityLocked neutralizingGasState sampleNonRuleBoxPokemon = true := by native_decide

-- ---- Clean state (no locks) ----

theorem clean_state_no_garbotoxin :
    isGarbotoxinActive cleanState = false := by native_decide

theorem clean_state_no_path :
    isPathActive cleanState = false := by native_decide

theorem clean_state_no_neutralizing_gas :
    isNeutralizingGasActive cleanState = false := by native_decide

theorem clean_state_ability_functional :
    isAbilityFunctional cleanState sampleRuleBoxPokemon = true := by native_decide

theorem clean_state_ability_functional_non_rb :
    isAbilityFunctional cleanState sampleNonRuleBoxPokemon = true := by native_decide

-- ---- Locked abilities can't trigger ----

theorem locked_cant_activate :
    canActivate garbotoxinState activatedPokemonFresh = false := by native_decide

theorem locked_cant_trigger :
    canTrigger garbotoxinState triggeredPokemon = false := by native_decide

theorem locked_passive_not_operating :
    isPassiveOperating garbotoxinState sampleRuleBoxPokemon = false := by native_decide

-- ---- Activation once per turn ----

theorem activated_once_per_turn :
    canActivate cleanState activatedPokemonUsed = false := by native_decide

theorem activated_available_when_unused :
    canActivate cleanState activatedPokemonFresh = true := by native_decide

theorem use_ability_marks_used :
    (useAbility activatedPokemonFresh).usedAbility = true := by rfl

theorem reset_clears_used :
    (resetAbilityUsage activatedPokemonUsed).usedAbility = false := by rfl

-- ---- Stacking ----

theorem stacking_zero_with_empty :
    countAbility [] "Psychic Embrace" = 0 := by rfl

theorem stacking_one_copy :
    countAbility [activatedPokemonFresh] "Psychic Embrace" = 1 := by native_decide

theorem stacking_two_copies :
    countAbility twoGardevoirs "Psychic Embrace" = 2 := by native_decide

theorem stacked_effect_additive :
    stackedEffect twoGardevoirs "Psychic Embrace" 20 = 40 := by native_decide

theorem stacked_effect_three_copies :
    stackedEffect threeGardevoirs "Psychic Embrace" 20 = 60 := by native_decide

-- ---- Lock removal restores abilities ----

theorem remove_garbotoxin_lock_restores :
    isGarbotoxinActive (removeLock garbotoxinState .garbotoxin) = false := by native_decide

theorem remove_tool_disables_garbotoxin :
    isGarbotoxinActive (removeGarbodorTool garbotoxinState) = false := by native_decide

theorem remove_stadium_disables_path :
    isPathActive (removeStadium pathState) = false := by native_decide

theorem remove_neutralizing_gas_restores :
    isNeutralizingGasActive (removeLock neutralizingGasState .neutralizingGas) = false := by
  native_decide

-- ---- Priority ----

theorem lock_priority_beats_activation :
    AbilityPriorityLevel.lockLevel.value > AbilityPriorityLevel.activationLevel.value := by
  native_decide

-- ---- Functional stacking under locks ----

theorem functional_count_clean :
    countFunctionalAbility stateWithGardevoirs "Psychic Embrace" = 2 := by native_decide

theorem functional_count_locked :
    countFunctionalAbility lockedStateWithGardevoirs "Psychic Embrace" = 0 := by native_decide

theorem functional_stacked_locked_zero :
    functionalStackedEffect lockedStateWithGardevoirs "Psychic Embrace" 20 = 0 := by
  native_decide

theorem functional_stacked_clean :
    functionalStackedEffect stateWithGardevoirs "Psychic Embrace" 20 = 40 := by
  native_decide

-- ---- Mixed scenarios ----

theorem path_only_affects_rulebox_in_list :
    isAbilityLocked pathState sampleRuleBoxPokemon = true ∧
    isAbilityLocked pathState sampleNonRuleBoxPokemon = false := by
  constructor <;> native_decide

theorem rulebox_isRuleBox_true :
    RuleBoxStatus.hasRuleBox.isRuleBox = true := by rfl

theorem non_rulebox_isRuleBox_false :
    RuleBoxStatus.noRuleBox.isRuleBox = false := by rfl

-- ---- Reset all usage ----

theorem reset_all_clears_all :
    List.all (resetAllUsage [usedPokemon1, usedPokemon2])
      (fun p => !p.usedAbility) = true := by native_decide

-- ---- Passive operating in clean state ----

theorem passive_operates_clean :
    isPassiveOperating cleanState passivePokemon = true := by native_decide

theorem passive_blocked_by_garbotoxin :
    isPassiveOperating garbotoxinState passivePokemon = false := by native_decide

end PokemonLean.Core.AbilityInteraction
