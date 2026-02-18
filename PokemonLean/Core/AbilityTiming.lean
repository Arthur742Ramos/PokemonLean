/-
  PokemonLean / Core / AbilityTiming.lean

  Ability activation timing and resolution order for the Pokémon TCG.
  Covers timing categories (onPlay, oncePerTurn, always/passive, onAttack,
  betweenTurns, onKO), ability priority hierarchy (prevention > replacement
  > trigger > passive), ability negation (Garbotoxin, Path to the Peak,
  Neutralizing Gas), resolution order for simultaneous triggers, and
  specific ability interactions.

  Self-contained — no imports from other PokemonLean modules.
  All proofs are sorry-free.  35+ theorems.
-/

namespace PokemonLean.Core.AbilityTiming

-- ============================================================
-- §1  Ability Timing Categories
-- ============================================================

/-- When an ability can activate. -/
inductive Timing where
  | onPlay         -- Triggers when the Pokémon enters play (e.g. Lumineon V)
  | oncePerTurn    -- Can be used once per turn (e.g. Bibarel, Genesect V)
  | always         -- Passive, always active while in play (e.g. Manaphy)
  | onAttack       -- Triggered during attack resolution (e.g. extra damage)
  | betweenTurns   -- Triggered between turns (e.g. special conditions)
  | onKO           -- Triggered when this Pokémon is knocked out
deriving DecidableEq, Repr, BEq, Inhabited

/-- Whether a timing requires explicit activation by the player. -/
def Timing.requiresActivation : Timing → Bool
  | .onPlay      => false   -- Auto-triggers
  | .oncePerTurn => true    -- Player chooses to use it
  | .always      => false   -- Passive
  | .onAttack    => false   -- Triggered by game action
  | .betweenTurns => false  -- Triggered by game state
  | .onKO        => false   -- Triggered by game event

/-- Whether a timing can activate multiple times per turn. -/
def Timing.multiplePerTurn : Timing → Bool
  | .oncePerTurn => false
  | .onPlay      => false   -- Only triggers once (on entry)
  | _            => true    -- Passive/attack/between-turns can trigger multiple times

-- ============================================================
-- §2  Ability Priority Hierarchy
-- ============================================================

/-- Priority categories for ability resolution.
    Higher priority resolves first. -/
inductive AbilityPriority where
  | prevention    -- Prevents an effect (e.g. Manaphy's Bench Barrier)
  | replacement   -- Replaces one effect with another
  | trigger       -- Triggered by an event (onPlay, onKO)
  | passive       -- Always active, lowest priority
deriving DecidableEq, Repr, BEq, Inhabited

/-- Numeric priority value (higher = resolves first). -/
def AbilityPriority.value : AbilityPriority → Nat
  | .prevention  => 4
  | .replacement => 3
  | .trigger     => 2
  | .passive     => 1

/-- Compare two priorities: does p1 resolve before p2? -/
def AbilityPriority.resolvesBefore (p1 p2 : AbilityPriority) : Bool :=
  p1.value > p2.value

/-- All priorities in resolution order (highest first). -/
def AbilityPriority.allOrdered : List AbilityPriority :=
  [.prevention, .replacement, .trigger, .passive]

-- ============================================================
-- §3  Rule Box Classification (for Path to the Peak)
-- ============================================================

/-- Whether a Pokémon has a Rule Box. -/
inductive RuleBoxStatus where
  | hasRuleBox    -- EX, ex, GX, V, VMAX, VSTAR, Tag Team, etc.
  | noRuleBox     -- Regular Pokémon
deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================
-- §4  Ability Negation Sources
-- ============================================================

/-- Sources of ability negation in the Pokémon TCG. -/
inductive NegationSource where
  | garbotoxin       -- Garbodor with tool: blocks ALL abilities (except its own)
  | pathToThePeak    -- Stadium: blocks Rule Box Pokémon abilities only
  | neutralizingGas  -- Galarian Weezing: blocks all abilities (including own when leaving)
  | templeOfSinnoh   -- Stadium: blocks special energy effects (NOT abilities)
  | none             -- No negation
deriving DecidableEq, Repr, BEq, Inhabited

/-- Whether a negation source affects abilities at all. -/
def NegationSource.affectsAbilities : NegationSource → Bool
  | .garbotoxin      => true
  | .pathToThePeak   => true
  | .neutralizingGas => true
  | .templeOfSinnoh  => false   -- Temple affects energy, not abilities
  | .none            => false

/-- Whether a negation source blocks a Pokémon's ability.
    Parameters: the source, whether the Pokémon has a rule box,
    and whether this is the Garbodor with Garbotoxin itself. -/
def isAbilityBlocked (source : NegationSource) (ruleBox : RuleBoxStatus) (isSelf : Bool) : Bool :=
  match source with
  | .garbotoxin      => !isSelf  -- Blocks all except itself
  | .pathToThePeak   => ruleBox == .hasRuleBox  -- Only blocks Rule Box
  | .neutralizingGas => true   -- Blocks everything (even itself once resolved)
  | .templeOfSinnoh  => false  -- Doesn't block abilities
  | .none            => false

-- ============================================================
-- §5  Ability State Tracking
-- ============================================================

/-- State for a single ability instance on the field. -/
structure AbilityState where
  name      : String
  timing    : Timing
  priority  : AbilityPriority
  isActive  : Bool            -- Is the ability currently active?
  usedThisTurn : Bool         -- Has it been used this turn? (for oncePerTurn)
  ruleBox   : RuleBoxStatus   -- Does the Pokémon have a rule box?
  isGarbodor : Bool           -- Is this the Garbodor with Garbotoxin?
deriving Repr, Inhabited

/-- Whether this ability can currently activate. -/
def AbilityState.canActivate (a : AbilityState) (negation : NegationSource) : Bool :=
  a.isActive &&
  !isAbilityBlocked negation a.ruleBox a.isGarbodor &&
  (a.timing != .oncePerTurn || !a.usedThisTurn)

/-- Mark an ability as used this turn. -/
def AbilityState.markUsed (a : AbilityState) : AbilityState :=
  { a with usedThisTurn := true }

/-- Reset turn-based usage at start of turn. -/
def AbilityState.resetTurn (a : AbilityState) : AbilityState :=
  { a with usedThisTurn := false }

-- ============================================================
-- §6  Resolution Order
-- ============================================================

/-- Which player's abilities resolve first.
    Active player (the one whose turn it is) resolves first. -/
inductive PlayerOrder where
  | activePlayer
  | defendingPlayer
deriving DecidableEq, Repr, BEq, Inhabited

/-- Numeric order value (lower = resolves first). -/
def PlayerOrder.orderValue : PlayerOrder → Nat
  | .activePlayer    => 1
  | .defendingPlayer => 2

/-- Within the same player, abilities resolve in order of play
    (first placed on field resolves first).
    Modeled as a field index (lower = played first). -/
structure AbilityInQueue where
  ability     : AbilityState
  playerOrder : PlayerOrder
  playOrder   : Nat          -- Position order on field (lower = earlier)
deriving Repr, Inhabited

/-- Compare two queued abilities: who resolves first?
    1. Higher priority resolves first.
    2. Active player resolves before defending player.
    3. Earlier play order resolves first. -/
def resolvesBefore (a b : AbilityInQueue) : Bool :=
  if a.ability.priority.value > b.ability.priority.value then true
  else if a.ability.priority.value < b.ability.priority.value then false
  else if a.playerOrder.orderValue < b.playerOrder.orderValue then true
  else if a.playerOrder.orderValue > b.playerOrder.orderValue then false
  else a.playOrder < b.playOrder

-- ============================================================
-- §7  Specific Abilities
-- ============================================================

/-- Manaphy's Bench Barrier: prevents all damage done to benched Pokémon
    by opponent's attacks. Prevention ability, always active. -/
def manaphyBenchBarrier : AbilityState where
  name := "Bench Barrier"
  timing := .always
  priority := .prevention
  isActive := true
  usedThisTurn := false
  ruleBox := .noRuleBox
  isGarbodor := false

/-- Lumineon V's Luminous Sign: when played from hand to bench,
    search deck for a Supporter card. onPlay timing. -/
def lumineonLuminousSign : AbilityState where
  name := "Luminous Sign"
  timing := .onPlay
  priority := .trigger
  isActive := true
  usedThisTurn := false
  ruleBox := .hasRuleBox
  isGarbodor := false

/-- Bibarel's Industrious Incisors: once per turn, draw until 5 cards. -/
def bibarelIndustrious : AbilityState where
  name := "Industrious Incisors"
  timing := .oncePerTurn
  priority := .trigger
  isActive := true
  usedThisTurn := false
  ruleBox := .noRuleBox
  isGarbodor := false

/-- Genesect V's Fusion Strike System: once per turn, draw until hand
    equals number of Pokémon tools. -/
def genesectFSSystem : AbilityState where
  name := "Fusion Strike System"
  timing := .oncePerTurn
  priority := .trigger
  isActive := true
  usedThisTurn := false
  ruleBox := .hasRuleBox
  isGarbodor := false

/-- Garbodor's Garbotoxin: passive, blocks all other abilities. -/
def garbodorGarbotoxin : AbilityState where
  name := "Garbotoxin"
  timing := .always
  priority := .passive
  isActive := true
  usedThisTurn := false
  ruleBox := .noRuleBox
  isGarbodor := true

-- ============================================================
-- §8  Damage Prevention Model
-- ============================================================

/-- Whether bench damage is prevented (Manaphy interaction). -/
def benchDamagePrevented (manaphyInPlay : Bool) (negation : NegationSource) : Bool :=
  manaphyInPlay && !isAbilityBlocked negation .noRuleBox false

/-- Calculate final bench damage after prevention check. -/
def finalBenchDamage (rawDamage : Nat) (manaphyInPlay : Bool) (negation : NegationSource) : Nat :=
  if benchDamagePrevented manaphyInPlay negation then 0 else rawDamage

-- ============================================================
-- §9  Redundant Negation Model
-- ============================================================

/-- Multiple negation sources: the strictest one wins.
    Garbotoxin + Path = Garbotoxin (blocks more).
    Negation is NOT stackable — redundant locks don't create double-negation. -/
def effectiveNegation (sources : List NegationSource) : NegationSource :=
  if sources.any (· == .garbotoxin) then .garbotoxin
  else if sources.any (· == .neutralizingGas) then .neutralizingGas
  else if sources.any (· == .pathToThePeak) then .pathToThePeak
  else if sources.any (· == .templeOfSinnoh) then .templeOfSinnoh
  else .none

/-- Whether the effective negation of multiple sources blocks abilities.
    Key: it's the same as a single application — no double negation. -/
def multiNegationBlocks (sources : List NegationSource) (ruleBox : RuleBoxStatus) (isSelf : Bool) : Bool :=
  isAbilityBlocked (effectiveNegation sources) ruleBox isSelf

-- ============================================================
-- §10  onPlay Trigger Tracking
-- ============================================================

/-- An onPlay ability triggers exactly once: when the Pokémon enters play. -/
structure OnPlayTracker where
  hasTriggered : Bool
deriving DecidableEq, Repr, Inhabited

/-- Initial tracker: not yet triggered. -/
def OnPlayTracker.initial : OnPlayTracker := { hasTriggered := false }

/-- Trigger the onPlay ability. -/
def OnPlayTracker.trigger (_t : OnPlayTracker) : OnPlayTracker :=
  { hasTriggered := true }

/-- Whether the onPlay ability can still trigger. -/
def OnPlayTracker.canTrigger (t : OnPlayTracker) : Bool := !t.hasTriggered

-- ============================================================
-- §11  Theorems — Ability Timing Properties
-- ============================================================

/-- Theorem 1: Passive abilities don't require activation. -/
theorem passive_no_activation : Timing.always.requiresActivation = false := by rfl

/-- Theorem 2: oncePerTurn requires activation. -/
theorem once_per_turn_needs_activation : Timing.oncePerTurn.requiresActivation = true := by rfl

/-- Theorem 3: onPlay doesn't allow multiple per turn. -/
theorem on_play_once : Timing.onPlay.multiplePerTurn = false := by rfl

/-- Theorem 4: oncePerTurn doesn't allow multiple per turn. -/
theorem once_per_turn_single : Timing.oncePerTurn.multiplePerTurn = false := by rfl

/-- Theorem 5: Passive abilities can trigger multiple times. -/
theorem passive_multiple : Timing.always.multiplePerTurn = true := by rfl

-- ============================================================
-- §12  Theorems — Priority Hierarchy
-- ============================================================

/-- Theorem 6: Prevention has highest priority value. -/
theorem prevention_highest : AbilityPriority.prevention.value = 4 := by rfl

/-- Theorem 7: Prevention resolves before replacement. -/
theorem prevention_before_replacement :
    AbilityPriority.prevention.resolvesBefore .replacement = true := by native_decide

/-- Theorem 8: Replacement resolves before trigger. -/
theorem replacement_before_trigger :
    AbilityPriority.replacement.resolvesBefore .trigger = true := by native_decide

/-- Theorem 9: Trigger resolves before passive. -/
theorem trigger_before_passive :
    AbilityPriority.trigger.resolvesBefore .passive = true := by native_decide

/-- Theorem 10: Passive has lowest priority. -/
theorem passive_lowest : AbilityPriority.passive.value = 1 := by rfl

/-- Theorem 11: Priority ordering is transitive.
    If A > B and B > C, then A > C. -/
theorem priority_transitive (a b c : AbilityPriority)
    (hab : a.resolvesBefore b = true) (hbc : b.resolvesBefore c = true) :
    a.resolvesBefore c = true := by
  simp [AbilityPriority.resolvesBefore] at *
  omega

/-- Theorem 12: Priority is irreflexive — no ability resolves before itself. -/
theorem priority_irreflexive (a : AbilityPriority) :
    a.resolvesBefore a = false := by
  cases a <;> native_decide

/-- Theorem 13: All priorities are in the ordered list. -/
theorem all_priorities_count : AbilityPriority.allOrdered.length = 4 := by native_decide

-- ============================================================
-- §13  Theorems — Garbotoxin
-- ============================================================

/-- Theorem 14: Garbotoxin blocks all non-Garbodor abilities. -/
theorem garbotoxin_blocks_others :
    isAbilityBlocked .garbotoxin .noRuleBox false = true := by rfl

/-- Theorem 15: Garbotoxin blocks Rule Box abilities too. -/
theorem garbotoxin_blocks_rulebox :
    isAbilityBlocked .garbotoxin .hasRuleBox false = true := by rfl

/-- Theorem 16: Garbotoxin does NOT block itself. -/
theorem garbotoxin_self_exempt :
    isAbilityBlocked .garbotoxin .noRuleBox true = false := by rfl

/-- Theorem 17: Garbodor with Garbotoxin can still activate. -/
theorem garbodor_can_activate :
    garbodorGarbotoxin.canActivate .garbotoxin = true := by native_decide

/-- Theorem 18: Bibarel is blocked by Garbotoxin. -/
theorem bibarel_blocked_by_garbotoxin :
    bibarelIndustrious.canActivate .garbotoxin = false := by native_decide

-- ============================================================
-- §14  Theorems — Path to the Peak
-- ============================================================

/-- Theorem 19: Path blocks Rule Box abilities. -/
theorem path_blocks_rulebox :
    isAbilityBlocked .pathToThePeak .hasRuleBox false = true := by rfl

/-- Theorem 20: Path does NOT block non-Rule Box abilities. -/
theorem path_allows_non_rulebox :
    isAbilityBlocked .pathToThePeak .noRuleBox false = false := by rfl

/-- Theorem 21: Lumineon V (Rule Box) is blocked by Path. -/
theorem lumineon_blocked_by_path :
    lumineonLuminousSign.canActivate .pathToThePeak = false := by native_decide

/-- Theorem 22: Bibarel (no Rule Box) is NOT blocked by Path. -/
theorem bibarel_not_blocked_by_path :
    bibarelIndustrious.canActivate .pathToThePeak = true := by native_decide

/-- Theorem 23: Genesect V (Rule Box) is blocked by Path. -/
theorem genesect_blocked_by_path :
    genesectFSSystem.canActivate .pathToThePeak = false := by native_decide

-- ============================================================
-- §15  Theorems — Neutralizing Gas
-- ============================================================

/-- Theorem 24: Neutralizing Gas blocks everything (including non-self). -/
theorem neutral_gas_blocks_all :
    isAbilityBlocked .neutralizingGas .noRuleBox false = true := by rfl

/-- Theorem 25: Neutralizing Gas blocks even itself when resolved. -/
theorem neutral_gas_blocks_self :
    isAbilityBlocked .neutralizingGas .noRuleBox true = true := by rfl

-- ============================================================
-- §16  Theorems — Temple of Sinnoh
-- ============================================================

/-- Theorem 26: Temple of Sinnoh does NOT block abilities. -/
theorem temple_no_ability_block :
    isAbilityBlocked .templeOfSinnoh .hasRuleBox false = false := by rfl

/-- Theorem 27: Temple of Sinnoh does not affect abilities at all. -/
theorem temple_not_ability_negation :
    NegationSource.templeOfSinnoh.affectsAbilities = false := by rfl

-- ============================================================
-- §17  Theorems — Redundant Negation
-- ============================================================

/-- Theorem 28: Garbotoxin + Path = Garbotoxin (strictest wins). -/
theorem garb_plus_path :
    effectiveNegation [.garbotoxin, .pathToThePeak] = .garbotoxin := by native_decide

/-- Theorem 29: Negation is not stackable: two Garbotoxin = one Garbotoxin. -/
theorem double_garb_same :
    effectiveNegation [.garbotoxin, .garbotoxin] = .garbotoxin := by native_decide

/-- Theorem 30: Empty negation list = no negation. -/
theorem no_negation_sources :
    effectiveNegation [] = .none := by native_decide

/-- Theorem 31: Single Path = Path. -/
theorem single_path :
    effectiveNegation [.pathToThePeak] = .pathToThePeak := by native_decide

-- ============================================================
-- §18  Theorems — Specific Ability Properties
-- ============================================================

/-- Theorem 32: Manaphy's Bench Barrier is a prevention ability. -/
theorem manaphy_is_prevention : manaphyBenchBarrier.priority = .prevention := by rfl

/-- Theorem 33: Manaphy is always active (passive timing). -/
theorem manaphy_always_active : manaphyBenchBarrier.timing = .always := by rfl

/-- Theorem 34: Lumineon V is an onPlay ability. -/
theorem lumineon_on_play : lumineonLuminousSign.timing = .onPlay := by rfl

/-- Theorem 35: Bibarel is oncePerTurn. -/
theorem bibarel_once_per_turn : bibarelIndustrious.timing = .oncePerTurn := by rfl

-- ============================================================
-- §19  Theorems — Resolution Order
-- ============================================================

/-- Theorem 36: Active player resolves before defending player. -/
theorem active_before_defending :
    PlayerOrder.activePlayer.orderValue < PlayerOrder.defendingPlayer.orderValue := by
  native_decide

/-- Theorem 37: Prevention resolves before everything in queue. -/
theorem prevention_first_in_queue :
    let a : AbilityInQueue := ⟨manaphyBenchBarrier, .activePlayer, 0⟩
    let b : AbilityInQueue := ⟨bibarelIndustrious, .activePlayer, 0⟩
    resolvesBefore a b = true := by native_decide

-- ============================================================
-- §20  Theorems — onPlay Trigger
-- ============================================================

/-- Theorem 38: onPlay tracker starts untriggered. -/
theorem on_play_initial : OnPlayTracker.initial.canTrigger = true := by rfl

/-- Theorem 39: After triggering, onPlay cannot trigger again. -/
theorem on_play_once_only :
    (OnPlayTracker.initial.trigger).canTrigger = false := by rfl

/-- Theorem 40: Triggering is idempotent. -/
theorem on_play_idempotent (t : OnPlayTracker) :
    t.trigger.trigger = t.trigger := by
  simp [OnPlayTracker.trigger]

-- ============================================================
-- §21  Theorems — Bench Barrier Interaction
-- ============================================================

/-- Theorem 41: With Manaphy in play and no negation, bench damage is 0. -/
theorem manaphy_prevents_bench_damage :
    finalBenchDamage 120 true .none = 0 := by native_decide

/-- Theorem 42: Without Manaphy, bench damage goes through. -/
theorem no_manaphy_bench_damage :
    finalBenchDamage 120 false .none = 120 := by native_decide

/-- Theorem 43: With Manaphy BUT Garbotoxin active, bench damage goes through.
    (Garbotoxin blocks Manaphy's ability.) -/
theorem manaphy_blocked_by_garb :
    finalBenchDamage 120 true .garbotoxin = 120 := by native_decide

/-- Theorem 44: oncePerTurn ability cannot be used twice.
    After marking used, canActivate returns false. -/
theorem once_per_turn_used_blocked :
    (bibarelIndustrious.markUsed).canActivate .none = false := by native_decide

/-- Theorem 45: oncePerTurn ability resets at start of turn. -/
theorem once_per_turn_resets :
    (bibarelIndustrious.markUsed.resetTurn).canActivate .none = true := by native_decide

end PokemonLean.Core.AbilityTiming
