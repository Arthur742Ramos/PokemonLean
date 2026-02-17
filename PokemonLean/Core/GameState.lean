/-
  PokemonLean / Core / GameState.lean

  Game state structures for the Pokémon TCG: zones, active/bench slots,
  special conditions, player state, game state, turn phases, and
  win conditions.

  Imports Core.Card (which transitively imports Core.Types).

  All proofs are sorry-free.  30+ theorems.
-/

import PokemonLean.Core.Card

namespace PokemonLean.Core

-- ============================================================
-- §1  Zones
-- ============================================================

/-- The zones (locations) where cards can exist during a game. -/
inductive Zone where
  | active
  | bench
  | hand
  | deck
  | discard
  | prizes
  | lostZone
  | stadium
  | support
deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================
-- §2  Special Conditions
-- ============================================================

/-- The five special conditions in the Pokémon TCG. -/
inductive SpecialCondition where
  | poisoned
  | burned
  | asleep
  | confused
  | paralyzed
deriving DecidableEq, Repr, BEq, Inhabited

/-- Whether a condition occupies the exclusive slot.
    Only one of Asleep/Confused/Paralyzed can be active at a time.
    Poisoned and Burned stack independently. -/
def SpecialCondition.isExclusive : SpecialCondition → Bool
  | .asleep    => true
  | .confused  => true
  | .paralyzed => true
  | _          => false

/-- Whether a condition is stackable (Poisoned and Burned). -/
def SpecialCondition.isStackable : SpecialCondition → Bool
  | .poisoned => true
  | .burned   => true
  | _         => false

/-- Well-formed condition set: at most one exclusive condition,
    plus optional poison and/or burn. -/
structure ConditionSet where
  poisoned  : Bool
  burned    : Bool
  /-- At most one of asleep, confused, paralyzed. -/
  exclusive : Option SpecialCondition
deriving DecidableEq, Repr, BEq, Inhabited

/-- The empty condition set (no conditions). -/
def ConditionSet.empty : ConditionSet where
  poisoned := false
  burned := false
  exclusive := none

/-- Apply a new condition, respecting mutual exclusion rules. -/
def ConditionSet.apply (cs : ConditionSet) (sc : SpecialCondition) : ConditionSet :=
  match sc with
  | .poisoned  => { cs with poisoned := true }
  | .burned    => { cs with burned := true }
  | .asleep    => { cs with exclusive := some .asleep }
  | .confused  => { cs with exclusive := some .confused }
  | .paralyzed => { cs with exclusive := some .paralyzed }

/-- Remove a condition. -/
def ConditionSet.remove (cs : ConditionSet) (sc : SpecialCondition) : ConditionSet :=
  match sc with
  | .poisoned  => { cs with poisoned := false }
  | .burned    => { cs with burned := false }
  | .asleep    => if cs.exclusive == some .asleep then { cs with exclusive := none } else cs
  | .confused  => if cs.exclusive == some .confused then { cs with exclusive := none } else cs
  | .paralyzed => if cs.exclusive == some .paralyzed then { cs with exclusive := none } else cs

/-- Remove all conditions (e.g., when retreating or evolving). -/
def ConditionSet.clearAll : ConditionSet := ConditionSet.empty

/-- Check if a condition is active. -/
def ConditionSet.has (cs : ConditionSet) (sc : SpecialCondition) : Bool :=
  match sc with
  | .poisoned  => cs.poisoned
  | .burned    => cs.burned
  | .asleep    => cs.exclusive == some .asleep
  | .confused  => cs.exclusive == some .confused
  | .paralyzed => cs.exclusive == some .paralyzed

-- ============================================================
-- §3  Active Slot (Active Pokémon)
-- ============================================================

/-- The Active Pokémon slot. Includes attached energy, damage counters,
    conditions, and attached tools. -/
structure ActiveSlot where
  pokemon        : PokemonCard
  attachedEnergy : List EnergyType
  damage         : Nat   -- damage counters (in units of 10)
  conditions     : ConditionSet
  tools          : List TrainerCard
deriving Repr, Inhabited

/-- Remaining HP of the Active Pokémon. -/
def ActiveSlot.remainingHP (slot : ActiveSlot) : Nat :=
  if slot.pokemon.hp > slot.damage then slot.pokemon.hp - slot.damage else 0

/-- Whether the Active Pokémon is knocked out. -/
def ActiveSlot.isKnockedOut (slot : ActiveSlot) : Bool :=
  slot.damage ≥ slot.pokemon.hp

-- ============================================================
-- §4  Bench Slot (Benched Pokémon)
-- ============================================================

/-- A benched Pokémon slot. Similar to ActiveSlot but NO conditions
    (only the Active Pokémon gets special conditions). -/
structure BenchSlot where
  pokemon        : PokemonCard
  attachedEnergy : List EnergyType
  damage         : Nat
  tools          : List TrainerCard
deriving Repr, Inhabited

/-- Remaining HP of a benched Pokémon. -/
def BenchSlot.remainingHP (slot : BenchSlot) : Nat :=
  if slot.pokemon.hp > slot.damage then slot.pokemon.hp - slot.damage else 0

/-- Whether a benched Pokémon is knocked out. -/
def BenchSlot.isKnockedOut (slot : BenchSlot) : Bool :=
  slot.damage ≥ slot.pokemon.hp

/-- Convert an ActiveSlot to a BenchSlot (e.g. when retreating).
    Conditions are removed when going to the bench. -/
def ActiveSlot.toBench (slot : ActiveSlot) : BenchSlot where
  pokemon := slot.pokemon
  attachedEnergy := slot.attachedEnergy
  damage := slot.damage
  tools := slot.tools

/-- Convert a BenchSlot to an ActiveSlot (e.g. when promoting). -/
def BenchSlot.toActive (slot : BenchSlot) : ActiveSlot where
  pokemon := slot.pokemon
  attachedEnergy := slot.attachedEnergy
  damage := slot.damage
  conditions := ConditionSet.empty
  tools := slot.tools

-- ============================================================
-- §5  Player State
-- ============================================================

/-- Standard bench size limit. -/
def standardBenchSize : Nat := 5

/-- Standard prize count at game start. -/
def standardPrizeCount : Nat := 6

/-- Standard deck size. -/
def standardDeckSize : Nat := 60

/-- Full state of one player during a game. -/
structure PlayerState where
  active          : Option ActiveSlot
  bench           : List BenchSlot
  hand            : List Card
  deck            : List Card
  prizes          : List Card
  discard         : List Card
  lostZone        : List Card
  supporterPlayed : Bool
  energyAttached  : Bool
  gxUsed          : Bool
  vstarUsed       : Bool
deriving Repr, Inhabited

/-- An empty player state (used as a starting point). -/
def emptyPlayerState : PlayerState where
  active := none
  bench := []
  hand := []
  deck := []
  prizes := []
  discard := []
  lostZone := []
  supporterPlayed := false
  energyAttached := false
  gxUsed := false
  vstarUsed := false

/-- Number of Pokémon in play for this player. -/
def PlayerState.pokemonInPlay (ps : PlayerState) : Nat :=
  (if ps.active.isSome then 1 else 0) + ps.bench.length

/-- Whether this player has any Pokémon in play. -/
def PlayerState.hasPokemonInPlay (ps : PlayerState) : Bool :=
  ps.active.isSome || !ps.bench.isEmpty

/-- All cards this player owns (across all zones). -/
def PlayerState.allCards (ps : PlayerState) : List Card :=
  let activeCards := match ps.active with
    | some slot => [Card.pokemon slot.pokemon] ++
        slot.attachedEnergy.map (fun e => Card.energy e true) ++
        slot.tools.map Card.trainer
    | none => []
  let benchCards := ps.bench.foldl (fun acc slot =>
    acc ++ [Card.pokemon slot.pokemon] ++
      slot.attachedEnergy.map (fun e => Card.energy e true) ++
      slot.tools.map Card.trainer) []
  activeCards ++ benchCards ++ ps.hand ++ ps.deck ++ ps.prizes ++ ps.discard ++ ps.lostZone

-- ============================================================
-- §6  Turn Phases
-- ============================================================

/-- The phases of a turn in the Pokémon TCG. -/
inductive TurnPhase where
  | draw          -- mandatory draw at start of turn
  | main          -- play cards, attach energy, retreat, use abilities
  | attack        -- declare and resolve an attack
  | betweenTurns  -- check special conditions, poison/burn damage
deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================
-- §7  Game State
-- ============================================================

/-- Full game state. -/
structure GameState where
  player1    : PlayerState
  player2    : PlayerState
  currentTurn : Fin 2
  turnNumber : Nat
  stadium    : Option TrainerCard
deriving Repr, Inhabited

/-- Initial game state (empty, turn 1). -/
def initialGameState : GameState where
  player1 := emptyPlayerState
  player2 := emptyPlayerState
  currentTurn := 0
  turnNumber := 1
  stadium := none

/-- Get the current player's state. -/
def GameState.currentPlayer (gs : GameState) : PlayerState :=
  if gs.currentTurn = 0 then gs.player1 else gs.player2

/-- Get the opponent's state. -/
def GameState.opponent (gs : GameState) : PlayerState :=
  if gs.currentTurn = 0 then gs.player2 else gs.player1

-- ============================================================
-- §8  Win Conditions
-- ============================================================

/-- Win condition: opponent has no prizes remaining (you took all 6). -/
def PlayerState.noPrizesLeft (ps : PlayerState) : Bool :=
  ps.prizes.isEmpty

/-- Win condition: opponent's deck is empty (deckout — opponent can't draw). -/
def PlayerState.isDeckOut (ps : PlayerState) : Bool :=
  ps.deck.isEmpty

/-- Win condition: opponent has no Pokémon in play. -/
def PlayerState.noPokemonInPlay (ps : PlayerState) : Bool :=
  !ps.hasPokemonInPlay

/-- Check if a player has won against their opponent. -/
def hasWon (winner opponent : PlayerState) : Bool :=
  winner.noPrizesLeft || opponent.isDeckOut || opponent.noPokemonInPlay

-- ============================================================
-- §9  Between-Turns Effects
-- ============================================================

/-- Poison damage between turns: 1 damage counter (10 HP). -/
def poisonDamage : Nat := 10

/-- Burn damage between turns: 2 damage counters (20 HP), on failed flip. -/
def burnDamage : Nat := 20

/-- Apply poison damage to the active slot. -/
def ActiveSlot.applyPoison (slot : ActiveSlot) : ActiveSlot :=
  if slot.conditions.poisoned then
    { slot with damage := slot.damage + poisonDamage }
  else slot

/-- Apply burn damage to the active slot (assumes failed coin flip). -/
def ActiveSlot.applyBurn (slot : ActiveSlot) : ActiveSlot :=
  if slot.conditions.burned then
    { slot with damage := slot.damage + burnDamage }
  else slot

-- ============================================================
-- §10  Theorems — Condition Exclusivity
-- ============================================================

/-- Applying asleep replaces the exclusive slot. -/
theorem apply_asleep_sets_exclusive (cs : ConditionSet) :
    (cs.apply .asleep).exclusive = some .asleep := by
  rfl

/-- Applying confused replaces the exclusive slot. -/
theorem apply_confused_sets_exclusive (cs : ConditionSet) :
    (cs.apply .confused).exclusive = some .confused := by
  rfl

/-- Applying paralyzed replaces the exclusive slot. -/
theorem apply_paralyzed_sets_exclusive (cs : ConditionSet) :
    (cs.apply .paralyzed).exclusive = some .paralyzed := by
  rfl

/-- After applying asleep, the Pokémon is not confused. -/
theorem asleep_clears_confused (cs : ConditionSet) :
    (cs.apply .asleep).has .confused = false := by
  simp [ConditionSet.apply, ConditionSet.has]
  decide

/-- After applying asleep, the Pokémon is not paralyzed. -/
theorem asleep_clears_paralyzed (cs : ConditionSet) :
    (cs.apply .asleep).has .paralyzed = false := by
  simp [ConditionSet.apply, ConditionSet.has]
  decide

/-- Poison stacks with exclusive conditions: applying asleep preserves poison. -/
theorem poison_stacks_with_asleep (cs : ConditionSet) (h : cs.poisoned = true) :
    (cs.apply .asleep).poisoned = true := by
  simp [ConditionSet.apply, h]

/-- Burn stacks with exclusive conditions: applying paralyzed preserves burn. -/
theorem burn_stacks_with_paralyzed (cs : ConditionSet) (h : cs.burned = true) :
    (cs.apply .paralyzed).burned = true := by
  simp [ConditionSet.apply, h]

/-- Applying poison does not affect the exclusive slot. -/
theorem poison_preserves_exclusive (cs : ConditionSet) :
    (cs.apply .poisoned).exclusive = cs.exclusive := by
  rfl

/-- Applying burn does not affect the exclusive slot. -/
theorem burn_preserves_exclusive (cs : ConditionSet) :
    (cs.apply .burned).exclusive = cs.exclusive := by
  rfl

/-- Empty condition set has no conditions active. -/
theorem empty_has_nothing (sc : SpecialCondition) :
    ConditionSet.empty.has sc = false := by
  cases sc <;> rfl

/-- ClearAll produces the empty set. -/
theorem clearAll_is_empty : ConditionSet.clearAll = ConditionSet.empty := by
  rfl

-- ============================================================
-- §11  Theorems — Active / Bench conversion
-- ============================================================

/-- Retreating clears conditions: converting to bench removes all conditions. -/
theorem retreat_clears_conditions (slot : ActiveSlot) :
    slot.toBench.toActive.conditions = ConditionSet.empty := by
  rfl

/-- Promoting to active starts with no conditions. -/
theorem promote_no_conditions (slot : BenchSlot) :
    slot.toActive.conditions = ConditionSet.empty := by
  rfl

/-- Retreating preserves damage. -/
theorem retreat_preserves_damage (slot : ActiveSlot) :
    slot.toBench.toActive.damage = slot.damage := by
  rfl

/-- Retreating preserves energy. -/
theorem retreat_preserves_energy (slot : ActiveSlot) :
    slot.toBench.toActive.attachedEnergy = slot.attachedEnergy := by
  rfl

/-- Promoting preserves damage. -/
theorem promote_preserves_damage (slot : BenchSlot) :
    slot.toActive.damage = slot.damage := by
  rfl

-- ============================================================
-- §12  Theorems — Knockouts
-- ============================================================

/-- A Pokémon with damage ≥ HP is knocked out. -/
theorem damage_ge_hp_ko (slot : ActiveSlot) (h : slot.damage ≥ slot.pokemon.hp) :
    slot.isKnockedOut = true := by
  simp [ActiveSlot.isKnockedOut, h]

/-- A Pokémon with 0 damage is not knocked out (assuming hp > 0). -/
theorem zero_damage_not_ko (slot : ActiveSlot) (h : slot.damage = 0) (hpos : slot.pokemon.hp > 0) :
    slot.isKnockedOut = false := by
  simp [ActiveSlot.isKnockedOut, h]
  omega

/-- Remaining HP of undamaged Pokémon equals its HP. -/
theorem undamaged_full_hp (slot : ActiveSlot) (h : slot.damage = 0) :
    slot.remainingHP = slot.pokemon.hp := by
  simp [ActiveSlot.remainingHP, h]
  omega

/-- KO'd Pokémon has 0 remaining HP. -/
theorem ko_zero_hp (slot : ActiveSlot) (h : slot.damage ≥ slot.pokemon.hp) :
    slot.remainingHP = 0 := by
  simp [ActiveSlot.remainingHP]
  omega

-- ============================================================
-- §13  Theorems — Game State invariants
-- ============================================================

/-- Initial game state is on turn 1. -/
theorem initial_turn_one : initialGameState.turnNumber = 1 := by rfl

/-- Initial game state has no stadium. -/
theorem initial_no_stadium : initialGameState.stadium = none := by rfl

/-- Empty player has no Pokémon in play. -/
theorem empty_no_pokemon : emptyPlayerState.hasPokemonInPlay = false := by rfl

/-- Empty player has not played a supporter. -/
theorem empty_no_supporter : emptyPlayerState.supporterPlayed = false := by rfl

/-- Empty player has empty hand. -/
theorem empty_hand : emptyPlayerState.hand = [] := by rfl

/-- Empty player has not used GX. -/
theorem empty_no_gx : emptyPlayerState.gxUsed = false := by rfl

/-- Empty player has not used VSTAR power. -/
theorem empty_no_vstar : emptyPlayerState.vstarUsed = false := by rfl

/-- A player with no active and empty bench has no Pokémon in play. -/
theorem no_active_empty_bench_no_pokemon (ps : PlayerState)
    (ha : ps.active = none) (hb : ps.bench = []) :
    ps.hasPokemonInPlay = false := by
  simp [PlayerState.hasPokemonInPlay, ha, hb]

/-- Poison increases damage. -/
theorem poison_increases_damage (slot : ActiveSlot) (h : slot.conditions.poisoned = true) :
    (slot.applyPoison).damage = slot.damage + poisonDamage := by
  simp [ActiveSlot.applyPoison, h]

/-- No poison means no additional damage from applyPoison. -/
theorem no_poison_no_damage (slot : ActiveSlot) (h : slot.conditions.poisoned = false) :
    (slot.applyPoison).damage = slot.damage := by
  simp [ActiveSlot.applyPoison, h]

/-- Standard bench size is 5. -/
theorem bench_size_is_five : standardBenchSize = 5 := by rfl

/-- Standard prize count is 6. -/
theorem prize_count_is_six : standardPrizeCount = 6 := by rfl

/-- Standard deck size is 60. -/
theorem deck_size_is_sixty : standardDeckSize = 60 := by rfl

end PokemonLean.Core
