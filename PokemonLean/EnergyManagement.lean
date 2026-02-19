import PokemonLean.Basic

namespace PokemonLean.EnergyManagement

open PokemonLean

-- ============================================================================
-- SPECIAL ENERGY TYPES
-- ============================================================================

inductive SpecialEnergyKind
  | doubleColorless   -- provides 2 colorless energy
  | rainbow           -- provides any type but deals 10 damage
  | counterEnergy     -- provides 2 of any type when behind on prizes
  | twinEnergy        -- provides 2 colorless to non-V Pokémon
  deriving Repr, BEq, DecidableEq

structure SpecialEnergy where
  kind : SpecialEnergyKind
  deriving Repr, BEq, DecidableEq

/-- How many units of energy a special energy card provides -/
def SpecialEnergyKind.energyValue : SpecialEnergyKind → Nat
  | .doubleColorless => 2
  | .rainbow         => 1
  | .counterEnergy   => 2
  | .twinEnergy      => 2

-- ============================================================================
-- ENERGY CARD REPRESENTATION
-- ============================================================================

inductive EnergyCard
  | basic (energyType : EnergyType)
  | special (kind : SpecialEnergyKind)
  deriving Repr, BEq, DecidableEq

def EnergyCard.energyValue : EnergyCard → Nat
  | .basic _    => 1
  | .special k  => k.energyValue

-- ============================================================================
-- TURN-TRACKED STATE FOR ENERGY ATTACHMENT
-- ============================================================================

structure EnergyAttachState where
  turnNumber : Nat
  energyAttachedThisTurn : Nat   -- how many basic energy attached this turn
  accelerationUsed : Bool        -- whether an acceleration ability was used
  deriving Repr, BEq, DecidableEq

def initialAttachState (turn : Nat) : EnergyAttachState :=
  { turnNumber := turn, energyAttachedThisTurn := 0, accelerationUsed := false }

-- ============================================================================
-- ONE ENERGY PER TURN RULE
-- ============================================================================

/-- Can we attach a basic energy card this turn? -/
def canAttachEnergy (state : EnergyAttachState) : Prop :=
  state.energyAttachedThisTurn = 0

instance (state : EnergyAttachState) : Decidable (canAttachEnergy state) :=
  inferInstanceAs (Decidable (state.energyAttachedThisTurn = 0))

/-- Attach a basic energy card, updating the turn state -/
def attachEnergy (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : EnergyAttachState) : Option (PokemonInPlay × EnergyAttachState) :=
  if state.energyAttachedThisTurn = 0 then
    some ({ pokemon with energy := pokemon.energy ++ [energyType] },
          { state with energyAttachedThisTurn := state.energyAttachedThisTurn + 1 })
  else
    none

-- ============================================================================
-- ENERGY ACCELERATION (ATTACH EXTRA)
-- ============================================================================

/-- An acceleration ability allows one extra energy attachment -/
def canAccelerate (state : EnergyAttachState) : Prop :=
  state.accelerationUsed = false

instance (state : EnergyAttachState) : Decidable (canAccelerate state) :=
  inferInstanceAs (Decidable (state.accelerationUsed = false))

/-- Attach energy via acceleration ability, bypassing the once-per-turn limit -/
def accelerateEnergy (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : EnergyAttachState) : Option (PokemonInPlay × EnergyAttachState) :=
  if state.accelerationUsed = false then
    some ({ pokemon with energy := pokemon.energy ++ [energyType] },
          { state with accelerationUsed := true })
  else
    none

-- ============================================================================
-- ENERGY REMOVAL EFFECTS
-- ============================================================================

/-- Remove one energy of a specific type from a Pokémon -/
def removeEnergy (pokemon : PokemonInPlay) (energyType : EnergyType) : Option PokemonInPlay :=
  match removeFirstEnergy energyType pokemon.energy with
  | some remaining => some { pokemon with energy := remaining }
  | none => none

/-- Remove all energy from a Pokémon -/
def removeAllEnergy (pokemon : PokemonInPlay) : PokemonInPlay × List EnergyType :=
  ({ pokemon with energy := [] }, pokemon.energy)

/-- Remove n energy cards from a Pokémon (taking from the front) -/
def removeNEnergy (pokemon : PokemonInPlay) (n : Nat) : PokemonInPlay × List EnergyType :=
  let removed := pokemon.energy.take n
  let remaining := pokemon.energy.drop n
  ({ pokemon with energy := remaining }, removed)

-- ============================================================================
-- GAME-WIDE ENERGY TRACKING (CONSERVATION)
-- ============================================================================

/-- Count total energy cards across a player's entire board -/
def playerBoardEnergy (player : PlayerState) : Nat :=
  let activeEnergy := match player.active with
    | none => 0
    | some pokemon => pokemon.energy.length
  let benchEnergy := (player.bench.map (fun p => p.energy.length)).sum
  activeEnergy + benchEnergy

/-- Count energy cards in all zones for a player -/
def playerTotalEnergy (player : PlayerState) : Nat :=
  playerBoardEnergy player

-- ============================================================================
-- TURN STATE RESET
-- ============================================================================

/-- Reset attachment state for a new turn -/
def newTurnState (turn : Nat) : EnergyAttachState :=
  initialAttachState turn

-- ============================================================================
-- attachEnergy THEOREMS
-- ============================================================================

theorem attachEnergy_adds_energy (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : EnergyAttachState) (pokemon' : PokemonInPlay) (state' : EnergyAttachState)
    (h : attachEnergy pokemon energyType state = some (pokemon', state')) :
    pokemon'.energy = pokemon.energy ++ [energyType] := by
  unfold attachEnergy at h
  split at h
  · simp at h; obtain ⟨hp, _⟩ := h; exact hp ▸ rfl
  · simp at h

theorem attachEnergy_increments_count (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : EnergyAttachState) (pokemon' : PokemonInPlay) (state' : EnergyAttachState)
    (h : attachEnergy pokemon energyType state = some (pokemon', state')) :
    state'.energyAttachedThisTurn = state.energyAttachedThisTurn + 1 := by
  unfold attachEnergy at h
  split at h
  · simp at h; obtain ⟨_, hs⟩ := h; exact hs ▸ rfl
  · simp at h

theorem attachEnergy_requires_zero (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : EnergyAttachState) (result : PokemonInPlay × EnergyAttachState)
    (h : attachEnergy pokemon energyType state = some result) :
    canAttachEnergy state := by
  unfold attachEnergy at h
  split at h
  · assumption
  · simp at h

theorem attachEnergy_once_then_blocked (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : EnergyAttachState) (pokemon' : PokemonInPlay) (state' : EnergyAttachState)
    (h : attachEnergy pokemon energyType state = some (pokemon', state')) :
    attachEnergy pokemon' energyType state' = none := by
  unfold attachEnergy at h
  split at h
  case isTrue hZero =>
    simp at h
    obtain ⟨_, hs⟩ := h
    unfold attachEnergy
    subst hs
    simp [hZero]
  case isFalse => simp at h

theorem attachEnergy_length (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : EnergyAttachState) (pokemon' : PokemonInPlay) (state' : EnergyAttachState)
    (h : attachEnergy pokemon energyType state = some (pokemon', state')) :
    pokemon'.energy.length = pokemon.energy.length + 1 := by
  have hE := attachEnergy_adds_energy pokemon energyType state pokemon' state' h
  simp [hE]

theorem attachEnergy_preserves_damage (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : EnergyAttachState) (pokemon' : PokemonInPlay) (state' : EnergyAttachState)
    (h : attachEnergy pokemon energyType state = some (pokemon', state')) :
    pokemon'.damage = pokemon.damage := by
  unfold attachEnergy at h
  split at h
  · simp at h; obtain ⟨hp, _⟩ := h; exact hp ▸ rfl
  · simp at h

theorem attachEnergy_preserves_card (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : EnergyAttachState) (pokemon' : PokemonInPlay) (state' : EnergyAttachState)
    (h : attachEnergy pokemon energyType state = some (pokemon', state')) :
    pokemon'.card = pokemon.card := by
  unfold attachEnergy at h
  split at h
  · simp at h; obtain ⟨hp, _⟩ := h; exact hp ▸ rfl
  · simp at h

theorem attachEnergy_preserves_status (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : EnergyAttachState) (pokemon' : PokemonInPlay) (state' : EnergyAttachState)
    (h : attachEnergy pokemon energyType state = some (pokemon', state')) :
    pokemon'.status = pokemon.status := by
  unfold attachEnergy at h
  split at h
  · simp at h; obtain ⟨hp, _⟩ := h; exact hp ▸ rfl
  · simp at h

-- ============================================================================
-- accelerateEnergy THEOREMS
-- ============================================================================

theorem accelerateEnergy_adds_energy (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : EnergyAttachState) (pokemon' : PokemonInPlay) (state' : EnergyAttachState)
    (h : accelerateEnergy pokemon energyType state = some (pokemon', state')) :
    pokemon'.energy = pokemon.energy ++ [energyType] := by
  unfold accelerateEnergy at h
  split at h
  · simp at h; obtain ⟨hp, _⟩ := h; exact hp ▸ rfl
  · simp at h

theorem accelerateEnergy_sets_flag (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : EnergyAttachState) (pokemon' : PokemonInPlay) (state' : EnergyAttachState)
    (h : accelerateEnergy pokemon energyType state = some (pokemon', state')) :
    state'.accelerationUsed = true := by
  unfold accelerateEnergy at h
  split at h
  · simp at h; obtain ⟨_, hs⟩ := h; exact hs ▸ rfl
  · simp at h

theorem accelerateEnergy_requires_unused (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : EnergyAttachState) (result : PokemonInPlay × EnergyAttachState)
    (h : accelerateEnergy pokemon energyType state = some result) :
    canAccelerate state := by
  unfold accelerateEnergy at h
  split at h
  · assumption
  · simp at h

theorem accelerateEnergy_once_then_blocked (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : EnergyAttachState) (pokemon' : PokemonInPlay) (state' : EnergyAttachState)
    (h : accelerateEnergy pokemon energyType state = some (pokemon', state')) :
    accelerateEnergy pokemon' energyType state' = none := by
  have hFlag := accelerateEnergy_sets_flag pokemon energyType state pokemon' state' h
  unfold accelerateEnergy
  simp [hFlag]

theorem accelerateEnergy_length (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : EnergyAttachState) (pokemon' : PokemonInPlay) (state' : EnergyAttachState)
    (h : accelerateEnergy pokemon energyType state = some (pokemon', state')) :
    pokemon'.energy.length = pokemon.energy.length + 1 := by
  have hE := accelerateEnergy_adds_energy pokemon energyType state pokemon' state' h
  simp [hE]

-- ============================================================================
-- ENERGY REMOVAL THEOREMS
-- ============================================================================

theorem removeEnergy_decrements_length (pokemon : PokemonInPlay) (energyType : EnergyType)
    (pokemon' : PokemonInPlay) (h : removeEnergy pokemon energyType = some pokemon') :
    pokemon'.energy.length + 1 = pokemon.energy.length := by
  unfold removeEnergy at h
  cases hRem : removeFirstEnergy energyType pokemon.energy with
  | none => simp [hRem] at h
  | some remaining =>
    simp [hRem] at h
    cases h
    exact removeFirstEnergy_length energyType pokemon.energy remaining hRem

theorem removeEnergy_preserves_card (pokemon : PokemonInPlay) (energyType : EnergyType)
    (pokemon' : PokemonInPlay) (h : removeEnergy pokemon energyType = some pokemon') :
    pokemon'.card = pokemon.card := by
  unfold removeEnergy at h
  cases hRem : removeFirstEnergy energyType pokemon.energy with
  | none => simp [hRem] at h
  | some remaining => simp [hRem] at h; cases h; rfl

theorem removeEnergy_preserves_damage (pokemon : PokemonInPlay) (energyType : EnergyType)
    (pokemon' : PokemonInPlay) (h : removeEnergy pokemon energyType = some pokemon') :
    pokemon'.damage = pokemon.damage := by
  unfold removeEnergy at h
  cases hRem : removeFirstEnergy energyType pokemon.energy with
  | none => simp [hRem] at h
  | some remaining => simp [hRem] at h; cases h; rfl

theorem removeAllEnergy_clears (pokemon : PokemonInPlay) :
    (removeAllEnergy pokemon).1.energy = [] := by
  simp [removeAllEnergy]

theorem removeAllEnergy_returns_all (pokemon : PokemonInPlay) :
    (removeAllEnergy pokemon).2 = pokemon.energy := by
  simp [removeAllEnergy]

theorem removeAllEnergy_preserves_card (pokemon : PokemonInPlay) :
    (removeAllEnergy pokemon).1.card = pokemon.card := by
  simp [removeAllEnergy]

theorem removeAllEnergy_preserves_damage (pokemon : PokemonInPlay) :
    (removeAllEnergy pokemon).1.damage = pokemon.damage := by
  simp [removeAllEnergy]

-- ============================================================================
-- removeNEnergy THEOREMS
-- ============================================================================

theorem removeNEnergy_split (pokemon : PokemonInPlay) (n : Nat) :
    let result := removeNEnergy pokemon n
    result.1.energy ++ result.2 = pokemon.energy.drop n ++ pokemon.energy.take n := by
  simp [removeNEnergy]

theorem removeNEnergy_total_length (pokemon : PokemonInPlay) (n : Nat) :
    let result := removeNEnergy pokemon n
    result.1.energy.length + result.2.length = pokemon.energy.length := by
  simp [removeNEnergy]
  omega

theorem removeNEnergy_preserves_card (pokemon : PokemonInPlay) (n : Nat) :
    (removeNEnergy pokemon n).1.card = pokemon.card := by
  simp [removeNEnergy]

-- ============================================================================
-- TURN STATE THEOREMS
-- ============================================================================

theorem newTurnState_allows_attach (turn : Nat) :
    canAttachEnergy (newTurnState turn) := by
  simp [newTurnState, initialAttachState, canAttachEnergy]

theorem newTurnState_allows_accelerate (turn : Nat) :
    canAccelerate (newTurnState turn) := by
  simp [newTurnState, initialAttachState, canAccelerate]

theorem newTurnState_zero_attached (turn : Nat) :
    (newTurnState turn).energyAttachedThisTurn = 0 := by
  simp [newTurnState, initialAttachState]

theorem newTurnState_turn_number (turn : Nat) :
    (newTurnState turn).turnNumber = turn := by
  simp [newTurnState, initialAttachState]

-- ============================================================================
-- SPECIAL ENERGY VALUE THEOREMS
-- ============================================================================


theorem special_energy_value_pos (k : SpecialEnergyKind) :
    k.energyValue > 0 := by
  cases k <;> decide


theorem special_energy_ge_basic (k : SpecialEnergyKind) (t : EnergyType) :
    (EnergyCard.special k).energyValue ≥ (EnergyCard.basic t).energyValue := by
  cases k <;> simp [EnergyCard.energyValue, SpecialEnergyKind.energyValue]

-- ============================================================================
-- ENERGY CONSERVATION THEOREMS
-- ============================================================================

/-- Attaching energy to the active Pokémon increases board energy by 1 -/
theorem attach_increases_board_energy (player : PlayerState) (pokemon : PokemonInPlay)
    (energyType : EnergyType) (state : EnergyAttachState)
    (pokemon' : PokemonInPlay) (state' : EnergyAttachState)
    (hActive : player.active = some pokemon)
    (hAttach : attachEnergy pokemon energyType state = some (pokemon', state')) :
    playerBoardEnergy { player with active := some pokemon' } =
    playerBoardEnergy player + 1 := by
  have hLen := attachEnergy_length pokemon energyType state pokemon' state' hAttach
  simp [playerBoardEnergy, hActive]
  omega

/-- Removing energy from active Pokémon decreases board energy by 1 -/
theorem remove_decreases_board_energy (player : PlayerState) (pokemon : PokemonInPlay)
    (energyType : EnergyType) (pokemon' : PokemonInPlay)
    (hActive : player.active = some pokemon)
    (hRemove : removeEnergy pokemon energyType = some pokemon') :
    playerBoardEnergy { player with active := some pokemon' } + 1 =
    playerBoardEnergy player := by
  have hLen := removeEnergy_decrements_length pokemon energyType pokemon' hRemove
  simp [playerBoardEnergy, hActive]
  omega

/-- Removing all energy sets board energy to just bench energy -/
theorem removeAll_board_energy (player : PlayerState) (pokemon : PokemonInPlay)
    (_hActive : player.active = some pokemon) :
    playerBoardEnergy { player with active := some (removeAllEnergy pokemon).1 } =
    (player.bench.map (fun p => p.energy.length)).sum := by
  simp [playerBoardEnergy, removeAllEnergy]

end PokemonLean.EnergyManagement
