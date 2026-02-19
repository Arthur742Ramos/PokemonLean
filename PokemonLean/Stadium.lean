-- Stadium Cards and Field Effects
-- PokemonLean: Stadium mechanics, field effects, replacement rules

import PokemonLean.Basic

namespace PokemonLean.Stadium

open PokemonLean

-- ============================================================================
-- STADIUM EFFECT TYPES
-- ============================================================================

/-- Stadium effects that modify the game field for both players. -/
inductive StadiumEffect
  | modifyDamage (amount : Int)         -- Increase/decrease all damage
  | healBetweenTurns (amount : Nat)     -- Heal all Pokémon between turns
  | drawExtra (count : Nat)             -- Draw extra cards at start of turn
  | blockAbilities                       -- Path to the Peak: block Rule Box abilities
  | reduceRetreatCost (amount : Nat)    -- Beach Court: reduce retreat cost
  | searchBasic                          -- Artazon: search for Basic Pokémon
  | noEffect                            -- Placeholder / blank stadium
  deriving Repr, BEq, DecidableEq

/-- A stadium card with name and effect. -/
structure StadiumCard where
  name : String
  effect : StadiumEffect
  deriving Repr, BEq, DecidableEq

/-- The field state: at most one stadium in play. -/
structure FieldState where
  stadium : Option StadiumCard
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- COMMON STADIUMS
-- ============================================================================

def pathToThePeak : StadiumCard :=
  { name := "Path to the Peak"
  , effect := .blockAbilities }

def artazon : StadiumCard :=
  { name := "Artazon"
  , effect := .searchBasic }

def beachCourt : StadiumCard :=
  { name := "Beach Court"
  , effect := .reduceRetreatCost 1 }

def magmaBasin : StadiumCard :=
  { name := "Magma Basin"
  , effect := .modifyDamage 20 }

def templeOfSinnoh : StadiumCard :=
  { name := "Temple of Sinnoh"
  , effect := .noEffect }

def pokemonCenter : StadiumCard :=
  { name := "Pokémon Center"
  , effect := .healBetweenTurns 20 }

def researchLab : StadiumCard :=
  { name := "Research Lab"
  , effect := .drawExtra 1 }

-- ============================================================================
-- EMPTY FIELD
-- ============================================================================

def emptyField : FieldState :=
  { stadium := none }

@[simp] theorem emptyField_stadium : emptyField.stadium = none := rfl

-- ============================================================================
-- STADIUM PLACEMENT (replaces existing)
-- ============================================================================

/-- Play a new stadium. Any existing stadium is replaced (discarded). -/
def playStadium (field : FieldState) (newStadium : StadiumCard) : FieldState × Option StadiumCard :=
  let old := field.stadium
  ({ stadium := some newStadium }, old)

/-- Remove the current stadium (e.g. via trainer card). -/
def removeStadium (field : FieldState) : FieldState × Option StadiumCard :=
  let old := field.stadium
  ({ stadium := none }, old)

-- ============================================================================
-- STADIUM APPLICATION
-- ============================================================================

/-- Apply heal-between-turns stadium effect to a single Pokémon. -/
def healPokemon (pokemon : PokemonInPlay) (amount : Nat) : PokemonInPlay :=
  { pokemon with damage := pokemon.damage - amount }

/-- Apply heal-between-turns to a list of bench Pokémon. -/
def healBench (bench : List PokemonInPlay) (amount : Nat) : List PokemonInPlay :=
  bench.map (fun p => healPokemon p amount)

/-- Modify damage based on stadium effect (clamped to 0). -/
def modifyDamageAmount (baseDamage : Nat) (delta : Int) : Nat :=
  if delta ≥ 0 then baseDamage + delta.toNat
  else baseDamage - delta.natAbs

/-- Apply a stadium effect to a damage calculation. -/
def applyStadiumToDamage (effect : StadiumEffect) (baseDamage : Nat) : Nat :=
  match effect with
  | .modifyDamage delta => modifyDamageAmount baseDamage delta
  | _ => baseDamage

/-- Check whether a stadium blocks abilities (Path to the Peak). -/
def stadiumBlocksAbilities (field : FieldState) : Bool :=
  match field.stadium with
  | some s => s.effect == .blockAbilities
  | none => false

/-- Get the retreat cost reduction from the stadium. -/
def stadiumRetreatReduction (field : FieldState) : Nat :=
  match field.stadium with
  | some s =>
    match s.effect with
    | .reduceRetreatCost n => n
    | _ => 0
  | none => 0

/-- Get the extra draw count from the stadium. -/
def stadiumExtraDraw (field : FieldState) : Nat :=
  match field.stadium with
  | some s =>
    match s.effect with
    | .drawExtra n => n
    | _ => 0
  | none => 0

/-- Get the heal amount from the stadium (for between-turns healing). -/
def stadiumHealAmount (field : FieldState) : Nat :=
  match field.stadium with
  | some s =>
    match s.effect with
    | .healBetweenTurns n => n
    | _ => 0
  | none => 0

/-- Check if a stadium allows searching for Basic Pokémon. -/
def stadiumAllowsSearch (field : FieldState) : Bool :=
  match field.stadium with
  | some s => s.effect == .searchBasic
  | none => false

-- ============================================================================
-- THEOREMS: PLACEMENT RULES
-- ============================================================================

-- Playing a stadium always results in the new stadium being in play.

-- Playing a stadium returns the old stadium for discard.

-- Playing a stadium onto an empty field returns none for old.

-- Removing a stadium from empty field gives empty field.

-- Removing a stadium returns the old stadium.

-- Removing a stadium results in no stadium.

-- Play then remove yields empty field.

-- Playing a stadium twice: the second replaces the first.

-- Playing a stadium twice: the intermediate discard is s1.

-- ============================================================================
-- THEOREMS: HEAL MECHANICS
-- ============================================================================

/-- Healing reduces damage. -/
theorem healPokemon_damage_le (pokemon : PokemonInPlay) (amount : Nat) :
    (healPokemon pokemon amount).damage ≤ pokemon.damage := by
  simp [healPokemon, Nat.sub_le]

/-- Healing by 0 does nothing. -/
theorem healPokemon_zero (pokemon : PokemonInPlay) :
    healPokemon pokemon 0 = pokemon := by
  simp [healPokemon]

-- Healing preserves card.

-- Healing preserves status.

-- Healing preserves energy.

/-- healBench preserves list length. -/
theorem healBench_length (bench : List PokemonInPlay) (amount : Nat) :
    (healBench bench amount).length = bench.length := by
  simp [healBench, List.length_map]

/-- healBench with 0 preserves bench. -/
theorem healBench_zero (bench : List PokemonInPlay) :
    healBench bench 0 = bench := by
  simp [healBench, healPokemon]

/-- Healing can't make damage negative (Nat subtraction floors at 0). -/
theorem healPokemon_nonneg (pokemon : PokemonInPlay) (amount : Nat) :
    0 ≤ (healPokemon pokemon amount).damage := by
  exact Nat.zero_le _

/-- Healing with amount ≥ damage zeroes out damage. -/
theorem healPokemon_full (pokemon : PokemonInPlay) (amount : Nat) (h : pokemon.damage ≤ amount) :
    (healPokemon pokemon amount).damage = 0 := by
  simp [healPokemon, Nat.sub_eq_zero_of_le h]

-- Healing with amount < damage leaves some damage.

/-- Healing preserves damage bound. -/
theorem healPokemon_damage_le_hp (pokemon : PokemonInPlay) (amount : Nat)
    (hBound : pokemon.damage ≤ pokemon.card.hp) :
    (healPokemon pokemon amount).damage ≤ pokemon.card.hp := by
  exact Nat.le_trans (healPokemon_damage_le pokemon amount) hBound

-- ============================================================================
-- THEOREMS: DAMAGE MODIFICATION
-- ============================================================================

/-- Positive stadium modifier increases damage. -/
theorem modifyDamageAmount_pos (base : Nat) (delta : Int) (hPos : delta ≥ 0) :
    modifyDamageAmount base delta = base + delta.toNat := by
  simp [modifyDamageAmount, hPos]

/-- Zero modifier does nothing. -/
theorem modifyDamageAmount_zero (base : Nat) :
    modifyDamageAmount base 0 = base := by
  simp [modifyDamageAmount]

/-- Positive modifier increases damage. -/
theorem modifyDamageAmount_ge_of_pos (base : Nat) (delta : Int) (hPos : delta ≥ 0) :
    base ≤ modifyDamageAmount base delta := by
  simp [modifyDamageAmount, hPos, Nat.le_add_right]

/-- Negative modifier can reduce damage (bounded by 0). -/
theorem modifyDamageAmount_le_of_neg (base : Nat) (delta : Int) (hNeg : delta < 0) :
    modifyDamageAmount base delta ≤ base := by
  simp [modifyDamageAmount]
  have hNotGe : ¬ (delta ≥ 0) := Int.not_le.mpr hNeg
  simp [hNotGe, Nat.sub_le]

-- Non-damage-modifying stadiums don't change damage.


-- ============================================================================
-- THEOREMS: FIELD QUERIES
-- ============================================================================

-- Empty field does not block abilities.

-- Path to the Peak blocks abilities.

-- Artazon does not block abilities.

-- Beach Court does not block abilities.

-- Empty field retreat reduction is 0.

-- Beach Court reduces retreat by 1.

-- Path to the Peak gives 0 retreat reduction.

-- Empty field extra draw is 0.

-- Research Lab gives 1 extra draw.

-- Empty field heal amount is 0.

-- Pokémon Center heals 20 between turns.

-- Empty field doesn't allow search.

-- Artazon allows search.

-- Path to the Peak doesn't allow search.

-- ============================================================================
-- THEOREMS: STADIUM AFFECTS BOTH PLAYERS SYMMETRICALLY
-- ============================================================================

-- Stadium heal amount is independent of which player queries it.

-- Stadium retreat reduction is the same for both players.

-- Playing the same stadium on any field gives the same result stadium.

-- After removal, the field is always the same empty state.

-- ============================================================================
-- THEOREMS: REPLACEMENT CHAIN
-- ============================================================================

-- Playing n stadiums in sequence: only the last one is in play.

-- Three stadiums: only the third survives.

-- Remove after play yields empty.

-- Play after remove installs the stadium.

-- ============================================================================
-- THEOREMS: STADIUM EFFECT CLASSIFICATION
-- ============================================================================

/-- A stadium either modifies damage or doesn't. -/
theorem applyStadiumToDamage_cases (effect : StadiumEffect) (base : Nat) :
    (∃ delta, effect = .modifyDamage delta ∧
        applyStadiumToDamage effect base = modifyDamageAmount base delta) ∨
    applyStadiumToDamage effect base = base := by
  cases effect with
  | modifyDamage delta => left; exact ⟨delta, rfl, rfl⟩
  | healBetweenTurns _ => right; rfl
  | drawExtra _ => right; rfl
  | blockAbilities => right; rfl
  | reduceRetreatCost _ => right; rfl
  | searchBasic => right; rfl
  | noEffect => right; rfl

/-- If the stadium effect is not modifyDamage, damage is unchanged. -/
theorem applyStadiumToDamage_non_modify (effect : StadiumEffect) (base : Nat)
    (h : ∀ delta, effect ≠ .modifyDamage delta) :
    applyStadiumToDamage effect base = base := by
  cases effect with
  | modifyDamage delta => exact absurd rfl (h delta)
  | healBetweenTurns _ => rfl
  | drawExtra _ => rfl
  | blockAbilities => rfl
  | reduceRetreatCost _ => rfl
  | searchBasic => rfl
  | noEffect => rfl

end PokemonLean.Stadium
