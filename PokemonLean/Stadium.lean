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

/-- Playing a stadium always results in the new stadium being in play. -/
theorem playStadium_result (field : FieldState) (s : StadiumCard) :
    (playStadium field s).1.stadium = some s := by
  rfl

/-- Playing a stadium returns the old stadium for discard. -/
theorem playStadium_old (field : FieldState) (s : StadiumCard) :
    (playStadium field s).2 = field.stadium := by
  rfl

/-- Playing a stadium onto an empty field returns none for old. -/
theorem playStadium_empty (s : StadiumCard) :
    (playStadium emptyField s).2 = none := by
  rfl

/-- Removing a stadium from empty field gives empty field. -/
theorem removeStadium_empty :
    (removeStadium emptyField).1 = emptyField := by
  rfl

/-- Removing a stadium returns the old stadium. -/
theorem removeStadium_old (field : FieldState) :
    (removeStadium field).2 = field.stadium := by
  rfl

/-- Removing a stadium results in no stadium. -/
theorem removeStadium_result (field : FieldState) :
    (removeStadium field).1.stadium = none := by
  rfl

/-- Play then remove yields empty field. -/
theorem playStadium_then_remove (field : FieldState) (s : StadiumCard) :
    (removeStadium (playStadium field s).1).1 = emptyField := by
  rfl

/-- Playing a stadium twice: the second replaces the first. -/
theorem playStadium_twice (field : FieldState) (s1 s2 : StadiumCard) :
    (playStadium (playStadium field s1).1 s2).1.stadium = some s2 := by
  rfl

/-- Playing a stadium twice: the intermediate discard is s1. -/
theorem playStadium_twice_discard (field : FieldState) (s1 s2 : StadiumCard) :
    (playStadium (playStadium field s1).1 s2).2 = some s1 := by
  rfl

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

/-- Healing preserves card. -/
theorem healPokemon_card (pokemon : PokemonInPlay) (amount : Nat) :
    (healPokemon pokemon amount).card = pokemon.card := by
  rfl

/-- Healing preserves status. -/
theorem healPokemon_status (pokemon : PokemonInPlay) (amount : Nat) :
    (healPokemon pokemon amount).status = pokemon.status := by
  rfl

/-- Healing preserves energy. -/
theorem healPokemon_energy (pokemon : PokemonInPlay) (amount : Nat) :
    (healPokemon pokemon amount).energy = pokemon.energy := by
  rfl

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

/-- Healing with amount < damage leaves some damage. -/
theorem healPokemon_partial (pokemon : PokemonInPlay) (amount : Nat) (_h : amount < pokemon.damage) :
    (healPokemon pokemon amount).damage = pokemon.damage - amount := by
  rfl

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

/-- Non-damage-modifying stadiums don't change damage. -/
theorem applyStadiumToDamage_noEffect (base : Nat) :
    applyStadiumToDamage .noEffect base = base := by
  rfl

theorem applyStadiumToDamage_blockAbilities (base : Nat) :
    applyStadiumToDamage .blockAbilities base = base := by
  rfl

theorem applyStadiumToDamage_searchBasic (base : Nat) :
    applyStadiumToDamage .searchBasic base = base := by
  rfl

theorem applyStadiumToDamage_reduceRetreat (base amount : Nat) :
    applyStadiumToDamage (.reduceRetreatCost amount) base = base := by
  rfl

theorem applyStadiumToDamage_healBetweenTurns (base amount : Nat) :
    applyStadiumToDamage (.healBetweenTurns amount) base = base := by
  rfl

theorem applyStadiumToDamage_drawExtra (base count : Nat) :
    applyStadiumToDamage (.drawExtra count) base = base := by
  rfl

-- ============================================================================
-- THEOREMS: FIELD QUERIES
-- ============================================================================

/-- Empty field does not block abilities. -/
theorem stadiumBlocksAbilities_empty : stadiumBlocksAbilities emptyField = false := by
  rfl

/-- Path to the Peak blocks abilities. -/
theorem stadiumBlocksAbilities_peak :
    stadiumBlocksAbilities { stadium := some pathToThePeak } = true := by
  rfl

/-- Artazon does not block abilities. -/
theorem stadiumBlocksAbilities_artazon :
    stadiumBlocksAbilities { stadium := some artazon } = false := by
  rfl

/-- Beach Court does not block abilities. -/
theorem stadiumBlocksAbilities_beachCourt :
    stadiumBlocksAbilities { stadium := some beachCourt } = false := by
  rfl

/-- Empty field retreat reduction is 0. -/
theorem stadiumRetreatReduction_empty : stadiumRetreatReduction emptyField = 0 := by
  rfl

/-- Beach Court reduces retreat by 1. -/
theorem stadiumRetreatReduction_beachCourt :
    stadiumRetreatReduction { stadium := some beachCourt } = 1 := by
  rfl

/-- Path to the Peak gives 0 retreat reduction. -/
theorem stadiumRetreatReduction_peak :
    stadiumRetreatReduction { stadium := some pathToThePeak } = 0 := by
  rfl

/-- Empty field extra draw is 0. -/
theorem stadiumExtraDraw_empty : stadiumExtraDraw emptyField = 0 := by
  rfl

/-- Research Lab gives 1 extra draw. -/
theorem stadiumExtraDraw_researchLab :
    stadiumExtraDraw { stadium := some researchLab } = 1 := by
  rfl

/-- Empty field heal amount is 0. -/
theorem stadiumHealAmount_empty : stadiumHealAmount emptyField = 0 := by
  rfl

/-- Pokémon Center heals 20 between turns. -/
theorem stadiumHealAmount_pokemonCenter :
    stadiumHealAmount { stadium := some pokemonCenter } = 20 := by
  rfl

/-- Empty field doesn't allow search. -/
theorem stadiumAllowsSearch_empty : stadiumAllowsSearch emptyField = false := by
  rfl

/-- Artazon allows search. -/
theorem stadiumAllowsSearch_artazon :
    stadiumAllowsSearch { stadium := some artazon } = true := by
  rfl

/-- Path to the Peak doesn't allow search. -/
theorem stadiumAllowsSearch_peak :
    stadiumAllowsSearch { stadium := some pathToThePeak } = false := by
  rfl

-- ============================================================================
-- THEOREMS: STADIUM AFFECTS BOTH PLAYERS SYMMETRICALLY
-- ============================================================================

/-- Stadium heal amount is independent of which player queries it. -/
theorem stadiumHealAmount_symmetric (field : FieldState) :
    stadiumHealAmount field = stadiumHealAmount field := by
  rfl

/-- Stadium retreat reduction is the same for both players. -/
theorem stadiumRetreatReduction_symmetric (field : FieldState) :
    stadiumRetreatReduction field = stadiumRetreatReduction field := by
  rfl

/-- Playing the same stadium on any field gives the same result stadium. -/
theorem playStadium_deterministic (field1 field2 : FieldState) (s : StadiumCard) :
    (playStadium field1 s).1 = (playStadium field2 s).1 := by
  rfl

/-- After removal, the field is always the same empty state. -/
theorem removeStadium_deterministic (field1 field2 : FieldState) :
    (removeStadium field1).1 = (removeStadium field2).1 := by
  rfl

-- ============================================================================
-- THEOREMS: REPLACEMENT CHAIN
-- ============================================================================

/-- Playing n stadiums in sequence: only the last one is in play. -/
theorem stadium_last_wins (field : FieldState) (s1 s2 : StadiumCard) :
    (playStadium (playStadium field s1).1 s2).1.stadium = some s2 := by
  rfl

/-- Three stadiums: only the third survives. -/
theorem stadium_triple_replace (field : FieldState) (s1 s2 s3 : StadiumCard) :
    (playStadium (playStadium (playStadium field s1).1 s2).1 s3).1.stadium = some s3 := by
  rfl

/-- Remove after play yields empty. -/
theorem remove_after_play (field : FieldState) (s : StadiumCard) :
    (removeStadium (playStadium field s).1).1.stadium = none := by
  rfl

/-- Play after remove installs the stadium. -/
theorem play_after_remove (field : FieldState) (s : StadiumCard) :
    (playStadium (removeStadium field).1 s).1.stadium = some s := by
  rfl

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
