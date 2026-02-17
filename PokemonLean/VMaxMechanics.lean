/-
  PokemonLean / VMaxMechanics.lean

  VMAX card mechanics for the Pokémon TCG:
  - VMAX evolves from V (Gigantamax/Dynamax forms)
  - Gives 3 prizes when KO'd
  - HP ranges 300-340
  - G-Max moves (powerful attacks)
  - Interaction with V-rule cards
  - Cannot have more than 1 VMAX active in some formats

-/

namespace VMaxMechanics
-- ============================================================================
-- §2  VMAX Types
-- ============================================================================

/-- Pokémon V variant types. -/
inductive VVariant where
  | vBasic   : VVariant    -- Regular V card
  | vStar    : VVariant    -- V-STAR
  | vMax     : VVariant    -- VMAX (Gigantamax/Dynamax)
  | vUnion   : VVariant    -- V-UNION
deriving DecidableEq, Repr, BEq

/-- Dynamax form type. -/
inductive DmaxForm where
  | dynamax    : DmaxForm   -- Generic Dynamax (larger)
  | gigantamax : DmaxForm   -- Specific Gigantamax form
deriving DecidableEq, Repr, BEq

/-- Energy types for attack costs. -/
inductive EnergyType where
  | fire | water | grass | lightning | psychic | fighting
  | darkness | metal | dragon | colorless | fairy
deriving DecidableEq, Repr, BEq

/-- A G-Max or Max attack. -/
structure GMaxAttack where
  name       : String
  damage     : Nat
  energyCost : List EnergyType
  isGMax     : Bool         -- true = G-Max move, false = regular Max Move
deriving DecidableEq, Repr, BEq

/-- Prize count rules for V variants. -/
def prizeCount : VVariant → Nat
  | .vBasic  => 2
  | .vStar   => 2
  | .vMax    => 3
  | .vUnion  => 2

/-- VMAX HP ranges: 300-340 typically. -/
def vmaxMinHP : Nat := 300
def vmaxMaxHP : Nat := 340

/-- Check if HP is in valid VMAX range. -/
def validVMaxHP (hp : Nat) : Bool :=
  hp ≥ vmaxMinHP && hp ≤ vmaxMaxHP

-- ============================================================================
-- §3  Game State for VMAX
-- ============================================================================

structure VMaxCard where
  name     : String
  hp       : Nat
  form     : DmaxForm
  attacks  : List GMaxAttack
  evolvesFrom : String       -- Name of V card it evolves from
deriving DecidableEq, Repr, BEq

inductive CardZone where
  | deck | hand | active | bench | discard | prizes
deriving DecidableEq, Repr, BEq

structure VMaxGameState where
  vCardInPlay    : Bool       -- Is the base V card in play?
  vmaxEvolved    : Bool       -- Has the V been evolved to VMAX?
  currentHP      : Nat
  maxHP          : Nat
  zone           : CardZone
  damageCounters : Nat
  attachedEnergy : List EnergyType
  turnNumber     : Nat
  prizesRemaining : Nat
  opponentPrizes : Nat
  form           : DmaxForm
deriving DecidableEq, Repr, BEq

def VMaxGameState.initial : VMaxGameState :=
  { vCardInPlay := false
  , vmaxEvolved := false
  , currentHP := 0
  , maxHP := 0
  , zone := .deck
  , damageCounters := 0
  , attachedEnergy := []
  , turnNumber := 1
  , prizesRemaining := 6
  , opponentPrizes := 6
  , form := .dynamax }

-- ============================================================================
-- §4  Evolution: V → VMAX
-- ============================================================================

-- ============================================================================
-- §5  VMAX Theorems
-- ============================================================================

/-- Theorem 1: VMAX gives 3 prizes when KO'd. -/
theorem vmax_gives_three_prizes : prizeCount VVariant.vMax = 3 := by
  simp [prizeCount]

/-- Theorem 2: Regular V gives only 2 prizes. -/
theorem v_basic_gives_two_prizes : prizeCount VVariant.vBasic = 2 := by
  simp [prizeCount]

/-- Theorem 3: VMAX gives more prizes than V. -/
theorem vmax_more_prizes_than_v : prizeCount VVariant.vMax > prizeCount VVariant.vBasic := by
  simp [prizeCount]


/-- Theorem 6: VMAX HP minimum is 300. -/
theorem vmax_min_hp_is_300 : vmaxMinHP = 300 := by
  simp [vmaxMinHP]

/-- Theorem 7: Valid VMAX HP of 320 is within range. -/
theorem hp_320_valid : validVMaxHP 320 = true := by
  native_decide

/-- Theorem 8: HP of 200 is NOT valid VMAX. -/
theorem hp_200_invalid : validVMaxHP 200 = false := by
  native_decide

/-- Theorem 9: Prize count never exceeds 3. -/
theorem prize_count_le_three (v : VVariant) : prizeCount v ≤ 3 := by
  cases v <;> simp [prizeCount]

/-- Theorem 10: Prize count is always at least 2 for all V variants. -/
theorem prize_count_ge_two (v : VVariant) : prizeCount v ≥ 2 := by
  cases v <;> simp [prizeCount]

-- ============================================================================
-- §6  Damage and KO Mechanics
-- ============================================================================

/-- Check if VMAX is KO'd. -/
def isKOd (s : VMaxGameState) : Bool :=
  s.damageCounters ≥ s.maxHP


-- ============================================================================
-- §7  G-Max Attacks
-- ============================================================================

/-- A G-Max attack does at least as much as its base. -/
structure GMaxBoost where
  baseAttack : GMaxAttack
  gmaxAttack : GMaxAttack
  boostProof : gmaxAttack.damage ≥ baseAttack.damage


-- ============================================================================
-- §8  Format Rules: VMAX limits
-- ============================================================================

/-- Format types with different VMAX rules. -/
inductive Format where
  | standard  : Format   -- max 4 copies of any card
  | expanded  : Format   -- max 4 copies
  | unlimited : Format   -- no restrictions
deriving DecidableEq, Repr, BEq

/-- Max VMAX copies allowed in a deck. -/
def maxVMaxCopies : Format → Nat
  | .standard  => 4
  | .expanded  => 4
  | .unlimited => 60  -- effectively unlimited

/-- Theorem 13: Standard format allows max 4 VMAX copies. -/
theorem standard_max_vmax_copies : maxVMaxCopies Format.standard = 4 := by
  simp [maxVMaxCopies]

/-- Theorem 14: Unlimited format allows more than standard. -/
theorem unlimited_more_than_standard :
    maxVMaxCopies Format.unlimited > maxVMaxCopies Format.standard := by
  simp [maxVMaxCopies]

-- ============================================================================
-- §9  VMAX vs Other V Variants
-- ============================================================================

/-- V-STAR also gives 2, like basic V. -/
theorem vstar_same_as_v : prizeCount VVariant.vStar = prizeCount VVariant.vBasic := by
  simp [prizeCount]

/-- V-UNION also gives 2. -/
theorem vunion_same_as_v : prizeCount VVariant.vUnion = prizeCount VVariant.vBasic := by
  simp [prizeCount]

/-- Theorem 15: VMAX is unique in giving 3 prizes among V variants. -/
theorem vmax_unique_three_prizes (v : VVariant) (h : prizeCount v = 3) : v = VVariant.vMax := by
  cases v <;> simp_all [prizeCount]

-- ============================================================================
-- §10  Path Coherence for VMAX mechanics
-- ============================================================================


/-- Theorem 17: VMAX max HP is 340. -/
theorem vmax_max_hp_is_340 : vmaxMaxHP = 340 := by
  simp [vmaxMaxHP]

/-- Theorem 18: Gigantamax and Dynamax are distinct forms. -/
theorem gmax_neq_dmax : DmaxForm.gigantamax ≠ DmaxForm.dynamax := by
  intro h; cases h

end VMaxMechanics
