/-
  PokemonLean / Core / EnergySystemDeep.lean

  Deep energy system formalization.
  Covers 11 energy types, special energy cards, energy attachment rules,
  energy acceleration methods, retreat cost mechanics, colorless wildcards,
  and Dragon type's lack of basic energy.

  Self-contained — no imports from other PokemonLean modules.
  All proofs are sorry-free.  35+ theorems.
-/

namespace PokemonLean.Core.EnergySystemDeep

-- ============================================================
-- §1  The 11 Energy Types
-- ============================================================

/-- The 11 Pokémon TCG energy types.
    Note: Colorless is an energy type but has no corresponding basic
    energy card — any basic energy satisfies a colorless requirement. -/
inductive EType where
  | grass
  | fire
  | water
  | lightning
  | psychic
  | fighting
  | dark
  | metal
  | fairy
  | dragon
  | colorless
deriving DecidableEq, Repr, BEq, Inhabited

/-- All 11 energy types as a list. -/
def EType.all : List EType :=
  [.grass, .fire, .water, .lightning, .psychic, .fighting,
   .dark, .metal, .fairy, .dragon, .colorless]

/-- Number of energy types. -/
def EType.count : Nat := 11

-- ============================================================
-- §2  Basic Energy Cards
-- ============================================================

/-- Basic energy provides exactly 1 energy of its type.
    There are 9 basic energy types (no Dragon basic, no Colorless basic). -/
inductive BasicEnergyType where
  | grass | fire | water | lightning | psychic
  | fighting | dark | metal | fairy
deriving DecidableEq, Repr, BEq, Inhabited

/-- Convert a basic energy to its EType. -/
def BasicEnergyType.toEType : BasicEnergyType → EType
  | .grass     => .grass
  | .fire      => .fire
  | .water     => .water
  | .lightning => .lightning
  | .psychic   => .psychic
  | .fighting  => .fighting
  | .dark      => .dark
  | .metal     => .metal
  | .fairy     => .fairy

/-- All basic energy types. -/
def BasicEnergyType.all : List BasicEnergyType :=
  [.grass, .fire, .water, .lightning, .psychic,
   .fighting, .dark, .metal, .fairy]

/-- Number of basic energy types (9 — no Dragon, no Colorless). -/
def BasicEnergyType.count : Nat := 9

/-- A basic energy card provides exactly 1 energy. -/
def basicEnergyProvides (_bet : BasicEnergyType) : Nat := 1

-- ============================================================
-- §3  Special Energy Cards
-- ============================================================

/-- Special energy cards can provide multiple types or effects. -/
structure SpecialEnergy where
  name : String
  provides : List EType   -- types this energy can provide
  effectDesc : String      -- additional effect description
  maxCopies : Nat := 4     -- max copies in deck (ACE SPEC = 1)
deriving Repr, Inhabited

/-- Number of types a special energy provides. -/
def SpecialEnergy.typeCount (se : SpecialEnergy) : Nat :=
  se.provides.length

-- Example special energies

/-- Double Colorless Energy: provides 2 colorless. -/
def doubleColorless : SpecialEnergy where
  name := "Double Colorless Energy"
  provides := [.colorless, .colorless]
  effectDesc := "Provides 2 Colorless Energy."

/-- Twin Energy: provides 2 colorless (non-V/ex only). -/
def twinEnergy : SpecialEnergy where
  name := "Twin Energy"
  provides := [.colorless, .colorless]
  effectDesc := "Provides 2 Colorless Energy. Can only be attached to non-Rule Box Pokémon."

/-- Double Turbo Energy: provides 2 colorless, −20 damage. -/
def doubleTurbo : SpecialEnergy where
  name := "Double Turbo Energy"
  provides := [.colorless, .colorless]
  effectDesc := "Provides 2 Colorless Energy. Attacks by the Pokémon this is attached to do 20 less damage."

/-- Aurora Energy: provides all types (discard a card to attach). -/
def auroraEnergy : SpecialEnergy where
  name := "Aurora Energy"
  provides := [.grass, .fire, .water, .lightning, .psychic, .fighting, .dark, .metal, .fairy, .dragon]
  effectDesc := "When you attach this card from your hand, discard a card. Provides every type of Energy but only 1 at a time."

/-- Jet Energy: provides 1 colorless + switch effect. -/
def jetEnergy : SpecialEnergy where
  name := "Jet Energy"
  provides := [.colorless]
  effectDesc := "Provides 1 Colorless Energy. When attached from hand to a Benched Pokémon, switch that Pokémon to Active."

/-- Reversal Energy: provides 3 colorless if behind on prizes. -/
def reversalEnergy : SpecialEnergy where
  name := "Reversal Energy"
  provides := [.colorless, .colorless, .colorless]
  effectDesc := "Provides 3 Colorless Energy if you have more Prize cards remaining. Only for evolved, non-Rule Box Pokémon."

-- ============================================================
-- §4  Energy Attachment Rule
-- ============================================================

/-- Track energy attachments in a turn. -/
structure TurnAttachState where
  normalAttachUsed : Bool   -- has the 1-per-turn manual attach been used?
  bonusAttaches    : Nat    -- extra attaches from abilities/trainers
deriving Repr, Inhabited

/-- Initial turn state: no attachments made. -/
def freshTurn : TurnAttachState where
  normalAttachUsed := false
  bonusAttaches := 0

/-- Can the player manually attach an energy this turn? -/
def canManualAttach (state : TurnAttachState) : Bool :=
  !state.normalAttachUsed

/-- Perform a manual attach. -/
def doManualAttach (state : TurnAttachState) : TurnAttachState :=
  { state with normalAttachUsed := true }

/-- Grant a bonus attach (from ability like Psychic Embrace, or trainer like Welder). -/
def grantBonusAttach (state : TurnAttachState) (n : Nat) : TurnAttachState :=
  { state with bonusAttaches := state.bonusAttaches + n }

/-- Total attaches available this turn. -/
def totalAttachesAvailable (state : TurnAttachState) : Nat :=
  (if state.normalAttachUsed then 0 else 1) + state.bonusAttaches

-- ============================================================
-- §5  Energy Acceleration Methods
-- ============================================================

/-- Source of energy acceleration. -/
inductive AccelSource where
  | fromDiscard   -- e.g., Dark Patch, Koraidon ex
  | fromDeck      -- e.g., Max Elixir
  | fromHand      -- e.g., Welder (attach extra from hand)
deriving DecidableEq, Repr, Inhabited

/-- An energy acceleration effect. -/
structure EnergyAccel where
  name       : String
  source     : AccelSource
  energyType : Option EType  -- None = any type
  maxCount   : Nat           -- max energies moved
deriving Repr, Inhabited

/-- Dark Patch: 1 Dark from discard to benched Dark Pokémon. -/
def darkPatch : EnergyAccel where
  name := "Dark Patch"
  source := .fromDiscard
  energyType := some .dark
  maxCount := 1

/-- Max Elixir: 1 Basic Energy from top 6 of deck to benched Basic. -/
def maxElixir : EnergyAccel where
  name := "Max Elixir"
  source := .fromDeck
  energyType := none
  maxCount := 1

/-- Welder: attach 2 Fire from hand, draw 3. -/
def welderAccel : EnergyAccel where
  name := "Welder"
  source := .fromHand
  energyType := some .fire
  maxCount := 2

-- ============================================================
-- §6  Attack Cost Validation
-- ============================================================

/-- Energy requirement for an attack. -/
structure AttackCost where
  typedReqs : List (EType × Nat)  -- (type, count) pairs
  colorlessReq : Nat
deriving Repr, Inhabited

/-- Attached energy pool. -/
structure EnergyPool where
  energies : List EType
deriving Repr, Inhabited

/-- Count energies of a specific type in pool. -/
def EnergyPool.countType (pool : EnergyPool) (t : EType) : Nat :=
  pool.energies.filter (· == t) |>.length

/-- Total energy in pool. -/
def EnergyPool.total (pool : EnergyPool) : Nat :=
  pool.energies.length

/-- Check if typed requirements are met. -/
def typedReqsMet (pool : EnergyPool) : List (EType × Nat) → Bool
  | [] => true
  | (t, n) :: rest => pool.countType t ≥ n && typedReqsMet pool rest

/-- Total typed energy needed. -/
def totalTypedNeeded : List (EType × Nat) → Nat
  | [] => 0
  | (_, n) :: rest => n + totalTypedNeeded rest

/-- Can this pool pay for the attack cost?
    Typed reqs must be met exactly, remaining energy covers colorless. -/
def canPayCost (pool : EnergyPool) (cost : AttackCost) : Bool :=
  typedReqsMet pool cost.typedReqs &&
  pool.total ≥ totalTypedNeeded cost.typedReqs + cost.colorlessReq

-- ============================================================
-- §7  Retreat Cost Mechanics
-- ============================================================

/-- Retreat: discard energy equal to retreat cost. Energy is gone permanently
    (unless recovered by other effects). -/
def retreatDiscard (attached : Nat) (retreatCost : Nat) : Option Nat :=
  if attached ≥ retreatCost then some (attached - retreatCost) else none

/-- Float Stone: reduces retreat cost to 0. -/
def floatStoneRetreat (_attached : Nat) : Option Nat :=
  some _attached  -- no discard needed

/-- Air Balloon: reduces retreat cost by 2 (min 0). -/
def airBalloonCost (baseCost : Nat) : Nat :=
  baseCost - 2

-- ============================================================
-- §8  Dragon Type: No Basic Energy
-- ============================================================

/-- Dragon has no basic energy type. Dragon Pokémon must use multi-type
    energy or energy of other types that their attacks require. -/
def hasBasicEnergy : EType → Bool
  | .grass     => true
  | .fire      => true
  | .water     => true
  | .lightning => true
  | .psychic   => true
  | .fighting  => true
  | .dark      => true
  | .metal     => true
  | .fairy     => true
  | .dragon    => false
  | .colorless => false

-- ============================================================
-- §9  Colorless as Wildcard
-- ============================================================

/-- Any energy type can satisfy a colorless requirement. -/
def satisfiesColorless (_e : EType) : Bool := true

/-- A typed energy satisfies its own type requirement. -/
def satisfiesType (e : EType) (req : EType) : Bool :=
  e == req

-- ============================================================
-- §10  Deck Rules for Energy
-- ============================================================

/-- Max copies of a basic energy: unlimited (60-card deck limit applies). -/
def basicEnergyMaxCopies : Option Nat := none  -- unlimited

/-- Max copies of a special energy: 4 (standard rule). -/
def specialEnergyMaxCopies : Nat := 4

/-- ACE SPEC energy: only 1 copy. -/
def aceSpecMaxCopies : Nat := 1

-- ============================================================
-- §11  Theorems: Colorless accepts any type
-- ============================================================

theorem colorless_accepts_grass : satisfiesColorless .grass = true := by rfl
theorem colorless_accepts_fire : satisfiesColorless .fire = true := by rfl
theorem colorless_accepts_water : satisfiesColorless .water = true := by rfl
theorem colorless_accepts_lightning : satisfiesColorless .lightning = true := by rfl
theorem colorless_accepts_psychic : satisfiesColorless .psychic = true := by rfl
theorem colorless_accepts_fighting : satisfiesColorless .fighting = true := by rfl
theorem colorless_accepts_dark : satisfiesColorless .dark = true := by rfl
theorem colorless_accepts_metal : satisfiesColorless .metal = true := by rfl

theorem colorless_accepts_any (e : EType) : satisfiesColorless e = true := by
  simp [satisfiesColorless]

-- ============================================================
-- §12  Theorems: Basic energy provides exactly 1
-- ============================================================

theorem basic_provides_one (b : BasicEnergyType) :
    basicEnergyProvides b = 1 := by
  simp [basicEnergyProvides]

-- ============================================================
-- §13  Theorems: Special energy provides ≤ reasonable bound
-- ============================================================

theorem dce_provides_two : doubleColorless.typeCount = 2 := by
  simp [SpecialEnergy.typeCount, doubleColorless]

theorem twin_provides_two : twinEnergy.typeCount = 2 := by
  simp [SpecialEnergy.typeCount, twinEnergy]

theorem double_turbo_provides_two : doubleTurbo.typeCount = 2 := by
  simp [SpecialEnergy.typeCount, doubleTurbo]

theorem jet_provides_one : jetEnergy.typeCount = 1 := by
  simp [SpecialEnergy.typeCount, jetEnergy]

theorem reversal_provides_three : reversalEnergy.typeCount = 3 := by
  simp [SpecialEnergy.typeCount, reversalEnergy]

-- ============================================================
-- §14  Theorems: 1 attachment per turn default
-- ============================================================

theorem fresh_turn_can_attach : canManualAttach freshTurn = true := by
  simp [canManualAttach, freshTurn]

theorem after_attach_cannot : canManualAttach (doManualAttach freshTurn) = false := by
  simp [canManualAttach, doManualAttach, freshTurn]

theorem manual_attach_once :
    canManualAttach (doManualAttach (doManualAttach freshTurn)) = false := by
  simp [canManualAttach, doManualAttach, freshTurn]

theorem fresh_turn_total : totalAttachesAvailable freshTurn = 1 := by
  simp [totalAttachesAvailable, freshTurn]

theorem bonus_adds_to_total :
    totalAttachesAvailable (grantBonusAttach freshTurn 2) = 3 := by
  simp [totalAttachesAvailable, grantBonusAttach, freshTurn]

-- ============================================================
-- §15  Theorems: Retreat removes energy permanently
-- ============================================================

theorem retreat_removes_energy :
    retreatDiscard 5 2 = some 3 := by
  simp [retreatDiscard]

theorem retreat_fails_insufficient :
    retreatDiscard 1 3 = none := by
  simp [retreatDiscard]

theorem retreat_exact :
    retreatDiscard 2 2 = some 0 := by
  simp [retreatDiscard]

theorem retreat_free :
    retreatDiscard 5 0 = some 5 := by
  simp [retreatDiscard]

theorem float_stone_no_discard (n : Nat) :
    floatStoneRetreat n = some n := by
  simp [floatStoneRetreat]

theorem air_balloon_reduces :
    airBalloonCost 3 = 1 := by
  simp [airBalloonCost]

theorem air_balloon_zero_floor :
    airBalloonCost 1 = 0 := by
  simp [airBalloonCost]

-- ============================================================
-- §16  Theorems: Dragon has no basic energy
-- ============================================================

theorem dragon_no_basic : hasBasicEnergy .dragon = false := by rfl
theorem colorless_no_basic : hasBasicEnergy .colorless = false := by rfl
theorem fire_has_basic : hasBasicEnergy .fire = true := by rfl
theorem water_has_basic : hasBasicEnergy .water = true := by rfl
theorem grass_has_basic : hasBasicEnergy .grass = true := by rfl
theorem psychic_has_basic : hasBasicEnergy .psychic = true := by rfl
theorem fighting_has_basic : hasBasicEnergy .fighting = true := by rfl

-- ============================================================
-- §17  Theorems: Energy count ≥ attack cost
-- ============================================================

theorem can_pay_free_attack :
    canPayCost { energies := [] } { typedReqs := [], colorlessReq := 0 } = true := by
  simp [canPayCost, typedReqsMet, totalTypedNeeded, EnergyPool.total]

theorem cannot_pay_no_energy :
    canPayCost { energies := [] } { typedReqs := [], colorlessReq := 1 } = false := by
  simp [canPayCost, typedReqsMet, totalTypedNeeded, EnergyPool.total]

theorem can_pay_with_enough :
    canPayCost { energies := [.fire, .fire, .colorless] }
               { typedReqs := [(.fire, 2)], colorlessReq := 1 } = true := by
  native_decide

-- ============================================================
-- §18  Theorems: Deck rules
-- ============================================================

theorem basic_energy_unlimited : basicEnergyMaxCopies = none := by rfl
theorem special_energy_four : specialEnergyMaxCopies = 4 := by rfl
theorem ace_spec_one : aceSpecMaxCopies = 1 := by rfl

-- ============================================================
-- §19  Theorems: Type satisfaction
-- ============================================================

theorem fire_satisfies_fire : satisfiesType .fire .fire = true := by
  native_decide

theorem water_not_fire : satisfiesType .water .fire = false := by
  native_decide

-- ============================================================
-- §20  Theorems: Energy type count
-- ============================================================

theorem eleven_types : EType.all.length = 11 := by
  simp [EType.all]

theorem nine_basic_types : BasicEnergyType.all.length = 9 := by
  simp [BasicEnergyType.all]

theorem etype_count_correct : EType.count = 11 := by rfl
theorem basic_count_correct : BasicEnergyType.count = 9 := by rfl

-- ============================================================
-- §21  Theorems: Acceleration sources
-- ============================================================

theorem dark_patch_from_discard : darkPatch.source = .fromDiscard := by rfl
theorem max_elixir_from_deck : maxElixir.source = .fromDeck := by rfl
theorem welder_from_hand : welderAccel.source = .fromHand := by rfl

theorem dark_patch_max_one : darkPatch.maxCount = 1 := by rfl
theorem welder_max_two : welderAccel.maxCount = 2 := by rfl

end PokemonLean.Core.EnergySystemDeep
