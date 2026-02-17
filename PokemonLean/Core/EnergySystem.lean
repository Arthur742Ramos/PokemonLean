/-
  PokemonLean / Core / EnergySystem.lean

  Comprehensive Pokémon TCG energy system.
  Covers manual energy attachment (once per turn), energy acceleration
  cards (Max Elixir, Welder, Dark Patch, Melony), special energy cards
  (DCE, Twin Energy, Counter Energy, Aurora Energy), energy removal
  (Crushing Hammer, Enhanced Hammer), attack cost validation, and
  colorless energy as a wildcard.

  Self-contained — no imports from other PokemonLean modules.
  All proofs are sorry-free.  30+ theorems.
-/

namespace PokemonLean.Core.EnergySystemMod

-- ============================================================
-- §1  Energy Types (self-contained)
-- ============================================================

/-- Pokémon types relevant to energy. -/
inductive PType where
  | fire | water | grass | electric | psychic
  | fighting | dark | steel | dragon | fairy | normal
deriving DecidableEq, Repr, BEq, Inhabited

/-- Energy types: typed energy or colorless. -/
inductive EnergyType where
  | typed (t : PType)
  | colorless
deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================
-- §2  Energy Cost
-- ============================================================

/-- Energy cost structure: typed requirements + colorless requirements. -/
structure EnergyCost where
  fireReq      : Nat := 0
  waterReq     : Nat := 0
  grassReq     : Nat := 0
  electricReq  : Nat := 0
  psychicReq   : Nat := 0
  fightingReq  : Nat := 0
  darkReq      : Nat := 0
  steelReq     : Nat := 0
  dragonReq    : Nat := 0
  fairyReq     : Nat := 0
  normalReq    : Nat := 0
  colorlessReq : Nat := 0
deriving DecidableEq, Repr, Inhabited

/-- Get the requirement for a specific type. -/
def EnergyCost.getReq (ec : EnergyCost) : PType → Nat
  | .fire      => ec.fireReq
  | .water     => ec.waterReq
  | .grass     => ec.grassReq
  | .electric  => ec.electricReq
  | .psychic   => ec.psychicReq
  | .fighting  => ec.fightingReq
  | .dark      => ec.darkReq
  | .steel     => ec.steelReq
  | .dragon    => ec.dragonReq
  | .fairy     => ec.fairyReq
  | .normal    => ec.normalReq

/-- Total typed energy required. -/
def EnergyCost.totalTyped (ec : EnergyCost) : Nat :=
  ec.fireReq + ec.waterReq + ec.grassReq + ec.electricReq +
  ec.psychicReq + ec.fightingReq + ec.darkReq + ec.steelReq +
  ec.dragonReq + ec.fairyReq + ec.normalReq

/-- Total energy required. -/
def EnergyCost.totalCost (ec : EnergyCost) : Nat :=
  ec.totalTyped + ec.colorlessReq

/-- Zero energy cost. -/
def EnergyCost.zero : EnergyCost := {}

-- ============================================================
-- §3  Attached Energy Pool
-- ============================================================

/-- Energy pool tracking what's attached to a Pokémon. -/
structure EnergyPool where
  fire      : Nat := 0
  water     : Nat := 0
  grass     : Nat := 0
  electric  : Nat := 0
  psychic   : Nat := 0
  fighting  : Nat := 0
  dark      : Nat := 0
  steel     : Nat := 0
  dragon    : Nat := 0
  fairy     : Nat := 0
  normal    : Nat := 0
  colorless : Nat := 0
  dce       : Nat := 0   -- Each DCE provides 2 colorless
  twinE     : Nat := 0   -- Each Twin Energy provides 2 colorless (non-V only)
  counterE  : Nat := 0   -- Each Counter Energy provides 1 of any type
  auroraE   : Nat := 0   -- Each Aurora Energy provides 1 of any type
deriving DecidableEq, Repr, Inhabited

/-- Empty energy pool. -/
def EnergyPool.empty : EnergyPool := {}

/-- Count of a specific typed energy. -/
def EnergyPool.getTyped (ep : EnergyPool) : PType → Nat
  | .fire      => ep.fire
  | .water     => ep.water
  | .grass     => ep.grass
  | .electric  => ep.electric
  | .psychic   => ep.psychic
  | .fighting  => ep.fighting
  | .dark      => ep.dark
  | .steel     => ep.steel
  | .dragon    => ep.dragon
  | .fairy     => ep.fairy
  | .normal    => ep.normal

/-- Total basic typed energy attached. -/
def EnergyPool.totalBasicTyped (ep : EnergyPool) : Nat :=
  ep.fire + ep.water + ep.grass + ep.electric + ep.psychic +
  ep.fighting + ep.dark + ep.steel + ep.dragon + ep.fairy + ep.normal

/-- Total special energy cards attached. -/
def EnergyPool.totalSpecial (ep : EnergyPool) : Nat :=
  ep.dce + ep.twinE + ep.counterE + ep.auroraE

/-- Total energy VALUE provided (counting DCE as 2, etc.). -/
def EnergyPool.totalValue (ep : EnergyPool) : Nat :=
  ep.totalBasicTyped + ep.colorless + ep.dce * 2 + ep.twinE * 2 +
  ep.counterE + ep.auroraE

/-- Total energy CARDS attached. -/
def EnergyPool.totalCards (ep : EnergyPool) : Nat :=
  ep.totalBasicTyped + ep.colorless + ep.dce + ep.twinE +
  ep.counterE + ep.auroraE

-- ============================================================
-- §4  Cost Satisfaction
-- ============================================================

/-- Check if a pool satisfies a cost, using a simplified greedy approach.
    Typed energy satisfies typed requirements first, then surplus + colorless
    + special energy value satisfies colorless requirements.
    Wild energy (Counter, Aurora) can satisfy any typed requirement. -/
def satisfiesCost (pool : EnergyPool) (cost : EnergyCost) (isVPokemon : Bool) : Bool :=
  let wildCount := pool.counterE + pool.auroraE
  -- For each type, check typed energy + wild ≥ requirement
  -- Simplified: sum up surplus and check colorless
  let allTypes := [PType.fire, .water, .grass, .electric, .psychic,
                   .fighting, .dark, .steel, .dragon, .fairy, .normal]
  -- Total typed requirement
  let totalTypedReq := cost.totalTyped
  -- Total typed energy available (including wild as any-type)
  let totalTypedAvail := pool.totalBasicTyped + wildCount
  -- Effective colorless from DCE and Twin Energy
  let twinValue := if isVPokemon then 0 else pool.twinE * 2
  let dceValue := pool.dce * 2
  let colorlessAvail := pool.colorless + dceValue + twinValue
  -- Check each typed requirement can be met
  let typedOk := allTypes.all fun t => pool.getTyped t + wildCount ≥ cost.getReq t
  -- If typed requirements met, surplus goes to colorless
  let surplus := if totalTypedAvail ≥ totalTypedReq
                 then totalTypedAvail - totalTypedReq else 0
  let colorlessOk := surplus + colorlessAvail ≥ cost.colorlessReq
  typedOk && colorlessOk

-- ============================================================
-- §5  Manual Energy Attachment
-- ============================================================

/-- Turn state for energy attachment. -/
structure EnergyAttachState where
  manualAttachUsed : Bool    -- Has the once-per-turn manual attach been used?
deriving DecidableEq, Repr, Inhabited

/-- Initial energy attach state. -/
def EnergyAttachState.initial : EnergyAttachState :=
  { manualAttachUsed := false }

/-- Can manually attach energy this turn? -/
def EnergyAttachState.canManualAttach (s : EnergyAttachState) : Bool :=
  !s.manualAttachUsed

/-- Perform a manual energy attachment. -/
def EnergyAttachState.doManualAttach (_s : EnergyAttachState) : EnergyAttachState :=
  { manualAttachUsed := true }

-- ============================================================
-- §6  Energy Acceleration Cards
-- ============================================================

/-- Energy acceleration method: how the energy gets attached. -/
inductive AccelMethod where
  | maxElixir     -- From top 6 of deck → bench basic Pokémon (basic energy)
  | welder        -- Attach up to 2 fire energy from hand, then draw 3
  | darkPatch     -- Dark energy from discard → bench Dark Pokémon
  | melony        -- Water energy from discard → any V Pokémon, then draw 3
deriving DecidableEq, Repr, BEq

/-- Number of energy attached by each acceleration method. -/
def AccelMethod.energyCount : AccelMethod → Nat
  | .maxElixir => 1
  | .welder    => 2
  | .darkPatch => 1
  | .melony    => 1

/-- Whether the acceleration method is from discard pile. -/
def AccelMethod.fromDiscard : AccelMethod → Bool
  | .maxElixir => false
  | .welder    => false
  | .darkPatch => true
  | .melony    => true

/-- Whether the acceleration method draws cards after attaching. -/
def AccelMethod.drawsCards : AccelMethod → Bool
  | .maxElixir => false
  | .welder    => true
  | .darkPatch => false
  | .melony    => true

/-- How many cards drawn after the acceleration. -/
def AccelMethod.drawCount : AccelMethod → Nat
  | .welder => 3
  | .melony => 3
  | _       => 0

-- ============================================================
-- §7  Special Energy Cards
-- ============================================================

/-- Special energy card types. -/
inductive SpecialEnergy where
  | doubleCE       -- Double Colorless Energy: provides 2 colorless
  | twinEnergy     -- Twin Energy: provides 2 colorless (non-V only)
  | counterEnergy  -- Counter Energy: provides 1 of any type if behind on prizes
  | auroraEnergy   -- Aurora Energy: discard 1 card to attach, provides any type
deriving DecidableEq, Repr, BEq, Inhabited

/-- Colorless value provided by each special energy. -/
def SpecialEnergy.colorlessValue : SpecialEnergy → Nat
  | .doubleCE      => 2
  | .twinEnergy    => 2
  | .counterEnergy => 1
  | .auroraEnergy  => 1

/-- Whether this special energy can provide any type (wild). -/
def SpecialEnergy.isWild : SpecialEnergy → Bool
  | .doubleCE      => false  -- Only colorless
  | .twinEnergy    => false  -- Only colorless
  | .counterEnergy => true   -- Any type when behind on prizes
  | .auroraEnergy  => true   -- Any type

/-- Whether Twin Energy works on V Pokémon. -/
def twinEnergyWorksOnV : Bool := false

/-- Whether Counter Energy provides rainbow effect. -/
def counterEnergyActive (playerPrizes opponentPrizes : Nat) : Bool :=
  playerPrizes > opponentPrizes

-- ============================================================
-- §8  Energy Removal
-- ============================================================

/-- Energy removal methods. -/
inductive RemovalMethod where
  | crushingHammer    -- Flip a coin: heads = remove 1 energy from opponent
  | enhancedHammer    -- Remove 1 special energy from opponent (no flip)
deriving DecidableEq, Repr, BEq

/-- Whether the removal method requires a coin flip. -/
def RemovalMethod.requiresFlip : RemovalMethod → Bool
  | .crushingHammer => true
  | .enhancedHammer => false

/-- Whether the removal targets only special energy. -/
def RemovalMethod.specialOnly : RemovalMethod → Bool
  | .crushingHammer => false
  | .enhancedHammer => true

/-- Remove one basic energy from a pool (fire specifically as example). -/
def EnergyPool.removeOneBasic (ep : EnergyPool) (t : PType) : EnergyPool :=
  match t with
  | .fire      => { ep with fire := ep.fire - 1 }
  | .water     => { ep with water := ep.water - 1 }
  | .grass     => { ep with grass := ep.grass - 1 }
  | .electric  => { ep with electric := ep.electric - 1 }
  | .psychic   => { ep with psychic := ep.psychic - 1 }
  | .fighting  => { ep with fighting := ep.fighting - 1 }
  | .dark      => { ep with dark := ep.dark - 1 }
  | .steel     => { ep with steel := ep.steel - 1 }
  | .dragon    => { ep with dragon := ep.dragon - 1 }
  | .fairy     => { ep with fairy := ep.fairy - 1 }
  | .normal    => { ep with normal := ep.normal - 1 }

/-- Remove one special energy (DCE first, then twin, then counter, then aurora). -/
def EnergyPool.removeOneSpecial (ep : EnergyPool) : EnergyPool :=
  if ep.dce > 0 then { ep with dce := ep.dce - 1 }
  else if ep.twinE > 0 then { ep with twinE := ep.twinE - 1 }
  else if ep.counterE > 0 then { ep with counterE := ep.counterE - 1 }
  else if ep.auroraE > 0 then { ep with auroraE := ep.auroraE - 1 }
  else ep

-- ============================================================
-- §9  Attach Operations
-- ============================================================

/-- Attach one basic typed energy. -/
def EnergyPool.attachBasic (ep : EnergyPool) (t : PType) : EnergyPool :=
  match t with
  | .fire      => { ep with fire := ep.fire + 1 }
  | .water     => { ep with water := ep.water + 1 }
  | .grass     => { ep with grass := ep.grass + 1 }
  | .electric  => { ep with electric := ep.electric + 1 }
  | .psychic   => { ep with psychic := ep.psychic + 1 }
  | .fighting  => { ep with fighting := ep.fighting + 1 }
  | .dark      => { ep with dark := ep.dark + 1 }
  | .steel     => { ep with steel := ep.steel + 1 }
  | .dragon    => { ep with dragon := ep.dragon + 1 }
  | .fairy     => { ep with fairy := ep.fairy + 1 }
  | .normal    => { ep with normal := ep.normal + 1 }

/-- Attach a DCE. -/
def EnergyPool.attachDCE (ep : EnergyPool) : EnergyPool :=
  { ep with dce := ep.dce + 1 }

/-- Attach Twin Energy. -/
def EnergyPool.attachTwin (ep : EnergyPool) : EnergyPool :=
  { ep with twinE := ep.twinE + 1 }

-- ============================================================
-- §10  Theorems — Manual Attach Limit
-- ============================================================

/-- Initially, manual attach is available. -/
theorem initial_can_attach :
    EnergyAttachState.initial.canManualAttach = true := by rfl

/-- After manual attach, cannot attach again. -/
theorem manual_attach_once (s : EnergyAttachState) :
    (s.doManualAttach).canManualAttach = false := by
  simp [EnergyAttachState.doManualAttach, EnergyAttachState.canManualAttach]

/-- Manual attach is idempotent. -/
theorem manual_attach_idempotent (s : EnergyAttachState) :
    (s.doManualAttach).doManualAttach = s.doManualAttach := by
  simp [EnergyAttachState.doManualAttach]

-- ============================================================
-- §11  Theorems — Energy Acceleration
-- ============================================================

/-- Welder attaches 2 energy. -/
theorem welder_attaches_two : AccelMethod.welder.energyCount = 2 := by rfl

/-- Max Elixir attaches 1 energy. -/
theorem max_elixir_attaches_one : AccelMethod.maxElixir.energyCount = 1 := by rfl

/-- Dark Patch comes from the discard pile. -/
theorem dark_patch_from_discard : AccelMethod.darkPatch.fromDiscard = true := by rfl

/-- Melony draws 3 cards after attaching. -/
theorem melony_draws_three : AccelMethod.melony.drawCount = 3 := by rfl

/-- Welder draws 3 cards after attaching. -/
theorem welder_draws_three : AccelMethod.welder.drawCount = 3 := by rfl

/-- Max Elixir does not draw cards. -/
theorem max_elixir_no_draw : AccelMethod.maxElixir.drawCount = 0 := by rfl

-- ============================================================
-- §12  Theorems — Special Energy
-- ============================================================

/-- DCE provides exactly 2 colorless energy value. -/
theorem dce_provides_two : SpecialEnergy.doubleCE.colorlessValue = 2 := by rfl

/-- Twin Energy provides exactly 2 colorless energy value. -/
theorem twin_provides_two : SpecialEnergy.twinEnergy.colorlessValue = 2 := by rfl

/-- Counter Energy is wild (any type). -/
theorem counter_is_wild : SpecialEnergy.counterEnergy.isWild = true := by rfl

/-- Aurora Energy is wild (any type). -/
theorem aurora_is_wild : SpecialEnergy.auroraEnergy.isWild = true := by rfl

/-- DCE is not wild (colorless only). -/
theorem dce_not_wild : SpecialEnergy.doubleCE.isWild = false := by rfl

/-- Twin Energy does NOT work on V Pokémon. -/
theorem twin_not_on_v : twinEnergyWorksOnV = false := by rfl

/-- Counter Energy active when behind on prizes. -/
theorem counter_active_behind : counterEnergyActive 4 2 = true := by rfl

/-- Counter Energy not active when ahead on prizes. -/
theorem counter_not_active_ahead : counterEnergyActive 2 4 = false := by rfl

/-- Counter Energy not active when tied. -/
theorem counter_not_active_tied : counterEnergyActive 3 3 = false := by rfl

-- ============================================================
-- §13  Theorems — Cost Satisfaction
-- ============================================================

/-- Zero cost is always satisfied. -/
theorem zero_cost_satisfied (ep : EnergyPool) (v : Bool) :
    satisfiesCost ep EnergyCost.zero v = true := by
  simp [satisfiesCost, EnergyCost.zero, EnergyCost.totalTyped,
        EnergyPool.totalBasicTyped, EnergyPool.getTyped, EnergyCost.getReq,
        List.all]

/-- Empty pool cannot satisfy a fire energy requirement. -/
theorem empty_pool_no_fire :
    satisfiesCost EnergyPool.empty { fireReq := 1 } false = false := by
  native_decide

/-- A pool with 1 fire satisfies 1 fire requirement. -/
theorem one_fire_satisfies :
    satisfiesCost { fire := 1 } { fireReq := 1 } false = true := by
  native_decide

/-- A pool with 2 fire and 1 colorless satisfies fire+fire+colorless. -/
theorem ffc_cost_satisfied :
    satisfiesCost { fire := 2, colorless := 1 } { fireReq := 2, colorlessReq := 1 } false = true := by
  native_decide

/-- DCE satisfies a 2-colorless requirement. -/
theorem dce_satisfies_two_colorless :
    satisfiesCost { dce := 1 } { colorlessReq := 2 } false = true := by
  native_decide

-- ============================================================
-- §14  Theorems — Energy Removal
-- ============================================================

/-- Crushing Hammer requires a flip. -/
theorem crushing_hammer_flip : RemovalMethod.crushingHammer.requiresFlip = true := by rfl

/-- Enhanced Hammer does not require a flip. -/
theorem enhanced_hammer_no_flip : RemovalMethod.enhancedHammer.requiresFlip = false := by rfl

/-- Enhanced Hammer only targets special energy. -/
theorem enhanced_hammer_special : RemovalMethod.enhancedHammer.specialOnly = true := by rfl

/-- Crushing Hammer can target any energy. -/
theorem crushing_hammer_any : RemovalMethod.crushingHammer.specialOnly = false := by rfl

-- ============================================================
-- §15  Theorems — Pool Operations
-- ============================================================

/-- Empty pool has total value 0. -/
theorem empty_pool_zero_value : EnergyPool.empty.totalValue = 0 := by rfl

/-- Empty pool has total cards 0. -/
theorem empty_pool_zero_cards : EnergyPool.empty.totalCards = 0 := by rfl

/-- Attaching DCE increases total value by 2. -/
theorem attach_dce_adds_two (ep : EnergyPool) :
    ep.attachDCE.totalValue = ep.totalValue + 2 := by
  simp [EnergyPool.attachDCE, EnergyPool.totalValue,
        EnergyPool.totalBasicTyped]
  omega

/-- Attaching basic fire increases total value by 1. -/
theorem attach_fire_adds_one (ep : EnergyPool) :
    (ep.attachBasic .fire).totalValue = ep.totalValue + 1 := by
  simp [EnergyPool.attachBasic, EnergyPool.totalValue,
        EnergyPool.totalBasicTyped]
  omega

/-- Removing special energy decreases or maintains special count. -/
theorem remove_special_decreases (ep : EnergyPool) :
    ep.removeOneSpecial.totalSpecial ≤ ep.totalSpecial := by
  unfold EnergyPool.removeOneSpecial EnergyPool.totalSpecial
  repeat split <;> simp_all

end PokemonLean.Core.EnergySystemMod
