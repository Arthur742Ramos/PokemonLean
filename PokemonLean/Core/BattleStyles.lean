/-
  PokemonLean / Core / BattleStyles.lean

  Sword & Shield era Battle Style mechanics: Single Strike, Rapid Strike,
  and Fusion Strike.  Covers style-specific energy, abilities, attacks,
  cross-style exclusivity, and style-locked card restrictions.

  Self-contained — no imports from other PokemonLean modules.
  All proofs are sorry-free.  30+ theorems.
-/

namespace PokemonLean.Core.BattleStyles

-- ============================================================
-- §1  Battle Style Definition
-- ============================================================

/-- The four battle style categories in Sword & Shield. -/
inductive BattleStyle where
  | singleStrike   -- Higher damage, single target focus
  | rapidStrike    -- Spread damage, bench hits, versatility
  | fusionStrike   -- Energy flexibility, combined power
  | none           -- No battle style
deriving DecidableEq, Repr, BEq, Inhabited

/-- All battle styles as a list. -/
def BattleStyle.all : List BattleStyle :=
  [.singleStrike, .rapidStrike, .fusionStrike, .none]

/-- Whether a Pokémon has a battle style. -/
def BattleStyle.hasStyle : BattleStyle → Bool
  | .none => false
  | _     => true

-- ============================================================
-- §2  Pokémon Types (self-contained)
-- ============================================================

/-- Pokémon types for energy provision. -/
inductive PType where
  | fire | water | grass | electric | psychic
  | fighting | dark | steel | dragon | fairy | normal
deriving DecidableEq, Repr, BEq, Inhabited

/-- Energy types: typed, colorless, or style-specific special. -/
inductive EnergyType where
  | basic (t : PType)
  | colorless
  | singleStrikeEnergy  -- Provides Fighting + Dark (Single Strike only)
  | rapidStrikeEnergy   -- Provides Fighting + Water (Rapid Strike only)
  | fusionStrikeEnergy  -- Provides any type + effect prevention (Fusion Strike only)
deriving DecidableEq, Repr, BEq, Inhabited

/-- Whether an energy card is a style-specific special energy. -/
def EnergyType.isStyleEnergy : EnergyType → Bool
  | .singleStrikeEnergy => true
  | .rapidStrikeEnergy  => true
  | .fusionStrikeEnergy => true
  | _                   => false

/-- Which battle style an energy requires on its Pokémon. -/
def EnergyType.requiredStyle : EnergyType → BattleStyle
  | .singleStrikeEnergy => .singleStrike
  | .rapidStrikeEnergy  => .rapidStrike
  | .fusionStrikeEnergy => .fusionStrike
  | _                   => .none

-- ============================================================
-- §3  Style-Specific Energy Provision
-- ============================================================

/-- Types provided by Single Strike Energy: 1 Fighting + 1 Dark.
    Returns the set of types it can satisfy. -/
def singleStrikeEnergyProvides : List PType := [.fighting, .dark]

/-- Types provided by Rapid Strike Energy: 1 Fighting + 1 Water. -/
def rapidStrikeEnergyProvides : List PType := [.fighting, .water]

/-- Fusion Strike Energy provides 1 of any type.
    Additionally prevents effects of opponent's Pokémon abilities on
    the attached Pokémon. -/
def fusionStrikeEnergyWild : Bool := true

/-- Whether a style energy can be attached to a Pokémon of the given style. -/
def canAttachStyleEnergy (energy : EnergyType) (pokemonStyle : BattleStyle) : Bool :=
  match energy with
  | .singleStrikeEnergy => pokemonStyle == .singleStrike
  | .rapidStrikeEnergy  => pokemonStyle == .rapidStrike
  | .fusionStrikeEnergy => pokemonStyle == .fusionStrike
  | _                   => true  -- Basic/colorless can attach to anything

-- ============================================================
-- §4  Battle Style Pokémon Card
-- ============================================================

/-- A simplified Battle Style Pokémon card. -/
structure BSPokemon where
  name        : String
  style       : BattleStyle
  hp          : Nat
  isV         : Bool        -- Is this a V/VMAX/VSTAR?
  prizeCount  : Nat         -- Prizes given on KO
deriving Repr, Inhabited

/-- Whether this Pokémon can use a style-locked card. -/
def BSPokemon.canUseStyleCard (p : BSPokemon) (cardStyle : BattleStyle) : Bool :=
  cardStyle == .none || p.style == cardStyle

-- ============================================================
-- §5  Style-Locked Trainer Cards
-- ============================================================

/-- Style-locked trainer cards. -/
inductive StyleTrainer where
  | urnOfVitality       -- Single Strike: retrieve SS Energy from discard
  | towerOfDarkness     -- Single Strike: discard SS card, draw 2
  | towerOfWaters       -- Rapid Strike: discard RS card, draw 2
  | rapidStrikeScroll   -- Rapid Strike: additional attack for RS Pokémon
  | powerTablet         -- Fusion Strike: +30 damage for FS attacks
  | crossSwitcher       -- Fusion Strike: play 2 at once to gust
deriving DecidableEq, Repr, BEq, Inhabited

/-- The required battle style for each style trainer. -/
def StyleTrainer.requiredStyle : StyleTrainer → BattleStyle
  | .urnOfVitality     => .singleStrike
  | .towerOfDarkness   => .singleStrike
  | .towerOfWaters     => .rapidStrike
  | .rapidStrikeScroll => .rapidStrike
  | .powerTablet       => .fusionStrike
  | .crossSwitcher     => .fusionStrike

/-- Whether a Pokémon can use a given style trainer. -/
def canUseStyleTrainer (pokemon : BSPokemon) (trainer : StyleTrainer) : Bool :=
  pokemon.style == trainer.requiredStyle

-- ============================================================
-- §6  Key Abilities (Style-Specific)
-- ============================================================

/-- Houndoom's Single Strike Roar ability:
    Attach 1 Single Strike Energy from deck to a Single Strike Pokémon.
    That Pokémon takes 20 damage (2 damage counters). -/
structure HoundoomAbility where
  activated   : Bool
  targetStyle : BattleStyle
deriving Repr, Inhabited

/-- Whether Houndoom's ability can activate.
    Once per turn, target must be Single Strike. -/
def HoundoomAbility.canActivate (a : HoundoomAbility) : Bool :=
  !a.activated && a.targetStyle == .singleStrike

/-- Self-damage from Houndoom's ability: 20 HP (2 damage counters). -/
def houndoomSelfDamage : Nat := 20

/-- Octillery's Rapid Strike Search ability:
    Once per turn, draw until you have 5 cards in hand.
    Only works for Rapid Strike Pokémon's owner. -/
structure OctilleryAbility where
  activated    : Bool
  octilleryStyle : BattleStyle
  handSize     : Nat
deriving Repr, Inhabited

/-- Target hand size for Octillery. -/
def octilleryTargetHand : Nat := 5

/-- Cards drawn by Octillery. -/
def OctilleryAbility.cardsToDraw (a : OctilleryAbility) : Nat :=
  if a.handSize < octilleryTargetHand then octilleryTargetHand - a.handSize else 0

/-- Whether Octillery's ability can activate. -/
def OctilleryAbility.canActivate (a : OctilleryAbility) : Bool :=
  !a.activated && a.octilleryStyle == .rapidStrike

/-- Genesect V's Fusion Strike System ability:
    Once per turn, draw until hand equals number of Fusion Strike Pokémon tools attached. -/
structure GenesectAbility where
  activated   : Bool
  genesectStyle : BattleStyle
  handSize    : Nat
  toolCount   : Nat  -- Number of Fusion Strike tools on Fusion Strike Pokémon
deriving Repr, Inhabited

/-- Cards drawn by Genesect V. -/
def GenesectAbility.cardsToDraw (a : GenesectAbility) : Nat :=
  if a.handSize < a.toolCount then a.toolCount - a.handSize else 0

/-- Whether Genesect V's ability can activate. -/
def GenesectAbility.canActivate (a : GenesectAbility) : Bool :=
  !a.activated && a.genesectStyle == .fusionStrike

-- ============================================================
-- §7  Key Attacks (Style-Specific)
-- ============================================================

/-- Single Strike Urshifu VMAX: G-Max One Blow.
    270 damage, single target, must discard all energy. -/
structure GMaxOneBlow where
  baseDamage    : Nat := 270
  discardAll    : Bool := true
  singleTarget  : Bool := true
deriving Repr, Inhabited

/-- Rapid Strike Urshifu VMAX: G-Max Rapid Flow.
    120 damage to each of 2 benched Pokémon.
    Bypasses bench protection effects. -/
structure GMaxRapidFlow where
  damagePerTarget : Nat := 120
  targetCount     : Nat := 2
  bypassBenchProt : Bool := true
deriving Repr, Inhabited

/-- Total spread damage from G-Max Rapid Flow. -/
def GMaxRapidFlow.totalDamage (a : GMaxRapidFlow) : Nat :=
  a.damagePerTarget * a.targetCount

/-- Mew VMAX: Cross Fusion Strike.
    Copy any attack of a benched Fusion Strike Pokémon. -/
structure CrossFusionStrike where
  canCopy        : Bool     -- Is there a FS Pokémon on bench?
  copiedDamage   : Nat      -- Damage of the copied attack
  copiedStyle    : BattleStyle  -- Must be fusionStrike
deriving Repr, Inhabited

/-- Whether Cross Fusion Strike can copy a given attack. -/
def CrossFusionStrike.isValid (a : CrossFusionStrike) : Bool :=
  a.canCopy && a.copiedStyle == .fusionStrike

-- ============================================================
-- §8  Fusion Strike Energy Effect Prevention
-- ============================================================

/-- Fusion Strike Energy prevents effects of abilities of opponent's
    Pokémon on the attached Pokémon.
    Model: track whether this Pokémon has FS Energy attached. -/
structure EffectPrevention where
  hasFusionStrikeEnergy : Bool
  pokemonStyle          : BattleStyle
deriving Repr, Inhabited

/-- Whether ability effects are prevented. -/
def EffectPrevention.preventsAbilityEffects (ep : EffectPrevention) : Bool :=
  ep.hasFusionStrikeEnergy && ep.pokemonStyle == .fusionStrike

-- ============================================================
-- §9  Damage Calculation for Style Attacks
-- ============================================================

/-- Power Tablet bonus: +30 damage per tablet for Fusion Strike attacks.
    Up to 4 can be played per turn. -/
def powerTabletBonus (tabletsPlayed : Nat) : Nat :=
  tabletsPlayed * 30

/-- Max Power Tablets playable per turn. -/
def maxPowerTablets : Nat := 4

/-- Calculate total Fusion Strike attack damage with Power Tablets. -/
def fusionStrikeDamage (baseDamage : Nat) (tabletsPlayed : Nat) : Nat :=
  baseDamage + powerTabletBonus (min tabletsPlayed maxPowerTablets)

/-- Single Strike damage: raw power, single target.
    Single Strike Scroll of Scorn: 10 × damage counters on all your Pokémon. -/
def scrollOfScornDamage (totalDamageCounters : Nat) : Nat :=
  totalDamageCounters * 10

/-- Rapid Strike spread damage distribution.
    Given total targets, distribute damagePerTarget to each. -/
def rapidStrikeSpreadTotal (damagePerTarget : Nat) (targets : Nat) : Nat :=
  damagePerTarget * targets

-- ============================================================
-- §10  Example Cards
-- ============================================================

/-- Single Strike Urshifu VMAX. -/
def ssUrshifuVMAX : BSPokemon where
  name := "Single Strike Urshifu VMAX"
  style := .singleStrike
  hp := 330
  isV := true
  prizeCount := 3

/-- Rapid Strike Urshifu VMAX. -/
def rsUrshifuVMAX : BSPokemon where
  name := "Rapid Strike Urshifu VMAX"
  style := .rapidStrike
  hp := 330
  isV := true
  prizeCount := 3

/-- Mew VMAX (Fusion Strike). -/
def mewVMAX : BSPokemon where
  name := "Mew VMAX"
  style := .fusionStrike
  hp := 310
  isV := true
  prizeCount := 3

/-- Genesect V (Fusion Strike). -/
def genesectV : BSPokemon where
  name := "Genesect V"
  style := .fusionStrike
  hp := 190
  isV := true
  prizeCount := 2

/-- Houndoom (Single Strike). -/
def houndoom : BSPokemon where
  name := "Houndoom"
  style := .singleStrike
  hp := 130
  isV := false
  prizeCount := 1

/-- Octillery (Rapid Strike). -/
def octillery : BSPokemon where
  name := "Octillery"
  style := .rapidStrike
  hp := 120
  isV := false
  prizeCount := 1

/-- Regular Pokémon (no style). -/
def regularPokemon : BSPokemon where
  name := "Bidoof"
  style := .none
  hp := 60
  isV := false
  prizeCount := 1

-- ============================================================
-- §11  Theorems — Style Energy Attachment Restrictions
-- ============================================================

/-- Theorem 1: Single Strike Energy can only attach to Single Strike Pokémon. -/
theorem ss_energy_only_ss :
    canAttachStyleEnergy .singleStrikeEnergy .singleStrike = true := by rfl

/-- Theorem 2: Single Strike Energy cannot attach to Rapid Strike. -/
theorem ss_energy_not_rs :
    canAttachStyleEnergy .singleStrikeEnergy .rapidStrike = false := by rfl

/-- Theorem 3: Single Strike Energy cannot attach to Fusion Strike. -/
theorem ss_energy_not_fs :
    canAttachStyleEnergy .singleStrikeEnergy .fusionStrike = false := by rfl

/-- Theorem 4: Single Strike Energy cannot attach to no-style Pokémon. -/
theorem ss_energy_not_none :
    canAttachStyleEnergy .singleStrikeEnergy .none = false := by rfl

/-- Theorem 5: Rapid Strike Energy can only attach to Rapid Strike Pokémon. -/
theorem rs_energy_only_rs :
    canAttachStyleEnergy .rapidStrikeEnergy .rapidStrike = true := by rfl

/-- Theorem 6: Rapid Strike Energy cannot attach to Single Strike. -/
theorem rs_energy_not_ss :
    canAttachStyleEnergy .rapidStrikeEnergy .singleStrike = false := by rfl

/-- Theorem 7: Fusion Strike Energy can only attach to Fusion Strike. -/
theorem fs_energy_only_fs :
    canAttachStyleEnergy .fusionStrikeEnergy .fusionStrike = true := by rfl

/-- Theorem 8: Fusion Strike Energy cannot attach to Rapid Strike. -/
theorem fs_energy_not_rs :
    canAttachStyleEnergy .fusionStrikeEnergy .rapidStrike = false := by rfl

/-- Theorem 9: Basic energy can attach to any style Pokémon. -/
theorem basic_energy_any_style (t : PType) (s : BattleStyle) :
    canAttachStyleEnergy (.basic t) s = true := by rfl

/-- Theorem 10: Colorless energy can attach to any style Pokémon. -/
theorem colorless_energy_any_style (s : BattleStyle) :
    canAttachStyleEnergy .colorless s = true := by rfl

-- ============================================================
-- §12  Theorems — Style Exclusivity
-- ============================================================

/-- Theorem 11: Battle styles are mutually exclusive — a Single Strike
    Pokémon is not Rapid Strike. -/
theorem styles_exclusive_ss_rs :
    BattleStyle.singleStrike ≠ BattleStyle.rapidStrike := by decide

/-- Theorem 12: Single Strike is not Fusion Strike. -/
theorem styles_exclusive_ss_fs :
    BattleStyle.singleStrike ≠ BattleStyle.fusionStrike := by decide

/-- Theorem 13: Rapid Strike is not Fusion Strike. -/
theorem styles_exclusive_rs_fs :
    BattleStyle.rapidStrike ≠ BattleStyle.fusionStrike := by decide

/-- Theorem 14: All styled Pokémon have a style. -/
theorem styled_has_style (s : BattleStyle) (h : s ≠ .none) :
    s.hasStyle = true := by
  cases s <;> simp [BattleStyle.hasStyle] <;> try contradiction

/-- Theorem 15: None style has no style. -/
theorem none_no_style : BattleStyle.none.hasStyle = false := by rfl

/-- Theorem 16: There are exactly 4 battle styles (including none). -/
theorem battle_style_count : BattleStyle.all.length = 4 := by native_decide

-- ============================================================
-- §13  Theorems — Style-Locked Trainer Cards
-- ============================================================

/-- Theorem 17: Urn of Vitality requires Single Strike. -/
theorem urn_requires_ss : StyleTrainer.urnOfVitality.requiredStyle = .singleStrike := by rfl

/-- Theorem 18: Tower of Waters requires Rapid Strike. -/
theorem tower_water_requires_rs : StyleTrainer.towerOfWaters.requiredStyle = .rapidStrike := by rfl

/-- Theorem 19: Power Tablet requires Fusion Strike. -/
theorem power_tablet_requires_fs : StyleTrainer.powerTablet.requiredStyle = .fusionStrike := by rfl

/-- Theorem 20: Cross-style trainer usage is blocked.
    A Single Strike Pokémon cannot use a Rapid Strike trainer. -/
theorem cross_style_blocked :
    canUseStyleTrainer ssUrshifuVMAX .towerOfWaters = false := by native_decide

/-- Theorem 21: Same-style trainer usage is allowed.
    Single Strike Urshifu VMAX can use Urn of Vitality. -/
theorem same_style_allowed :
    canUseStyleTrainer ssUrshifuVMAX .urnOfVitality = true := by native_decide

/-- Theorem 22: A no-style Pokémon cannot use any style trainer. -/
theorem no_style_no_trainer (t : StyleTrainer) :
    canUseStyleTrainer regularPokemon t = false := by
  cases t <;> native_decide

-- ============================================================
-- §14  Theorems — Ability Mechanics
-- ============================================================

/-- Theorem 23: Houndoom's ability deals 20 self-damage. -/
theorem houndoom_self_damage_value : houndoomSelfDamage = 20 := by rfl

/-- Theorem 24: Octillery draws up to 5 cards.
    With 3 in hand, draws 2. -/
theorem octillery_draw_from_3 :
    (OctilleryAbility.cardsToDraw
      { activated := false, octilleryStyle := .rapidStrike, handSize := 3 }) = 2 := by
  native_decide

/-- Theorem 25: Octillery draws 0 if hand already has 5+. -/
theorem octillery_no_draw_full :
    (OctilleryAbility.cardsToDraw
      { activated := false, octilleryStyle := .rapidStrike, handSize := 7 }) = 0 := by
  native_decide

/-- Theorem 26: Genesect V draws based on tool count.
    With 2 in hand and 6 tools, draws 4. -/
theorem genesect_draw_example :
    (GenesectAbility.cardsToDraw
      { activated := false, genesectStyle := .fusionStrike, handSize := 2, toolCount := 6 }) = 4 := by
  native_decide

-- ============================================================
-- §15  Theorems — Attack Mechanics
-- ============================================================

/-- Theorem 27: G-Max Rapid Flow deals 120 to each of 2 targets = 240 total. -/
theorem rapid_flow_total :
    (GMaxRapidFlow.totalDamage { damagePerTarget := 120, targetCount := 2, bypassBenchProt := true }) = 240 := by
  native_decide

/-- Theorem 28: G-Max One Blow base damage is 270. -/
theorem one_blow_damage :
    (GMaxOneBlow.mk).baseDamage = 270 := by rfl

/-- Theorem 29: Power Tablet bonus stacks: 3 tablets = 90 extra damage. -/
theorem power_tablet_stacks : powerTabletBonus 3 = 90 := by native_decide

/-- Theorem 30: Fusion Strike damage with 4 tablets on 210 base = 330. -/
theorem fs_damage_max_tablets : fusionStrikeDamage 210 4 = 330 := by native_decide

/-- Theorem 31: Fusion Strike damage with 0 tablets equals base. -/
theorem fs_damage_no_tablets (d : Nat) : fusionStrikeDamage d 0 = d := by
  simp [fusionStrikeDamage, powerTabletBonus, maxPowerTablets]

-- ============================================================
-- §16  Theorems — Fusion Strike Energy Effect Prevention
-- ============================================================

/-- Theorem 32: Fusion Strike Energy on FS Pokémon prevents ability effects. -/
theorem fs_energy_prevents_effects :
    (EffectPrevention.preventsAbilityEffects
      { hasFusionStrikeEnergy := true, pokemonStyle := .fusionStrike }) = true := by rfl

/-- Theorem 33: FS Energy on non-FS Pokémon does NOT prevent effects
    (can't legally be attached, but even if modeled, it wouldn't activate). -/
theorem fs_energy_wrong_style_no_prevent :
    (EffectPrevention.preventsAbilityEffects
      { hasFusionStrikeEnergy := true, pokemonStyle := .rapidStrike }) = false := by rfl

/-- Theorem 34: No FS Energy means no effect prevention. -/
theorem no_fs_energy_no_prevent (s : BattleStyle) :
    (EffectPrevention.preventsAbilityEffects
      { hasFusionStrikeEnergy := false, pokemonStyle := s }) = false := by
  simp [EffectPrevention.preventsAbilityEffects]

-- ============================================================
-- §17  Theorems — Style Energy Type Properties
-- ============================================================

/-- Theorem 35: All style energies are recognized as style energies. -/
theorem all_style_energies_detected (e : EnergyType) (h : e.isStyleEnergy = true) :
    e.requiredStyle ≠ .none := by
  cases e <;> simp [EnergyType.isStyleEnergy, EnergyType.requiredStyle] at *

/-- Theorem 36: Non-style energies have required style = none. -/
theorem non_style_required_none_basic (t : PType) :
    (EnergyType.basic t).requiredStyle = .none := by rfl

theorem non_style_required_none_colorless :
    EnergyType.colorless.requiredStyle = .none := by rfl

/-- Theorem 37: Single Strike Energy provides Fighting and Dark. -/
theorem ss_energy_provides : singleStrikeEnergyProvides = [.fighting, .dark] := by rfl

/-- Theorem 38: Rapid Strike Energy provides Fighting and Water. -/
theorem rs_energy_provides : rapidStrikeEnergyProvides = [.fighting, .water] := by rfl

/-- Theorem 39: Fusion Strike Energy is wild (provides any type). -/
theorem fs_energy_is_wild : fusionStrikeEnergyWild = true := by rfl

/-- Theorem 40: Style energy attachment is consistent with required style.
    If the energy requires style S and the Pokémon has style S, attachment is allowed. -/
theorem style_energy_consistent (e : EnergyType) (h : e.isStyleEnergy = true) :
    canAttachStyleEnergy e e.requiredStyle = true := by
  cases e <;> simp [EnergyType.isStyleEnergy, EnergyType.requiredStyle, canAttachStyleEnergy] at *

-- ============================================================
-- §18  Theorems — Cross-Style Interaction Summary
-- ============================================================

/-- Theorem 41: Rapid Strike spread distributes exact damage.
    5 targets × 30 each = 150 total. -/
theorem rapid_strike_exact_spread :
    rapidStrikeSpreadTotal 30 5 = 150 := by native_decide

/-- Theorem 42: Scroll of Scorn with 15 damage counters = 150 damage. -/
theorem scroll_of_scorn_calc :
    scrollOfScornDamage 15 = 150 := by native_decide

/-- Theorem 43: Power Tablet bonus with more than max is capped. -/
theorem power_tablet_capped :
    fusionStrikeDamage 100 10 = fusionStrikeDamage 100 4 := by native_decide

/-- Theorem 44: Cross Fusion Strike requires FS source. -/
theorem cross_fusion_needs_fs :
    (CrossFusionStrike.isValid
      { canCopy := true, copiedDamage := 210, copiedStyle := .fusionStrike }) = true := by rfl

/-- Theorem 45: Cross Fusion Strike rejects non-FS source. -/
theorem cross_fusion_rejects_non_fs :
    (CrossFusionStrike.isValid
      { canCopy := true, copiedDamage := 210, copiedStyle := .singleStrike }) = false := by rfl

end PokemonLean.Core.BattleStyles
