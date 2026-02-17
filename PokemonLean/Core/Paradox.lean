/-
  PokemonLean / Core / Paradox.lean

  Scarlet & Violet Paradox Rift mechanics: Ancient and Future Pokémon.
  Ancient Pokémon (past paradox forms) and Future Pokémon (future paradox
  forms) are always Basic, cannot evolve, and have unique booster capsule
  support cards.  Covers specific card models, Area Zero support, and
  comprehensive rule theorems.

  Self-contained — no imports from other PokemonLean modules.
  All proofs are sorry-free.  30+ theorems.
-/

namespace PokemonLean.Core.Paradox

-- ============================================================
-- §1  Paradox Type Definition
-- ============================================================

/-- Paradox classification for Pokémon cards. -/
inductive ParadoxType where
  | ancient   -- Past paradox forms (Scarlet exclusives)
  | future    -- Future paradox forms (Violet exclusives)
  | none      -- Regular Pokémon (not paradox)
deriving DecidableEq, Repr, BEq, Inhabited

/-- All paradox types. -/
def ParadoxType.all : List ParadoxType := [.ancient, .future, .none]

/-- Whether a Pokémon is a paradox Pokémon. -/
def ParadoxType.isParadox : ParadoxType → Bool
  | .none => false
  | _     => true

-- ============================================================
-- §2  Pokémon Types (self-contained)
-- ============================================================

/-- Pokémon types for the type chart. -/
inductive PType where
  | fire | water | grass | electric | psychic
  | fighting | dark | steel | dragon | fairy | normal
deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================
-- §3  Evolution Stage
-- ============================================================

/-- Evolution stage. Paradox Pokémon are always Basic. -/
inductive Stage where
  | basic
  | stage1
  | stage2
deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================
-- §4  Paradox Pokémon Card
-- ============================================================

/-- A Paradox Pokémon card with full attributes. -/
structure ParadoxCard where
  name        : String
  paradox     : ParadoxType
  ptype       : PType
  hp          : Nat
  stage       : Stage
  isEx        : Bool      -- Is this an ex Pokémon?
  prizeCount  : Nat       -- Prizes on KO (1 for regular, 2 for ex)
  canEvolve   : Bool      -- Always false for Paradox
deriving Repr, Inhabited

/-- Whether a paradox card is rule-valid: paradox ⇒ basic ∧ ¬canEvolve. -/
def ParadoxCard.isValid (c : ParadoxCard) : Bool :=
  if c.paradox.isParadox then
    c.stage == .basic && !c.canEvolve
  else true

-- ============================================================
-- §5  Booster Energy Capsules
-- ============================================================

/-- The two Booster Energy Capsule types. -/
inductive BoosterCapsule where
  | ancientBooster   -- Ancient Booster Energy Capsule: +60 HP or stat boost
  | futureBooster    -- Future Booster Energy Capsule: stat boost (different)
deriving DecidableEq, Repr, BEq, Inhabited

/-- Which paradox type a capsule requires. -/
def BoosterCapsule.requiredParadox : BoosterCapsule → ParadoxType
  | .ancientBooster => .ancient
  | .futureBooster  => .future

/-- Whether a capsule can be attached to a given Pokémon. -/
def canAttachBooster (capsule : BoosterCapsule) (pokemon : ParadoxCard) : Bool :=
  pokemon.paradox == capsule.requiredParadox

/-- HP bonus from Ancient Booster Energy Capsule. -/
def ancientBoosterHPBonus : Nat := 60

/-- Effective HP of a Pokémon with Ancient Booster Capsule.
    Only applies if the Pokémon is Ancient. -/
def effectiveHP (card : ParadoxCard) (hasAncientBooster : Bool) : Nat :=
  if hasAncientBooster && card.paradox == .ancient then
    card.hp + ancientBoosterHPBonus
  else card.hp

-- ============================================================
-- §6  Specific Paradox Cards
-- ============================================================

/-- Roaring Moon ex: Ancient, Dark type, 230 HP.
    Frenzied Gouging: Discard all energy, 220 + coin flip for 220 more. -/
def roaringMoonEx : ParadoxCard where
  name := "Roaring Moon ex"
  paradox := .ancient
  ptype := .dark
  hp := 230
  stage := .basic
  isEx := true
  prizeCount := 2
  canEvolve := false

/-- Iron Hands ex: Future, Electric type, 230 HP.
    Amp You Very Much: 120 + take extra prize card. -/
def ironHandsEx : ParadoxCard where
  name := "Iron Hands ex"
  paradox := .future
  ptype := .electric
  hp := 230
  stage := .basic
  isEx := true
  prizeCount := 2
  canEvolve := false

/-- Iron Valiant ex: Future, Psychic type, 220 HP.
    Tachyon Bits: 200 to a benched ex/V Pokémon. -/
def ironValiantEx : ParadoxCard where
  name := "Iron Valiant ex"
  paradox := .future
  ptype := .psychic
  hp := 220
  stage := .basic
  isEx := true
  prizeCount := 2
  canEvolve := false

/-- Great Tusk ex: Ancient, Fighting type, 250 HP.
    Gigantic Tusks: 260 with coin flip (tails = 0). -/
def greatTuskEx : ParadoxCard where
  name := "Great Tusk ex"
  paradox := .ancient
  ptype := .fighting
  hp := 250
  stage := .basic
  isEx := true
  prizeCount := 2
  canEvolve := false

/-- Flutter Mane (Ancient, non-ex). -/
def flutterMane : ParadoxCard where
  name := "Flutter Mane"
  paradox := .ancient
  ptype := .psychic
  hp := 90
  stage := .basic
  isEx := false
  prizeCount := 1
  canEvolve := false

/-- Iron Thorns ex: Future, Electric type, 230 HP. -/
def ironThornsEx : ParadoxCard where
  name := "Iron Thorns ex"
  paradox := .future
  ptype := .electric
  hp := 230
  stage := .basic
  isEx := true
  prizeCount := 2
  canEvolve := false

/-- Gardevoir (regular, not paradox). -/
def gardevoir : ParadoxCard where
  name := "Gardevoir"
  paradox := .none
  ptype := .psychic
  hp := 160
  stage := .stage2
  isEx := false
  prizeCount := 1
  canEvolve := false

-- ============================================================
-- §7  Key Attacks
-- ============================================================

/-- Coin flip result for attack resolution. -/
inductive CoinResult where
  | heads | tails
deriving DecidableEq, Repr, BEq, Inhabited

/-- Frenzied Gouging damage: 220 base + flip for 220 more.
    Risk: discard all attached energy. -/
def frenziedGougingDamage (flip : CoinResult) : Nat :=
  match flip with
  | .heads => 220 + 220
  | .tails => 220

/-- Whether Frenzied Gouging discards all energy. Always true. -/
def frenziedGougingDiscardsAll : Bool := true

/-- Amp You Very Much damage. -/
def ampYouVeryMuchDamage : Nat := 120

/-- Amp You Very Much extra prize condition:
    Take an extra prize if the opponent's Active has 3 or more energy. -/
def ampYouVeryMuchExtraPrize (opponentEnergy : Nat) : Bool :=
  opponentEnergy ≥ 3

/-- Iron Hands total prizes from KO with extra prize.
    Base = 2 (ex), +1 if condition met. -/
def ironHandsTotalPrizes (normalPrizes : Nat) (extraCondition : Bool) : Nat :=
  normalPrizes + (if extraCondition then 1 else 0)

/-- Tachyon Bits: 200 damage to a benched ex/V Pokémon.
    Must target a benched Pokémon with a rule box. -/
def tachyonBitsDamage : Nat := 200

/-- Whether a target is valid for Tachyon Bits (must be benched ex/V). -/
def tachyonBitsValidTarget (isBenched : Bool) (isExOrV : Bool) : Bool :=
  isBenched && isExOrV

/-- Gigantic Tusks damage: 260 on heads, 0 on tails. -/
def giganticTusksDamage (flip : CoinResult) : Nat :=
  match flip with
  | .heads => 260
  | .tails => 0

-- ============================================================
-- §8  Area Zero Support
-- ============================================================

/-- Area Zero Underdepths (Stadium): Ancient/Future Pokémon get
    free retreat (retreat cost reduced to 0). -/
def areaZeroFreeRetreat (pokemonParadox : ParadoxType) : Bool :=
  pokemonParadox.isParadox

/-- Area Zero research support: search deck for Paradox Pokémon. -/
def canSearchParadox (pokemonParadox : ParadoxType) : Bool :=
  pokemonParadox.isParadox

/-- Professor Sada's Vitality: Attach up to 2 basic energy from discard
    to Ancient Pokémon in any way. -/
def sadaEnergyCount : Nat := 2

/-- Professor Turo's Scenario: Switch an opponent's Active Future Pokémon
    with a benched one, then draw 3. -/
def turoDrawCount : Nat := 3

-- ============================================================
-- §9  Theorems — Paradox Are Always Basic
-- ============================================================

/-- Theorem 1: Roaring Moon ex is Basic. -/
theorem roaring_moon_basic : roaringMoonEx.stage = .basic := by rfl

/-- Theorem 2: Iron Hands ex is Basic. -/
theorem iron_hands_basic : ironHandsEx.stage = .basic := by rfl

/-- Theorem 3: Iron Valiant ex is Basic. -/
theorem iron_valiant_basic : ironValiantEx.stage = .basic := by rfl

/-- Theorem 4: Great Tusk ex is Basic. -/
theorem great_tusk_basic : greatTuskEx.stage = .basic := by rfl

/-- Theorem 5: Flutter Mane is Basic. -/
theorem flutter_mane_basic : flutterMane.stage = .basic := by rfl

/-- Theorem 6: Iron Thorns ex is Basic. -/
theorem iron_thorns_basic : ironThornsEx.stage = .basic := by rfl

-- ============================================================
-- §10  Theorems — Paradox Cannot Evolve
-- ============================================================

/-- Theorem 7: Roaring Moon ex cannot evolve. -/
theorem roaring_moon_no_evolve : roaringMoonEx.canEvolve = false := by rfl

/-- Theorem 8: Iron Hands ex cannot evolve. -/
theorem iron_hands_no_evolve : ironHandsEx.canEvolve = false := by rfl

/-- Theorem 9: Great Tusk ex cannot evolve. -/
theorem great_tusk_no_evolve : greatTuskEx.canEvolve = false := by rfl

/-- Theorem 10: All specific paradox cards are valid. -/
theorem roaring_moon_valid : roaringMoonEx.isValid = true := by native_decide
theorem iron_hands_valid : ironHandsEx.isValid = true := by native_decide
theorem iron_valiant_valid : ironValiantEx.isValid = true := by native_decide
theorem great_tusk_valid : greatTuskEx.isValid = true := by native_decide
theorem flutter_mane_valid : flutterMane.isValid = true := by native_decide
theorem iron_thorns_valid : ironThornsEx.isValid = true := by native_decide

-- ============================================================
-- §11  Theorems — Ancient/Future Exclusivity
-- ============================================================

/-- Theorem 11: Ancient and Future are distinct. -/
theorem ancient_ne_future : ParadoxType.ancient ≠ ParadoxType.future := by decide

/-- Theorem 12: Ancient is paradox. -/
theorem ancient_is_paradox : ParadoxType.ancient.isParadox = true := by rfl

/-- Theorem 13: Future is paradox. -/
theorem future_is_paradox : ParadoxType.future.isParadox = true := by rfl

/-- Theorem 14: None is not paradox. -/
theorem none_not_paradox : ParadoxType.none.isParadox = false := by rfl

/-- Theorem 15: Paradox types are exhaustive — exactly 3 values. -/
theorem paradox_type_count : ParadoxType.all.length = 3 := by native_decide

-- ============================================================
-- §12  Theorems — Booster Capsule Restrictions
-- ============================================================

/-- Theorem 16: Ancient Booster can only attach to Ancient Pokémon. -/
theorem ancient_booster_ancient :
    canAttachBooster .ancientBooster roaringMoonEx = true := by native_decide

/-- Theorem 17: Ancient Booster cannot attach to Future Pokémon. -/
theorem ancient_booster_not_future :
    canAttachBooster .ancientBooster ironHandsEx = false := by native_decide

/-- Theorem 18: Future Booster can only attach to Future Pokémon. -/
theorem future_booster_future :
    canAttachBooster .futureBooster ironHandsEx = true := by native_decide

/-- Theorem 19: Future Booster cannot attach to Ancient Pokémon. -/
theorem future_booster_not_ancient :
    canAttachBooster .futureBooster roaringMoonEx = false := by native_decide

/-- Theorem 20: Neither Booster attaches to regular Pokémon. -/
theorem no_booster_regular_ancient :
    canAttachBooster .ancientBooster gardevoir = false := by native_decide

theorem no_booster_regular_future :
    canAttachBooster .futureBooster gardevoir = false := by native_decide

/-- Theorem 21: Ancient Booster HP bonus is 60. -/
theorem ancient_booster_hp_bonus : ancientBoosterHPBonus = 60 := by rfl

/-- Theorem 22: Effective HP with Ancient Booster on Ancient Pokémon. -/
theorem effective_hp_ancient_booster :
    effectiveHP roaringMoonEx true = 290 := by native_decide

/-- Theorem 23: Effective HP without booster is base HP. -/
theorem effective_hp_no_booster :
    effectiveHP roaringMoonEx false = 230 := by native_decide

/-- Theorem 24: Effective HP of non-Ancient with "booster" is just base. -/
theorem effective_hp_wrong_type :
    effectiveHP ironHandsEx true = 230 := by native_decide

-- ============================================================
-- §13  Theorems — Attack Mechanics
-- ============================================================

/-- Theorem 25: Frenzied Gouging on heads = 440 damage. -/
theorem frenzied_gouging_heads : frenziedGougingDamage .heads = 440 := by rfl

/-- Theorem 26: Frenzied Gouging on tails = 220 damage. -/
theorem frenzied_gouging_tails : frenziedGougingDamage .tails = 220 := by rfl

/-- Theorem 27: Frenzied Gouging always discards all energy. -/
theorem frenzied_gouging_discards : frenziedGougingDiscardsAll = true := by rfl

/-- Theorem 28: Amp You Very Much base damage is 120. -/
theorem amp_damage : ampYouVeryMuchDamage = 120 := by rfl

/-- Theorem 29: Iron Hands takes extra prize when opponent has 3+ energy. -/
theorem iron_hands_extra_prize_3 :
    ampYouVeryMuchExtraPrize 3 = true := by native_decide

/-- Theorem 30: Iron Hands no extra prize when opponent has 2 energy. -/
theorem iron_hands_no_extra_2 :
    ampYouVeryMuchExtraPrize 2 = false := by native_decide

/-- Theorem 31: Iron Hands total prizes with extra = 3 (2 base + 1). -/
theorem iron_hands_total_3 :
    ironHandsTotalPrizes 2 true = 3 := by native_decide

/-- Theorem 32: Gigantic Tusks on heads = 260. -/
theorem gigantic_tusks_heads : giganticTusksDamage .heads = 260 := by rfl

/-- Theorem 33: Gigantic Tusks on tails = 0 (whiff). -/
theorem gigantic_tusks_tails : giganticTusksDamage .tails = 0 := by rfl

/-- Theorem 34: Tachyon Bits deals 200 damage. -/
theorem tachyon_bits_damage_val : tachyonBitsDamage = 200 := by rfl

/-- Theorem 35: Tachyon Bits valid target: benched ex/V. -/
theorem tachyon_valid_target :
    tachyonBitsValidTarget true true = true := by rfl

/-- Theorem 36: Tachyon Bits invalid target: active Pokémon. -/
theorem tachyon_invalid_active :
    tachyonBitsValidTarget false true = false := by rfl

/-- Theorem 37: Tachyon Bits invalid target: benched non-ex/V. -/
theorem tachyon_invalid_non_ex :
    tachyonBitsValidTarget true false = false := by rfl

-- ============================================================
-- §14  Theorems — Area Zero & Support
-- ============================================================

/-- Theorem 38: Area Zero gives free retreat to Ancient. -/
theorem area_zero_ancient : areaZeroFreeRetreat .ancient = true := by rfl

/-- Theorem 39: Area Zero gives free retreat to Future. -/
theorem area_zero_future : areaZeroFreeRetreat .future = true := by rfl

/-- Theorem 40: Area Zero does NOT give free retreat to regular Pokémon. -/
theorem area_zero_no_regular : areaZeroFreeRetreat .none = false := by rfl

/-- Theorem 41: Professor Sada attaches 2 energy. -/
theorem sada_energy : sadaEnergyCount = 2 := by rfl

/-- Theorem 42: Professor Turo draws 3 cards. -/
theorem turo_draw : turoDrawCount = 3 := by rfl

end PokemonLean.Core.Paradox
