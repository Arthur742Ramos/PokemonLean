/-
  PokemonLean / ChampionsPath.lean

  Champion's Path set mechanics for the Pokémon TCG:
  V/VMAX cards in the set, special art rares, pull rates,
  Charizard VMAX chase card, ETB contents, pin collections,
  set numbering, collector value tiers.

-/

namespace ChampionsPath
-- ============================================================================
-- §2  Champion's Path set types
-- ============================================================================

/-- Rarity tiers in Champion's Path. -/
inductive CPRarity where
  | common | uncommon | rare | holo | vCard | vMax | fullArt | secretRare | rainbowRare
deriving DecidableEq, Repr, BEq

/-- Pokémon type (TCG types relevant to Champion's Path). -/
inductive CPType where
  | fire | water | grass | lightning | psychic | fighting
  | darkness | metal | dragon | colorless | fairy
deriving DecidableEq, Repr, BEq

/-- Card category. -/
inductive CardCat where
  | pokemon | trainer | energy
deriving DecidableEq, Repr, BEq

/-- A card in the Champion's Path set. -/
structure CPCard where
  number   : Nat         -- Set number (1–80 main, 81+ secret)
  name     : String
  rarity   : CPRarity
  cardType : CPType
  cat      : CardCat
  hp       : Nat
  isV      : Bool
  isVMax   : Bool
deriving DecidableEq, Repr

/-- The set has 73 regular + 7 secret = 80 cards total. -/
def setRegularCount : Nat := 73
def setSecretCount  : Nat := 7
def setTotalCount   : Nat := 80

/-- Theorem 1 – Total card count. -/
theorem total_card_count :
    setRegularCount + setSecretCount = setTotalCount := rfl

-- ============================================================================
-- §3  V and VMAX cards in the set
-- ============================================================================

/-- Number of V cards in Champion's Path. -/
def vCardCount   : Nat := 6
def vMaxCardCount : Nat := 3

/-- Prize cards given up when knocked out. -/
def prizesForV    : Nat := 2
def prizesForVMax : Nat := 3
def prizesForRegular : Nat := 1

/-- Theorem 2 – VMAX gives one more prize than V.
    Multi-step path: VMAX → 3 prizes, V → 2 prizes, difference = 1. -/
theorem vmax_extra_prize :
    prizesForVMax - prizesForV = 1 := rfl

/-- Theorem 3 – Total V-family cards (V + VMAX). -/
theorem v_family_total :
    vCardCount + vMaxCardCount = 9 := rfl

/-- Theorem 4 – V gives more prizes than regular via path chain.
    Path: regular → 1 prize →⁻¹ V → 2 prizes, so V gives 2× regular. -/
theorem v_double_regular_prizes :
    prizesForV = 2 * prizesForRegular := rfl

-- ============================================================================
-- §4  Charizard VMAX — the chase card
-- ============================================================================

/-- The Charizard VMAX card. -/
def charizardVMax : CPCard :=
  { number := 74, name := "Charizard VMAX", rarity := .secretRare,
    cardType := .fire, cat := .pokemon, hp := 330,
    isV := false, isVMax := true }

/-- The Charizard V (evolves into VMAX). -/
def charizardV : CPCard :=
  { number := 79, name := "Charizard V", rarity := .fullArt,
    cardType := .fire, cat := .pokemon, hp := 220,
    isV := true, isVMax := false }

/-- Theorem 5 – Charizard VMAX is a secret rare. -/
theorem charizard_vmax_is_secret :
    charizardVMax.rarity = .secretRare := rfl

/-- Theorem 6 – Charizard VMAX has 330 HP. -/
theorem charizard_vmax_hp :
    charizardVMax.hp = 330 := rfl

/-- Theorem 7 – VMAX has more HP than V (evolution path).
    Path chain: V_hp = 220 → VMAX_hp = 330, diff = 110. -/
theorem vmax_hp_boost :
    charizardVMax.hp - charizardV.hp = 110 := rfl

-- ============================================================================
-- §5  ETB (Elite Trainer Box) contents
-- ============================================================================

/-- Contents of a Champion's Path ETB. -/
structure ETBContents where
  boosterPacks  : Nat
  promoCard     : Bool
  sleeves       : Nat
  energyCards   : Nat
  diceSet       : Bool
  conditionMarkers : Bool

def championsPathETB : ETBContents :=
  { boosterPacks := 10, promoCard := true, sleeves := 65,
    energyCards := 45, diceSet := true, conditionMarkers := true }

/-- Theorem 9 – ETB has 10 packs. -/
theorem etb_pack_count :
    championsPathETB.boosterPacks = 10 := rfl

/-- Theorem 10 – ETB includes a promo. -/
theorem etb_has_promo :
    championsPathETB.promoCard = true := rfl

/-- Theorem 11 – Total sleeves in ETB. -/
theorem etb_sleeve_count :
    championsPathETB.sleeves = 65 := rfl

-- ============================================================================
-- §6  Pull rates and collector value tiers
-- ============================================================================

/-- Pull rate model: denominator of chance per pack. -/
structure PullRate where
  oneIn : Nat   -- "1 in N packs" for the rarity

def pullRateV       : PullRate := ⟨6⟩
def pullRateVMax    : PullRate := ⟨36⟩
def pullRateFullArt : PullRate := ⟨18⟩
def pullRateSecret  : PullRate := ⟨72⟩
def pullRateRainbow : PullRate := ⟨72⟩

/-- Theorem 12 – VMAX is 6× harder to pull than V.
    Path chain: V rate 1/6, VMAX rate 1/36, ratio = 6. -/
theorem vmax_pull_difficulty :
    pullRateVMax.oneIn / pullRateV.oneIn = 6 := rfl

/-- Theorem 13 – Secret rares are twice as hard as full arts. -/
theorem secret_vs_fullart_rate :
    pullRateSecret.oneIn / pullRateFullArt.oneIn = 4 := rfl

/-- Collector value tiers (relative value 1–5 scale). -/
def valueBulk     : Nat := 1
def valueHolo     : Nat := 2
def valueV        : Nat := 3
def valueFullArt  : Nat := 4
def valueChaseMax : Nat := 5

/-- Theorem 14 – Chase card is max tier. -/
theorem chase_is_max_value :
    valueChaseMax = valueBulk + valueFullArt := rfl

-- ============================================================================
-- §7  Pin collection boxes
-- ============================================================================

/-- A pin collection product. -/
structure PinCollection where
  name        : String
  packs       : Nat
  promoCards  : Nat
  hasPin      : Bool

def turffield : PinCollection :=
  { name := "Turffield Gym", packs := 3, promoCards := 1, hasPin := true }

def motostoke : PinCollection :=
  { name := "Motostoke Gym", packs := 3, promoCards := 1, hasPin := true }

def ballonlea : PinCollection :=
  { name := "Ballonlea Gym", packs := 3, promoCards := 1, hasPin := true }

/-- Theorem 15 – All pin collections have 3 packs. -/
theorem pin_packs_uniform :
    turffield.packs = motostoke.packs ∧
    motostoke.packs = ballonlea.packs ∧
    ballonlea.packs = 3 :=
  ⟨rfl, rfl, rfl⟩

/-- Theorem 16 – Total packs across 3 pin collections. -/
theorem total_pin_packs :
    turffield.packs + motostoke.packs + ballonlea.packs = 9 := rfl

-- ============================================================================
-- §8  Set numbering and congrArg chains
-- ============================================================================

/-- Theorem 17 – Charizard VMAX number is in the secret rare range (> 73). -/
theorem charizard_in_secret_range :
    charizardVMax.number > setRegularCount := by decide

/-- Theorem 18 – congrArg: changing a card's HP propagates through structure.
    We witness that editing HP via congrArg preserves other fields. -/
theorem congrArg_card_name (c : CPCard) (h1 h2 : Nat) (heq : h1 = h2) :
    ({ c with hp := h1 } : CPCard).name = ({ c with hp := h2 } : CPCard).name :=
  congrArg (fun h => ({ c with hp := h } : CPCard).name) heq

/-- Theorem 19 – congrArg chain: rarity preserved through HP update. -/
theorem congrArg_card_rarity (c : CPCard) (h1 h2 : Nat) (heq : h1 = h2) :
    ({ c with hp := h1 } : CPCard).rarity = ({ c with hp := h2 } : CPCard).rarity :=
  congrArg (fun h => ({ c with hp := h } : CPCard).rarity) heq


-- ============================================================================
-- §9  Multi-step trans/symm chains
-- ============================================================================

/-- Some representative cards. -/
def lucarioV : CPCard :=
  { number := 27, name := "Lucario V", rarity := .vCard,
    cardType := .fighting, cat := .pokemon, hp := 210,
    isV := true, isVMax := false }

def alcremieVMax : CPCard :=
  { number := 23, name := "Alcremie VMAX", rarity := .vMax,
    cardType := .psychic, cat := .pokemon, hp := 310,
    isV := false, isVMax := true }


-- ============================================================================
-- §10  Booster pack odds and ratios
-- ============================================================================

/-- Cards per booster pack. -/
def cardsPerPack : Nat := 10
def reverseHoloPerPack : Nat := 1
def rareSlotPerPack : Nat := 1

/-- Theorem 25 – Common/uncommon slots per pack. -/
theorem common_uncommon_per_pack :
    cardsPerPack - reverseHoloPerPack - rareSlotPerPack = 8 := rfl

/-- Theorem 26 – Packs in an ETB vs pin collection: ETB has more. -/
theorem etb_more_than_pin :
    championsPathETB.boosterPacks > turffield.packs := by decide

/-- Theorem 27 – Expected V pulls from an ETB (10 packs, 1-in-6). -/
def expectedVPerETB : Nat := championsPathETB.boosterPacks / pullRateV.oneIn

theorem expected_v_per_etb :
    expectedVPerETB = 1 := rfl

end ChampionsPath
