/-
  PokemonLean / Core / Strategy.lean

  Consolidated strategy mechanics for the Pokémon TCG.
  Merges content from: DeckBuilding, CompleteDeckBuilder, SetupAttacks,
  MillDecking, MillDeckStrategy, FieldEffects, LostZone, RegionalForms,
  WeaknessMechanics, RareCandy.

  Covers:
  - Deck archetypes: Aggro, Control, Combo, Mill, Stall
  - Setup attacks: Swords Dance, Dragon Dance, boost stacking/clamping
  - Mill strategy: Durant Devour, deck-out win condition, turns-to-KO
  - Lost Zone engine: Comfey Flower Selecting, thresholds (≥4, ≥7, ≥10)
  - Regional forms: Alolan, Galarian, Hisuian, Paldean — different types
  - Weakness exploitation: 2× damage, −30 resistance, Weakness Policy
  - Rare Candy: skip Stage 1, legality rules, evolution line validation
  - Field effects: weather/terrain duration, damage modifiers

  All proofs are sorry-free.  35+ theorems.
-/

set_option linter.unusedVariables false

namespace PokemonLean.Core.Strategy

-- ============================================================
-- §1  Card and deck types
-- ============================================================

inductive CardCategory where
  | pokemon | trainer | energy
  deriving DecidableEq, Repr

inductive EnergyKind where
  | basicEnergy | specialEnergy
  deriving DecidableEq, Repr

structure Card where
  name       : String
  category   : CardCategory
  energyKind : Option EnergyKind
  deriving DecidableEq, Repr

abbrev Deck := List Card

def deckSize (d : Deck) : Nat := d.length

def isBasicEnergy (c : Card) : Bool :=
  c.energyKind == some .basicEnergy

def countCard (d : Deck) (name : String) : Nat :=
  d.filter (fun c => c.name == name) |>.length

def countPokemon (d : Deck) : Nat :=
  d.filter (fun c => c.category == .pokemon) |>.length

def countTrainer (d : Deck) : Nat :=
  d.filter (fun c => c.category == .trainer) |>.length

def countEnergy (d : Deck) : Nat :=
  d.filter (fun c => c.category == .energy) |>.length

-- ============================================================
-- §2  Deck archetype classification
-- ============================================================

/-- Deck archetypes. -/
inductive Archetype where
  | aggro    -- Fast damage, high Pokémon count, minimize turns to win
  | control  -- Resource denial, high trainer count
  | combo    -- Specific card synergies, balanced
  | mill     -- Deck out opponent
  | stall    -- Wall + heal, deny prizes
  | unknown
  deriving DecidableEq, Repr

def classifyDeck (d : Deck) : Archetype :=
  let pct := countPokemon d
  let tct := countTrainer d
  if pct ≥ 20 then .aggro
  else if tct ≥ 35 then .control
  else if pct ≥ 12 && tct ≥ 20 then .combo
  else .unknown

/-- Theorem 1: Classification of empty deck. -/
theorem classify_empty : classifyDeck [] = .unknown := rfl

/-- Theorem 2: Pokemon count ≤ deck size. -/
theorem countPokemon_le (d : Deck) : countPokemon d ≤ deckSize d := by
  simp [countPokemon, deckSize]; exact List.length_filter_le _ _

/-- Theorem 3: Trainer count ≤ deck size. -/
theorem countTrainer_le (d : Deck) : countTrainer d ≤ deckSize d := by
  simp [countTrainer, deckSize]; exact List.length_filter_le _ _

/-- Theorem 4: Energy count ≤ deck size. -/
theorem countEnergy_le (d : Deck) : countEnergy d ≤ deckSize d := by
  simp [countEnergy, deckSize]; exact List.length_filter_le _ _

/-- Theorem 5: Adding a card increments size by 1. -/
theorem addCard_size (d : Deck) (c : Card) :
    deckSize (c :: d) = deckSize d + 1 := by
  simp [deckSize, List.length_cons]

-- ============================================================
-- §3  Mill strategy
-- ============================================================

/-- Mill win condition: opponent's deck is empty. -/
def deckOutLoss (deckCount : Nat) : Prop := deckCount = 0

structure MillState where
  oppDeck   : Nat
  oppHand   : Nat
  turnNum   : Nat
  deriving DecidableEq, Repr

def durantMill (s : MillState) (durants : Nat) : MillState :=
  { s with oppDeck := s.oppDeck - durants }

def naturalDraw (s : MillState) : MillState :=
  { s with oppDeck := s.oppDeck - 1, oppHand := s.oppHand + 1, turnNum := s.turnNum + 1 }

/-- Theorem 6: Deck-out at 0. -/
theorem deckout_zero : deckOutLoss 0 := rfl

/-- Theorem 7: Non-zero deck is not a loss. -/
theorem deckout_succ_false (n : Nat) : ¬ deckOutLoss (n + 1) := by
  simp [deckOutLoss]

/-- Theorem 8: Durant milling is non-increasing. -/
theorem durant_nonincreasing (s : MillState) (d : Nat) :
    (durantMill s d).oppDeck ≤ s.oppDeck :=
  Nat.sub_le _ _

/-- Theorem 9: Durant then draw exact zero. -/
theorem durant_then_draw_exact_zero (s : MillState) (d : Nat)
    (h : s.oppDeck = d + 1) :
    (naturalDraw (durantMill s d)).oppDeck = 0 := by
  simp [naturalDraw, durantMill, h]

-- Mill rate calculation
def naturalMillPerTurn : Nat := 1
def devourMill (durantsInPlay : Nat) : Nat := durantsInPlay

def totalMillOverTurns (activeMillPerTurn : Nat) (turns : Nat) : Nat :=
  (naturalMillPerTurn + activeMillPerTurn) * turns

def turnsToDeckOut (oppDeck : Nat) (activeMillPerTurn : Nat) : Nat :=
  let totalPerTurn := naturalMillPerTurn + activeMillPerTurn
  if totalPerTurn = 0 then 0
  else (oppDeck + totalPerTurn - 1) / totalPerTurn

/-- Theorem 10: 4 Durants mill 4 per turn. -/
theorem four_durant_mill : devourMill 4 = 4 := rfl

/-- Theorem 11: Total mill at 0 turns is 0. -/
theorem totalMill_zero (r : Nat) : totalMillOverTurns r 0 = 0 := by
  simp [totalMillOverTurns]

/-- Theorem 12: With 4 extra mill, 60-card deck-out in 12 turns. -/
theorem deckout_with_4mill : turnsToDeckOut 60 4 = 12 := by
  simp [turnsToDeckOut, naturalMillPerTurn]

/-- Theorem 13: Natural draw only: 60 turns for 60-card deck. -/
theorem deckout_natural_only : turnsToDeckOut 60 0 = 60 := by
  simp [turnsToDeckOut, naturalMillPerTurn]

-- ============================================================
-- §4  Lost Zone engine
-- ============================================================

structure LZState where
  lostZoneSize : Nat
  deckSize     : Nat
  handSize     : Nat
  oppHP        : Nat
  deriving DecidableEq, Repr

def mirageGateActive (gs : LZState) : Prop := gs.lostZoneSize ≥ 7
def lostMineActive (gs : LZState) : Prop := gs.lostZoneSize ≥ 10
def cramorantActive (gs : LZState) : Prop := gs.lostZoneSize ≥ 4

/-- Theorem 14: Colress's Experiment from 4 reaches ≥7. -/
theorem colress_from_4_reaches_7 (gs : LZState) (h4 : gs.lostZoneSize = 4) :
    mirageGateActive { gs with lostZoneSize := gs.lostZoneSize + 3 } := by
  simp [mirageGateActive]; omega

/-- Theorem 15: Two Flower Selectings from 5 reach 7. -/
theorem two_flowers_from_5 (gs : LZState) (h5 : gs.lostZoneSize = 5) :
    mirageGateActive { gs with lostZoneSize := gs.lostZoneSize + 2 } := by
  simp [mirageGateActive]; omega

/-- Theorem 16: Colress from 7 reaches 10 for Sableye Lost Mine. -/
theorem colress_from_7_reaches_10 (gs : LZState) (h7 : gs.lostZoneSize = 7) :
    lostMineActive { gs with lostZoneSize := gs.lostZoneSize + 3 } := by
  simp [lostMineActive]; omega

/-- Theorem 17: If already ≥10, still ≥7 (threshold monotonicity). -/
theorem lostmine_implies_mirage (gs : LZState)
    (h : lostMineActive gs) : mirageGateActive gs := by
  simp [lostMineActive, mirageGateActive] at *; omega

/-- Theorem 18: If ≥7 then ≥4 (threshold monotonicity). -/
theorem mirage_implies_cramorant (gs : LZState)
    (h : mirageGateActive gs) : cramorantActive gs := by
  simp [mirageGateActive, cramorantActive] at *; omega

-- ============================================================
-- §5  Regional forms
-- ============================================================

inductive Region where
  | kanto | alola | galar | hisui | paldea
  deriving DecidableEq, Repr

inductive PType where
  | normal | fire | water | grass | electric | psychic | fighting
  | dark | steel | fairy | dragon | ice | ground | rock
  | flying | poison | bug | ghost
  deriving DecidableEq, Repr

structure RegionalForm where
  dexNum    : Nat
  name      : String
  region    : Region
  type1     : PType
  deriving DecidableEq, Repr

def sameSpecies (f1 f2 : RegionalForm) : Prop :=
  f1.dexNum = f2.dexNum ∧ f1.name = f2.name

def differentTyping (f1 f2 : RegionalForm) : Prop :=
  f1.type1 ≠ f2.type1

-- Concrete
def vulpixKanto : RegionalForm := ⟨37, "Vulpix", .kanto, .fire⟩
def vulpixAlola : RegionalForm := ⟨37, "Vulpix", .alola, .ice⟩
def meowthKanto : RegionalForm := ⟨52, "Meowth", .kanto, .normal⟩
def meowthGalar : RegionalForm := ⟨52, "Meowth", .galar, .steel⟩
def wooperPaldea : RegionalForm := ⟨194, "Wooper", .paldea, .poison⟩

/-- Theorem 19: Vulpix Kanto and Alola are same species. -/
theorem vulpix_same_species : sameSpecies vulpixKanto vulpixAlola := by
  constructor <;> rfl

/-- Theorem 20: Vulpix Kanto (Fire) ≠ Alola (Ice) in type. -/
theorem vulpix_different_type : differentTyping vulpixKanto vulpixAlola := by
  simp [differentTyping, vulpixKanto, vulpixAlola]

/-- Theorem 21: Meowth Kanto (Normal) ≠ Galar (Steel). -/
theorem meowth_kanto_galar_diff_type : differentTyping meowthKanto meowthGalar := by
  simp [differentTyping, meowthKanto, meowthGalar]

/-- Regional forms count as same Pokémon for 4-copy rule. -/
structure DeckEntry where
  cardName : String
  count    : Nat
  dexNum   : Nat
  deriving DecidableEq, Repr

def totalCopies (entries : List DeckEntry) (dex : Nat) : Nat :=
  entries.filter (fun e => e.dexNum == dex) |>.foldl (fun acc e => acc + e.count) 0

/-- Theorem 22: Regional forms count as same species — 2+2 = 4 ≤ 4. -/
theorem regional_same_species_count :
    let entries := [
      DeckEntry.mk "Vulpix (Kanto)" 2 37,
      DeckEntry.mk "Vulpix (Alola)" 2 37
    ]
    totalCopies entries 37 = 4 := by native_decide

-- ============================================================
-- §6  Weakness and resistance
-- ============================================================

inductive WType where
  | fire | water | grass | lightning | psychic | fighting
  | darkness | metal | dragon | fairy | normal | colorless
  deriving DecidableEq, Repr

inductive Effectiveness where
  | weak | resist | neutral
  deriving DecidableEq, Repr

def typeChart : WType → WType → Effectiveness
  | .fire,      .water     => .weak
  | .water,     .grass     => .weak
  | .water,     .lightning => .weak
  | .grass,     .fire      => .weak
  | .lightning, .fighting  => .weak
  | .psychic,   .darkness  => .weak
  | .fighting,  .psychic   => .weak
  | .metal,     .fire      => .weak
  | .fairy,     .metal     => .weak
  | .fire,      .metal     => .resist
  | .grass,     .water     => .resist
  | _,          _          => .neutral

/-- Combined damage modifier for dual type. -/
def dualTypeDamage (base : Nat) (e1 e2 : Effectiveness) : Nat :=
  let after1 := match e1 with
    | .weak => base * 2
    | .resist => if base ≥ 30 then base - 30 else 0
    | .neutral => base
  match e2 with
    | .weak => after1 * 2
    | .resist => if after1 ≥ 30 then after1 - 30 else 0
    | .neutral => after1

/-- Theorem 23: Fire is weak to Water. -/
theorem fire_weak_to_water : typeChart .fire .water = .weak := rfl

/-- Theorem 24: Grass resists Water attacks. -/
theorem grass_resist_water : typeChart .grass .water = .resist := rfl

/-- Theorem 25: Double weakness = ×4. -/
theorem double_weakness_x4 (base : Nat) :
    dualTypeDamage base .weak .weak = base * 4 := by
  simp [dualTypeDamage, Nat.mul_assoc]

/-- Theorem 26: Double neutral = base. -/
theorem double_neutral (base : Nat) :
    dualTypeDamage base .neutral .neutral = base := by
  simp [dualTypeDamage]

/-- Theorem 27: Colorless is neutral to everything. -/
theorem colorless_neutral (t : WType) : typeChart .colorless t = .neutral := by
  cases t <;> rfl

-- ============================================================
-- §7  Rare Candy
-- ============================================================

inductive EvStage where
  | basic | stage1 | stage2 | break_
  deriving DecidableEq, Repr

structure RCPokemon where
  name        : String
  stage       : EvStage
  evolvesFrom : Option String
  deriving DecidableEq, Repr

structure InPlayPokemon where
  card       : RCPokemon
  turnPlayed : Nat
  hasEvolved : Bool
  deriving DecidableEq, Repr

structure RCGameState where
  currentTurn : Nat
  isFirstTurn : Bool
  hand        : List RCPokemon
  deriving Repr

def canUseRareCandy (gs : RCGameState) (target : InPlayPokemon) (stage2 : RCPokemon) : Prop :=
  gs.isFirstTurn = false ∧
  target.card.stage = .basic ∧
  stage2.stage = .stage2 ∧
  stage2 ∈ gs.hand ∧
  target.turnPlayed < gs.currentTurn ∧
  target.hasEvolved = false

/-- Theorem 28: Rare Candy can't be used on the first turn. -/
theorem no_rare_candy_first_turn (gs : RCGameState) (target : InPlayPokemon) (s2 : RCPokemon)
    (hFirst : gs.isFirstTurn = true) :
    ¬canUseRareCandy gs target s2 := by
  intro ⟨h, _⟩; rw [hFirst] at h; exact absurd h (by decide)

/-- Theorem 29: Rare Candy can't target a Stage 1. -/
theorem no_rare_candy_on_stage1 (gs : RCGameState) (target : InPlayPokemon) (s2 : RCPokemon)
    (hStage : target.card.stage = .stage1) :
    ¬canUseRareCandy gs target s2 := by
  intro ⟨_, hBasic, _⟩; rw [hStage] at hBasic; exact absurd hBasic (by decide)

/-- Theorem 30: Rare Candy can't evolve to a Stage 1 (must be Stage 2). -/
theorem rare_candy_needs_stage2 (gs : RCGameState) (target : InPlayPokemon) (s2 : RCPokemon)
    (hNotS2 : s2.stage ≠ .stage2) :
    ¬canUseRareCandy gs target s2 := by
  intro ⟨_, _, hS2, _⟩; exact hNotS2 hS2

/-- Theorem 31: Can't use Rare Candy on same-turn Pokémon. -/
theorem no_rare_candy_same_turn (gs : RCGameState) (target : InPlayPokemon) (s2 : RCPokemon)
    (hTurn : target.turnPlayed ≥ gs.currentTurn) :
    ¬canUseRareCandy gs target s2 := by
  intro ⟨_, _, _, _, hLt, _⟩; omega

/-- Theorem 32: Can't use Rare Candy on already-evolved Pokémon. -/
theorem no_rare_candy_already_evolved (gs : RCGameState) (target : InPlayPokemon) (s2 : RCPokemon)
    (hEvolved : target.hasEvolved = true) :
    ¬canUseRareCandy gs target s2 := by
  intro ⟨_, _, _, _, _, hFalse⟩; rw [hEvolved] at hFalse; exact absurd hFalse (by decide)

-- Evolution line validation
def inEvolutionLine (basic stage1 stage2 : RCPokemon) : Bool :=
  basic.stage == .basic &&
  stage1.stage == .stage1 &&
  stage2.stage == .stage2 &&
  stage1.evolvesFrom == some basic.name &&
  stage2.evolvesFrom == some stage1.name

def charmander : RCPokemon := ⟨"Charmander", .basic, none⟩
def charmeleon : RCPokemon := ⟨"Charmeleon", .stage1, some "Charmander"⟩
def charizard  : RCPokemon := ⟨"Charizard", .stage2, some "Charmeleon"⟩

/-- Theorem 33: Charmander → Charmeleon → Charizard is valid line. -/
theorem charmander_valid_for_charizard :
    inEvolutionLine charmander charmeleon charizard = true := by native_decide

-- ============================================================
-- §8  Setup attacks
-- ============================================================

structure Boosts where
  attack  : Int
  speed   : Int
  defense : Int
  deriving DecidableEq, Repr

def Boosts.zero : Boosts := ⟨0, 0, 0⟩

def clampBoost (n : Int) : Int :=
  if n > 6 then 6 else if n < -6 then -6 else n

structure PkmnState where
  name    : String
  baseAtk : Nat
  boosts  : Boosts
  isActive : Bool
  deriving DecidableEq, Repr

def swordsDance (s : PkmnState) : PkmnState :=
  { s with boosts := { s.boosts with attack := clampBoost (s.boosts.attack + 2) } }

def dragonDance (s : PkmnState) : PkmnState :=
  { s with boosts := { s.boosts with
      attack := clampBoost (s.boosts.attack + 1)
      speed  := clampBoost (s.boosts.speed + 1) } }

def resetBoosts (s : PkmnState) : PkmnState :=
  { s with boosts := Boosts.zero, isActive := false }

def switchIn (s : PkmnState) : PkmnState :=
  { s with isActive := true, boosts := Boosts.zero }

def effectiveAtk (s : PkmnState) : Int :=
  s.baseAtk + s.boosts.attack * 10

/-- Theorem 34: Swords Dance increases attack by 2 from zero. -/
theorem swords_dance_from_zero (s : PkmnState) (h : s.boosts.attack = 0) :
    (swordsDance s).boosts.attack = 2 := by
  simp [swordsDance, clampBoost, h]

/-- Theorem 35: Dragon Dance gives +1/+1 from zero. -/
theorem dragon_dance_from_zero (s : PkmnState)
    (ha : s.boosts.attack = 0) (hs : s.boosts.speed = 0) :
    (dragonDance s).boosts.attack = 1 ∧ (dragonDance s).boosts.speed = 1 := by
  constructor <;> simp [dragonDance, clampBoost, ha, hs]

/-- Theorem 36: Switching resets boosts. -/
theorem switch_resets (s : PkmnState) :
    (resetBoosts s).boosts = Boosts.zero := by
  simp [resetBoosts]

/-- Theorem 37: Clamp can't exceed 6. -/
theorem clamp_upper (n : Int) : clampBoost n ≤ 6 := by
  simp [clampBoost]
  split
  · omega
  · split <;> omega

/-- Theorem 38: Triple Swords Dance caps at +6. -/
theorem triple_swords_dance_capped (s : PkmnState) (h : s.boosts.attack = 0) :
    (swordsDance (swordsDance (swordsDance s))).boosts.attack = 6 := by
  simp [swordsDance, clampBoost, h]

/-- Theorem 39: Clamp is idempotent. -/
theorem clamp_idempotent (n : Int) :
    clampBoost (clampBoost n) = clampBoost n := by
  simp only [clampBoost]
  split <;> split <;> (first | rfl | (split <;> omega))

/-- Theorem 40: Effective attack increases after Swords Dance (from 0). -/
theorem eff_atk_increases (s : PkmnState) (h : s.boosts.attack = 0) :
    effectiveAtk (swordsDance s) = effectiveAtk s + 20 := by
  simp [effectiveAtk, swordsDance, clampBoost, h]

-- ============================================================
-- §9  Field effects
-- ============================================================

inductive Weather where
  | none | rain | sun | sandstorm | hail
  deriving DecidableEq, Repr

inductive Terrain where
  | none | electric | grassy | psychic | misty
  deriving DecidableEq, Repr

structure FieldState where
  weather      : Weather
  weatherTurns : Nat
  terrain      : Terrain
  terrainTurns : Nat
  deriving DecidableEq, Repr

def weatherDuration : Nat := 5

def setWeather (w : Weather) (fs : FieldState) : FieldState :=
  { fs with weather := w, weatherTurns := weatherDuration }

def tickWeather (fs : FieldState) : FieldState :=
  if fs.weatherTurns ≤ 1 then { fs with weather := .none, weatherTurns := 0 }
  else { fs with weatherTurns := fs.weatherTurns - 1 }

/-- Theorem 41: Setting weather overrides existing weather. -/
theorem weather_override (fs : FieldState) (w : Weather) :
    (setWeather w fs).weather = w := by
  simp [setWeather]

/-- Theorem 42: Setting weather resets duration. -/
theorem weather_duration_reset (fs : FieldState) (w : Weather) :
    (setWeather w fs).weatherTurns = weatherDuration := by
  simp [setWeather]

/-- Theorem 43: Weather expires when turns reach 1. -/
theorem weather_expires_at_one :
    (tickWeather (FieldState.mk .rain 1 .none 0)).weather = .none := by
  simp [tickWeather]

-- ============================================================
-- §10  Archetype classification completeness
-- ============================================================

/-- Theorem 44: Archetype classification is exhaustive. -/
theorem archetype_exhaustive (a : Archetype) :
    a = .aggro ∨ a = .control ∨ a = .combo ∨ a = .mill ∨ a = .stall ∨ a = .unknown := by
  cases a <;> simp

/-- Theorem 45: Aggro minimizes turns to win (prize-based vs mill). -/
def aggroPrizesAfter (prizeRate turns : Nat) : Nat := prizeRate * turns

theorem aggro_takes_6_in_3_turns : aggroPrizesAfter 2 3 = 6 := by
  simp [aggroPrizesAfter]

/-- Theorem 46: Mill wins via deckout (independent of prizes). -/
def millWinDeniedPrizes (oppDeck oppPrizes : Nat) : Prop :=
  oppDeck = 0 ∧ oppPrizes > 0

theorem mill_no_prizes_needed (hd : oppDeck = 0) (hp : oppPrizes > 0) :
    millWinDeniedPrizes oppDeck oppPrizes := ⟨hd, hp⟩

-- ============================================================
-- §11  Stall sustainability
-- ============================================================

def healSustainable (healPerTurn dmgPerTurn : Nat) : Bool :=
  healPerTurn ≥ dmgPerTurn

def turnsToKO (currentHP dmgPerTurn : Nat) : Nat :=
  if dmgPerTurn = 0 then 0
  else (currentHP + dmgPerTurn - 1) / dmgPerTurn

/-- Theorem 47: If damage = HP, KO in 1 turn. -/
theorem exact_ko (hp : Nat) (hpos : hp > 0) :
    turnsToKO hp hp = 1 := by
  simp [turnsToKO, Nat.ne_of_gt hpos]
  have h1 : hp + hp - 1 = hp * 1 + (hp - 1) := by omega
  rw [h1, Nat.mul_add_div hpos]
  have : hp - 1 < hp := by omega
  have h2 : (hp - 1) / hp = 0 := Nat.div_eq_zero_iff.mpr (Or.inr this)
  omega

end PokemonLean.Core.Strategy
