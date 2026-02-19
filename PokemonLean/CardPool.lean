import PokemonLean.Basic

namespace PokemonLean.CardPool

open PokemonLean

-- ============================================================================
-- RARITY & SET METADATA
-- ============================================================================

inductive Rarity
  | common
  | uncommon
  | rare
  | holo
  | ultraRare
  | secretRare
  deriving Repr, BEq, DecidableEq

inductive CardSet
  | baseSet
  | scarletViolet
  | obsidianFlames
  | paldeaEvolved
  | paradoxRift
  deriving Repr, BEq, DecidableEq

inductive CardVariant
  | normal
  | ex       -- Pokémon ex: give 2 prizes when KO'd
  | v        -- Pokémon V: give 2 prizes when KO'd
  | vstar    -- Pokémon VSTAR: give 2 prizes, has VSTAR power
  deriving Repr, BEq, DecidableEq

/-- Prize value when this card is KO'd. -/
def prizeValue : CardVariant → Nat
  | .normal => 1
  | .ex     => 2
  | .v      => 2
  | .vstar  => 2

/-- Extended card with metadata. -/
structure CardEntry where
  card : Card
  rarity : Rarity
  cardSet : CardSet
  variant : CardVariant := .normal
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- FIRE TYPE CARDS
-- ============================================================================

def charmander : Card :=
  { name := "Charmander", hp := 70, energyType := .fire
  , attacks := [{ name := "Ember", baseDamage := 30, effects := [], energyCost := [.fire] }]
  , weakness := some { energyType := .water }, resistance := none }

def charmeleon : Card :=
  { name := "Charmeleon", hp := 100, energyType := .fire
  , attacks := [{ name := "Slash", baseDamage := 50, effects := [], energyCost := [.fire, .colorless] }]
  , weakness := some { energyType := .water }, resistance := none }

def charizard : Card :=
  { name := "Charizard", hp := 170, energyType := .fire
  , attacks := [{ name := "Fire Blast", baseDamage := 120, effects := [], energyCost := [.fire, .fire, .colorless] }]
  , weakness := some { energyType := .water }, resistance := none }

def charizardEx : Card :=
  { name := "Charizard ex", hp := 330, energyType := .fire
  , attacks := [{ name := "Burning Dark", baseDamage := 180, effects := [], energyCost := [.fire, .fire, .colorless] }
               ,{ name := "Inferno Reign", baseDamage := 250, effects := [], energyCost := [.fire, .fire, .fire, .colorless] }]
  , weakness := some { energyType := .water }, resistance := none }

def arcanine : Card :=
  { name := "Arcanine", hp := 140, energyType := .fire
  , attacks := [{ name := "Fire Mane", baseDamage := 90, effects := [], energyCost := [.fire, .colorless, .colorless] }]
  , weakness := some { energyType := .water }, resistance := none }

def magmar : Card :=
  { name := "Magmar", hp := 80, energyType := .fire
  , attacks := [{ name := "Flamethrower", baseDamage := 70, effects := [], energyCost := [.fire, .colorless] }]
  , weakness := some { energyType := .water }, resistance := none }

def entei : Card :=
  { name := "Entei", hp := 130, energyType := .fire
  , attacks := [{ name := "Inferno Dance", baseDamage := 20, effects := [], energyCost := [.fire] }
               ,{ name := "Bursting Flame", baseDamage := 120, effects := [], energyCost := [.fire, .fire, .colorless] }]
  , weakness := some { energyType := .water }, resistance := none }

-- ============================================================================
-- WATER TYPE CARDS
-- ============================================================================

def squirtle : Card :=
  { name := "Squirtle", hp := 60, energyType := .water
  , attacks := [{ name := "Water Gun", baseDamage := 20, effects := [], energyCost := [.water] }]
  , weakness := some { energyType := .lightning }, resistance := none }

def wartortle : Card :=
  { name := "Wartortle", hp := 90, energyType := .water
  , attacks := [{ name := "Wave Splash", baseDamage := 40, effects := [], energyCost := [.water, .colorless] }]
  , weakness := some { energyType := .lightning }, resistance := none }

def blastoise : Card :=
  { name := "Blastoise", hp := 160, energyType := .water
  , attacks := [{ name := "Hydro Pump", baseDamage := 130, effects := [], energyCost := [.water, .water, .colorless] }]
  , weakness := some { energyType := .lightning }, resistance := none }

def lapras : Card :=
  { name := "Lapras", hp := 130, energyType := .water
  , attacks := [{ name := "Ice Beam", baseDamage := 80, effects := [.applyStatus .paralyzed], energyCost := [.water, .colorless, .colorless] }]
  , weakness := some { energyType := .lightning }, resistance := none }

def gyarados : Card :=
  { name := "Gyarados", hp := 150, energyType := .water
  , attacks := [{ name := "Hyper Beam", baseDamage := 100, effects := [], energyCost := [.water, .water, .colorless] }]
  , weakness := some { energyType := .lightning }, resistance := none }

def suicune : Card :=
  { name := "Suicune", hp := 120, energyType := .water
  , attacks := [{ name := "Blizzard Rondo", baseDamage := 70, effects := [.addDamage 20], energyCost := [.water, .colorless] }]
  , weakness := some { energyType := .lightning }, resistance := none }

-- ============================================================================
-- GRASS TYPE CARDS
-- ============================================================================

def bulbasaur : Card :=
  { name := "Bulbasaur", hp := 70, energyType := .grass
  , attacks := [{ name := "Vine Whip", baseDamage := 20, effects := [], energyCost := [.grass] }]
  , weakness := some { energyType := .fire }, resistance := none }

def ivysaur : Card :=
  { name := "Ivysaur", hp := 100, energyType := .grass
  , attacks := [{ name := "Razor Leaf", baseDamage := 50, effects := [], energyCost := [.grass, .colorless] }]
  , weakness := some { energyType := .fire }, resistance := none }

def venusaur : Card :=
  { name := "Venusaur", hp := 160, energyType := .grass
  , attacks := [{ name := "Solar Beam", baseDamage := 120, effects := [], energyCost := [.grass, .grass, .colorless] }]
  , weakness := some { energyType := .fire }, resistance := none }

def sceptile : Card :=
  { name := "Sceptile", hp := 150, energyType := .grass
  , attacks := [{ name := "Leaf Blade", baseDamage := 110, effects := [], energyCost := [.grass, .grass] }]
  , weakness := some { energyType := .fire }, resistance := none }

def leafeon : Card :=
  { name := "Leafeon", hp := 110, energyType := .grass
  , attacks := [{ name := "Leaf Guard", baseDamage := 40, effects := [.heal 30], energyCost := [.grass, .colorless] }]
  , weakness := some { energyType := .fire }, resistance := none }

-- ============================================================================
-- LIGHTNING TYPE CARDS
-- ============================================================================

def pikachu : Card :=
  { name := "Pikachu", hp := 60, energyType := .lightning
  , attacks := [{ name := "Thunder Shock", baseDamage := 20, effects := [.applyStatus .paralyzed], energyCost := [.lightning] }]
  , weakness := some { energyType := .fighting }, resistance := some { energyType := .metal } }

def raichu : Card :=
  { name := "Raichu", hp := 120, energyType := .lightning
  , attacks := [{ name := "Thunderbolt", baseDamage := 100, effects := [], energyCost := [.lightning, .lightning, .colorless] }]
  , weakness := some { energyType := .fighting }, resistance := some { energyType := .metal } }

def pikachuEx : Card :=
  { name := "Pikachu ex", hp := 200, energyType := .lightning
  , attacks := [{ name := "Circle Circuit", baseDamage := 90, effects := [.addDamage 30], energyCost := [.lightning, .lightning] }
               ,{ name := "Topfull Thunderbolt", baseDamage := 200, effects := [], energyCost := [.lightning, .lightning, .colorless] }]
  , weakness := some { energyType := .fighting }, resistance := none }

def jolteon : Card :=
  { name := "Jolteon", hp := 100, energyType := .lightning
  , attacks := [{ name := "Pin Missile", baseDamage := 60, effects := [], energyCost := [.lightning, .colorless] }]
  , weakness := some { energyType := .fighting }, resistance := none }

def luxray : Card :=
  { name := "Luxray", hp := 150, energyType := .lightning
  , attacks := [{ name := "Wild Charge", baseDamage := 120, effects := [], energyCost := [.lightning, .lightning, .colorless] }]
  , weakness := some { energyType := .fighting }, resistance := none }

-- ============================================================================
-- PSYCHIC TYPE CARDS
-- ============================================================================

def ralts : Card :=
  { name := "Ralts", hp := 60, energyType := .psychic
  , attacks := [{ name := "Psychic", baseDamage := 20, effects := [], energyCost := [.psychic] }]
  , weakness := some { energyType := .dark }, resistance := none }

def kirlia : Card :=
  { name := "Kirlia", hp := 80, energyType := .psychic
  , attacks := [{ name := "Psybeam", baseDamage := 40, effects := [.applyStatus .confused], energyCost := [.psychic, .colorless] }]
  , weakness := some { energyType := .dark }, resistance := none }

def gardevoir : Card :=
  { name := "Gardevoir", hp := 150, energyType := .psychic
  , attacks := [{ name := "Psychic Shot", baseDamage := 100, effects := [], energyCost := [.psychic, .psychic, .colorless] }]
  , weakness := some { energyType := .dark }, resistance := none }

def gardevoirEx : Card :=
  { name := "Gardevoir ex", hp := 310, energyType := .psychic
  , attacks := [{ name := "Miracle Force", baseDamage := 190, effects := [], energyCost := [.psychic, .psychic, .psychic] }]
  , weakness := some { energyType := .dark }, resistance := none }

def mewtwo : Card :=
  { name := "Mewtwo", hp := 130, energyType := .psychic
  , attacks := [{ name := "Psydrive", baseDamage := 120, effects := [], energyCost := [.psychic, .psychic, .colorless] }]
  , weakness := some { energyType := .dark }, resistance := none }

-- ============================================================================
-- FIGHTING TYPE CARDS
-- ============================================================================

def machop : Card :=
  { name := "Machop", hp := 70, energyType := .fighting
  , attacks := [{ name := "Low Kick", baseDamage := 20, effects := [], energyCost := [.fighting] }]
  , weakness := some { energyType := .psychic }, resistance := none }

def machoke : Card :=
  { name := "Machoke", hp := 100, energyType := .fighting
  , attacks := [{ name := "Karate Chop", baseDamage := 60, effects := [], energyCost := [.fighting, .colorless] }]
  , weakness := some { energyType := .psychic }, resistance := none }

def machamp : Card :=
  { name := "Machamp", hp := 170, energyType := .fighting
  , attacks := [{ name := "Seismic Toss", baseDamage := 130, effects := [], energyCost := [.fighting, .fighting, .colorless] }]
  , weakness := some { energyType := .psychic }, resistance := none }

def lucario : Card :=
  { name := "Lucario", hp := 130, energyType := .fighting
  , attacks := [{ name := "Aura Sphere", baseDamage := 80, effects := [.addDamage 30], energyCost := [.fighting, .colorless] }]
  , weakness := some { energyType := .psychic }, resistance := none }

-- ============================================================================
-- DARK TYPE CARDS
-- ============================================================================

def umbreon : Card :=
  { name := "Umbreon", hp := 110, energyType := .dark
  , attacks := [{ name := "Dark Pulse", baseDamage := 80, effects := [], energyCost := [.dark, .colorless] }]
  , weakness := some { energyType := .fighting }, resistance := none }

def tyranitar : Card :=
  { name := "Tyranitar", hp := 180, energyType := .dark
  , attacks := [{ name := "Mountain Swing", baseDamage := 150, effects := [], energyCost := [.dark, .dark, .colorless] }]
  , weakness := some { energyType := .fighting }, resistance := none }

def darkrai : Card :=
  { name := "Darkrai", hp := 120, energyType := .dark
  , attacks := [{ name := "Dark Void", baseDamage := 80, effects := [.applyStatus .asleep], energyCost := [.dark, .dark] }]
  , weakness := some { energyType := .fighting }, resistance := none }

-- ============================================================================
-- METAL TYPE CARDS
-- ============================================================================

def magnemite : Card :=
  { name := "Magnemite", hp := 60, energyType := .metal
  , attacks := [{ name := "Thunder Wave", baseDamage := 20, effects := [.applyStatus .paralyzed], energyCost := [.metal] }]
  , weakness := some { energyType := .fire }, resistance := some { energyType := .grass } }

def magneton : Card :=
  { name := "Magneton", hp := 90, energyType := .metal
  , attacks := [{ name := "Tri Attack", baseDamage := 50, effects := [], energyCost := [.metal, .colorless] }]
  , weakness := some { energyType := .fire }, resistance := some { energyType := .grass } }

def magnezone : Card :=
  { name := "Magnezone", hp := 160, energyType := .metal
  , attacks := [{ name := "Electro Ball", baseDamage := 120, effects := [], energyCost := [.metal, .metal, .colorless] }]
  , weakness := some { energyType := .fire }, resistance := some { energyType := .grass } }

-- ============================================================================
-- DRAGON TYPE CARDS
-- ============================================================================

def dratini : Card :=
  { name := "Dratini", hp := 60, energyType := .dragon
  , attacks := [{ name := "Wrap", baseDamage := 20, effects := [], energyCost := [.colorless] }]
  , weakness := none, resistance := none }

def dragonair : Card :=
  { name := "Dragonair", hp := 90, energyType := .dragon
  , attacks := [{ name := "Twister", baseDamage := 50, effects := [], energyCost := [.water, .lightning] }]
  , weakness := none, resistance := none }

def dragonite : Card :=
  { name := "Dragonite", hp := 170, energyType := .dragon
  , attacks := [{ name := "Hurricane Charge", baseDamage := 130, effects := [], energyCost := [.water, .lightning, .colorless] }]
  , weakness := none, resistance := none }

-- ============================================================================
-- FAIRY TYPE CARDS
-- ============================================================================

def clefairy : Card :=
  { name := "Clefairy", hp := 50, energyType := .fairy
  , attacks := [{ name := "Sing", baseDamage := 10, effects := [.applyStatus .asleep], energyCost := [.fairy] }]
  , weakness := some { energyType := .metal }, resistance := some { energyType := .dark } }

def clefable : Card :=
  { name := "Clefable", hp := 100, energyType := .fairy
  , attacks := [{ name := "Moon Blast", baseDamage := 60, effects := [], energyCost := [.fairy, .colorless] }]
  , weakness := some { energyType := .metal }, resistance := some { energyType := .dark } }

-- ============================================================================
-- COLORLESS TYPE CARDS
-- ============================================================================

def eevee : Card :=
  { name := "Eevee", hp := 60, energyType := .colorless
  , attacks := [{ name := "Tackle", baseDamage := 20, effects := [], energyCost := [.colorless] }]
  , weakness := some { energyType := .fighting }, resistance := none }

def snorlax : Card :=
  { name := "Snorlax", hp := 150, energyType := .colorless
  , attacks := [{ name := "Body Slam", baseDamage := 80, effects := [.applyStatus .paralyzed], energyCost := [.colorless, .colorless, .colorless] }]
  , weakness := some { energyType := .fighting }, resistance := none }

-- ============================================================================
-- COMPLETE CARD POOL
-- ============================================================================

def allCards : List Card :=
  [ charmander, charmeleon, charizard, charizardEx, arcanine, magmar, entei
  , squirtle, wartortle, blastoise, lapras, gyarados, suicune
  , bulbasaur, ivysaur, venusaur, sceptile, leafeon
  , pikachu, raichu, pikachuEx, jolteon, luxray
  , ralts, kirlia, gardevoir, gardevoirEx, mewtwo
  , machop, machoke, machamp, lucario
  , umbreon, tyranitar, darkrai
  , magnemite, magneton, magnezone
  , dratini, dragonair, dragonite
  , clefairy, clefable
  , eevee, snorlax
  ]

def allCardEntries : List CardEntry :=
  [ ⟨charmander, .common, .baseSet, .normal⟩
  , ⟨charmeleon, .uncommon, .baseSet, .normal⟩
  , ⟨charizard, .rare, .baseSet, .normal⟩
  , ⟨charizardEx, .ultraRare, .obsidianFlames, .ex⟩
  , ⟨arcanine, .uncommon, .baseSet, .normal⟩
  , ⟨magmar, .common, .baseSet, .normal⟩
  , ⟨entei, .holo, .paldeaEvolved, .normal⟩
  , ⟨squirtle, .common, .baseSet, .normal⟩
  , ⟨wartortle, .uncommon, .baseSet, .normal⟩
  , ⟨blastoise, .rare, .baseSet, .normal⟩
  , ⟨lapras, .uncommon, .scarletViolet, .normal⟩
  , ⟨gyarados, .rare, .scarletViolet, .normal⟩
  , ⟨suicune, .holo, .paldeaEvolved, .normal⟩
  , ⟨bulbasaur, .common, .baseSet, .normal⟩
  , ⟨ivysaur, .uncommon, .baseSet, .normal⟩
  , ⟨venusaur, .rare, .baseSet, .normal⟩
  , ⟨sceptile, .rare, .paradoxRift, .normal⟩
  , ⟨leafeon, .uncommon, .paldeaEvolved, .normal⟩
  , ⟨pikachu, .common, .baseSet, .normal⟩
  , ⟨raichu, .rare, .baseSet, .normal⟩
  , ⟨pikachuEx, .ultraRare, .scarletViolet, .ex⟩
  , ⟨jolteon, .uncommon, .scarletViolet, .normal⟩
  , ⟨luxray, .rare, .obsidianFlames, .normal⟩
  , ⟨ralts, .common, .scarletViolet, .normal⟩
  , ⟨kirlia, .uncommon, .scarletViolet, .normal⟩
  , ⟨gardevoir, .rare, .scarletViolet, .normal⟩
  , ⟨gardevoirEx, .ultraRare, .scarletViolet, .ex⟩
  , ⟨mewtwo, .holo, .scarletViolet, .normal⟩
  , ⟨machop, .common, .scarletViolet, .normal⟩
  , ⟨machoke, .uncommon, .scarletViolet, .normal⟩
  , ⟨machamp, .rare, .scarletViolet, .normal⟩
  , ⟨lucario, .uncommon, .paldeaEvolved, .normal⟩
  , ⟨umbreon, .uncommon, .obsidianFlames, .normal⟩
  , ⟨tyranitar, .rare, .obsidianFlames, .normal⟩
  , ⟨darkrai, .holo, .paradoxRift, .normal⟩
  , ⟨magnemite, .common, .scarletViolet, .normal⟩
  , ⟨magneton, .uncommon, .scarletViolet, .normal⟩
  , ⟨magnezone, .rare, .scarletViolet, .normal⟩
  , ⟨dratini, .common, .paradoxRift, .normal⟩
  , ⟨dragonair, .uncommon, .paradoxRift, .normal⟩
  , ⟨dragonite, .rare, .paradoxRift, .normal⟩
  , ⟨clefairy, .common, .scarletViolet, .normal⟩
  , ⟨clefable, .uncommon, .scarletViolet, .normal⟩
  , ⟨eevee, .common, .scarletViolet, .normal⟩
  , ⟨snorlax, .uncommon, .paldeaEvolved, .normal⟩
  ]

-- ============================================================================
-- CARD WELL-FORMEDNESS
-- ============================================================================

/-- A card is well-formed if it has positive HP and at least one attack. -/
def cardWellFormed (card : Card) : Prop :=
  card.hp > 0 ∧ card.attacks.length > 0

/-- All cards in the pool are well-formed. -/
theorem allCardsWellFormed : ∀ card ∈ allCards, cardWellFormed card := by
  intro card hIn
  simp [allCards] at hIn
  rcases hIn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals (simp [cardWellFormed, charmander, charmeleon, charizard, charizardEx, arcanine, magmar, entei,
    squirtle, wartortle, blastoise, lapras, gyarados, suicune,
    bulbasaur, ivysaur, venusaur, sceptile, leafeon,
    pikachu, raichu, pikachuEx, jolteon, luxray,
    ralts, kirlia, gardevoir, gardevoirEx, mewtwo,
    machop, machoke, machamp, lucario,
    umbreon, tyranitar, darkrai,
    magnemite, magneton, magnezone,
    dratini, dragonair, dragonite,
    clefairy, clefable, eevee, snorlax])

-- ============================================================================
-- CARD POOL SIZE THEOREMS
-- ============================================================================

theorem allCards_length : allCards.length = 45 := by native_decide

theorem allCards_nonempty : allCards ≠ [] := by
  simp [allCards]

-- ============================================================================
-- CARD SEARCH & FILTER FUNCTIONS
-- ============================================================================

/-- Filter cards by energy type. -/
def cardsByType (energyType : EnergyType) : List Card :=
  allCards.filter (fun c => decide (c.energyType = energyType))

/-- Filter card entries by rarity. -/
def cardsByRarity (r : Rarity) : List CardEntry :=
  allCardEntries.filter (fun e => e.rarity == r)

/-- Filter card entries by set. -/
def cardsBySet (s : CardSet) : List CardEntry :=
  allCardEntries.filter (fun e => e.cardSet == s)

/-- Filter card entries by variant (ex, V, VSTAR). -/
def cardsByVariant (v : CardVariant) : List CardEntry :=
  allCardEntries.filter (fun e => e.variant == v)

/-- Find a card by name. -/
def findCard (name : String) : Option Card :=
  allCards.find? (fun c => c.name == name)

/-- Filter cards with HP above a threshold. -/
def cardsWithMinHP (minHP : Nat) : List Card :=
  allCards.filter (fun c => c.hp ≥ minHP)

/-- Filter cards with base damage above a threshold (first attack). -/
def cardsWithMinDamage (minDmg : Nat) : List Card :=
  allCards.filter (fun c =>
    match c.attacks with
    | [] => false
    | a :: _ => a.baseDamage ≥ minDmg)

-- ============================================================================
-- FILTER SUBSET THEOREMS
-- ============================================================================

theorem cardsByType_subset (t : EnergyType) :
    ∀ c ∈ cardsByType t, c ∈ allCards := by
  intro c hc
  simp [cardsByType] at hc
  exact hc.1

theorem cardsByType_correct (t : EnergyType) :
    ∀ c ∈ cardsByType t, c.energyType = t := by
  intro c hc
  simp only [cardsByType, List.mem_filter, decide_eq_true_eq] at hc
  exact hc.2

theorem cardsWithMinHP_subset (n : Nat) :
    ∀ c ∈ cardsWithMinHP n, c ∈ allCards := by
  intro c hc
  simp [cardsWithMinHP] at hc
  exact hc.1

theorem cardsWithMinHP_correct (n : Nat) :
    ∀ c ∈ cardsWithMinHP n, c.hp ≥ n := by
  intro c hc
  simp [cardsWithMinHP] at hc
  exact hc.2

theorem cardsWithMinDamage_subset (n : Nat) :
    ∀ c ∈ cardsWithMinDamage n, c ∈ allCards := by
  intro c hc
  simp [cardsWithMinDamage] at hc
  exact hc.1

-- ============================================================================
-- PRIZE VALUE THEOREMS
-- ============================================================================

@[simp] theorem prizeValue_normal : prizeValue .normal = 1 := rfl
@[simp] theorem prizeValue_ex : prizeValue .ex = 2 := rfl
@[simp] theorem prizeValue_v : prizeValue .v = 2 := rfl
@[simp] theorem prizeValue_vstar : prizeValue .vstar = 2 := rfl

theorem prizeValue_pos (v : CardVariant) : 0 < prizeValue v := by
  cases v <;> simp [prizeValue]

theorem prizeValue_le_two (v : CardVariant) : prizeValue v ≤ 2 := by
  cases v <;> simp [prizeValue]

theorem ex_more_prizes_than_normal : prizeValue .ex > prizeValue .normal := by decide

theorem v_more_prizes_than_normal : prizeValue .v > prizeValue .normal := by decide

theorem vstar_more_prizes_than_normal : prizeValue .vstar > prizeValue .normal := by decide

-- ============================================================================
-- EVOLUTION LINE THEOREMS
-- ============================================================================

/-- Charizard line: HP increases through evolution. -/
theorem charizard_line_hp_increasing :
    charmander.hp < charmeleon.hp ∧ charmeleon.hp < charizard.hp := by
  simp [charmander, charmeleon, charizard]

/-- Blastoise line: HP increases through evolution. -/
theorem blastoise_line_hp_increasing :
    squirtle.hp < wartortle.hp ∧ wartortle.hp < blastoise.hp := by
  simp [squirtle, wartortle, blastoise]

/-- Venusaur line: HP increases through evolution. -/
theorem venusaur_line_hp_increasing :
    bulbasaur.hp < ivysaur.hp ∧ ivysaur.hp < venusaur.hp := by
  simp [bulbasaur, ivysaur, venusaur]

/-- Machamp line: HP increases through evolution. -/
theorem machamp_line_hp_increasing :
    machop.hp < machoke.hp ∧ machoke.hp < machamp.hp := by
  simp [machop, machoke, machamp]

/-- Gardevoir line: HP increases through evolution. -/
theorem gardevoir_line_hp_increasing :
    ralts.hp < kirlia.hp ∧ kirlia.hp < gardevoir.hp := by
  simp [ralts, kirlia, gardevoir]

/-- Dragonite line: HP increases through evolution. -/
theorem dragonite_line_hp_increasing :
    dratini.hp < dragonair.hp ∧ dragonair.hp < dragonite.hp := by
  simp [dratini, dragonair, dragonite]

/-- Magnezone line: HP increases through evolution. -/
theorem magnezone_line_hp_increasing :
    magnemite.hp < magneton.hp ∧ magneton.hp < magnezone.hp := by
  simp [magnemite, magneton, magnezone]

/-- EX cards have higher HP than their normal counterparts. -/
theorem charizardEx_hp_gt_charizard :
    charizardEx.hp > charizard.hp := by
  simp [charizardEx, charizard]

theorem gardevoirEx_hp_gt_gardevoir :
    gardevoirEx.hp > gardevoir.hp := by
  simp [gardevoirEx, gardevoir]

theorem pikachuEx_hp_gt_raichu :
    pikachuEx.hp > raichu.hp := by
  simp [pikachuEx, raichu]

-- ============================================================================
-- TYPE CONSISTENCY THEOREMS
-- ============================================================================

/-- All fire cards are fire type. -/
theorem fire_cards_type :
    charmander.energyType = .fire ∧ charmeleon.energyType = .fire ∧
    charizard.energyType = .fire ∧ charizardEx.energyType = .fire ∧
    arcanine.energyType = .fire ∧ magmar.energyType = .fire ∧
    entei.energyType = .fire := by
  simp [charmander, charmeleon, charizard, charizardEx, arcanine, magmar, entei]

/-- All water cards are fire-weak. -/
theorem water_cards_weakness :
    squirtle.weakness = some { energyType := .lightning } ∧
    wartortle.weakness = some { energyType := .lightning } ∧
    blastoise.weakness = some { energyType := .lightning } := by
  simp [squirtle, wartortle, blastoise]

end PokemonLean.CardPool
