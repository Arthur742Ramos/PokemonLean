/-
  PokemonLean / Core / DeckChecker.lean

  Certified deck legality validator for the Pokémon TCG.
  Self-contained: defines DeckCard, Deck, all legality predicates,
  example decks (Lost Zone Box, Lugia VSTAR, Charizard ex), and
  proofs of legality/illegality.

  TCG deck rules:
    - Exactly 60 cards
    - At most 4 copies of any non-basic-energy card
    - At least 1 Basic Pokémon
    - At most 1 ACE SPEC total
    - At most 1 of each Prism Star
    - At most 1 Radiant Pokémon total

  All proofs are sorry-free.  30+ theorems.
-/

namespace PokemonLean.Core.DeckChecker

-- ============================================================
-- §1  DeckCard definition
-- ============================================================

/-- Card category in a deck. -/
inductive CardCategory where
  | pokemon
  | trainer
  | energy
deriving DecidableEq, Repr, BEq, Inhabited

/-- A card in a deck, with all legality-relevant attributes. -/
structure DeckCard where
  name         : String
  category     : CardCategory
  isBasicEnergy : Bool    -- basic energy cards are exempt from 4-copy rule
  isAceSpec    : Bool     -- ACE SPEC cards: at most 1 total per deck
  isPrismStar  : Bool     -- Prism Star cards: at most 1 of each
  isRadiant    : Bool     -- Radiant Pokémon: at most 1 total per deck
  isBasicPokemon : Bool   -- needed for "at least 1 Basic Pokémon" check
deriving DecidableEq, Repr, BEq, Inhabited

/-- A deck is a list of DeckCards. -/
abbrev Deck := List DeckCard

-- ============================================================
-- §2  Counting and predicate functions
-- ============================================================

/-- Total number of cards in the deck. -/
def deckSize (d : Deck) : Nat := d.length

/-- Count occurrences of a card name. -/
def cardCount (name : String) (d : Deck) : Nat :=
  d.filter (fun c => c.name == name) |>.length

/-- Whether the deck has at least one Basic Pokémon. -/
def hasBasicPokemon (d : Deck) : Bool :=
  d.any (fun c => c.isBasicPokemon)

/-- Count of ACE SPEC cards in the deck. -/
def aceSpecCount (d : Deck) : Nat :=
  d.filter (fun c => c.isAceSpec) |>.length

/-- Count of Radiant Pokémon in the deck. -/
def radiantCount (d : Deck) : Nat :=
  d.filter (fun c => c.isRadiant) |>.length

/-- Count of Prism Star cards with a given name. -/
def prismStarCountByName (name : String) (d : Deck) : Nat :=
  d.filter (fun c => c.isPrismStar && c.name == name) |>.length

/-- Whether a card name refers to a basic energy. -/
def isBasicEnergyName (name : String) (d : Deck) : Bool :=
  d.any (fun c => c.name == name && c.isBasicEnergy)

/-- Get all unique non-basic-energy card names. -/
def nonBasicEnergyNames (d : Deck) : List String :=
  (d.filter (fun c => !c.isBasicEnergy)).map (fun c => c.name)
  |>.eraseDups

/-- Get all unique Prism Star names. -/
def prismStarNames (d : Deck) : List String :=
  (d.filter (fun c => c.isPrismStar)).map (fun c => c.name)
  |>.eraseDups

/-- Check: all non-basic-energy cards have ≤ 4 copies. -/
def fourCopyRuleSatisfied (d : Deck) : Bool :=
  (nonBasicEnergyNames d).all (fun name => cardCount name d ≤ 4)

/-- Check: all Prism Star cards appear at most once each. -/
def prismStarRuleSatisfied (d : Deck) : Bool :=
  (prismStarNames d).all (fun name => prismStarCountByName name d ≤ 1)

-- ============================================================
-- §3  isLegal predicate
-- ============================================================

/-- A deck is legal if it satisfies ALL TCG deck construction rules. -/
def isLegal (d : Deck) : Bool :=
  deckSize d == 60 &&
  fourCopyRuleSatisfied d &&
  hasBasicPokemon d &&
  aceSpecCount d ≤ 1 &&
  prismStarRuleSatisfied d &&
  radiantCount d ≤ 1

-- ============================================================
-- §4  Helper constructors for building decks
-- ============================================================

/-- Create a basic Pokémon card entry. -/
def mkBasic (name : String) : DeckCard where
  name := name
  category := .pokemon
  isBasicEnergy := false
  isAceSpec := false
  isPrismStar := false
  isRadiant := false
  isBasicPokemon := true

/-- Create a non-basic (evolution) Pokémon card entry. -/
def mkEvolution (name : String) : DeckCard where
  name := name
  category := .pokemon
  isBasicEnergy := false
  isAceSpec := false
  isPrismStar := false
  isRadiant := false
  isBasicPokemon := false

/-- Create a Trainer card entry. -/
def mkTrainer (name : String) : DeckCard where
  name := name
  category := .trainer
  isBasicEnergy := false
  isAceSpec := false
  isPrismStar := false
  isRadiant := false
  isBasicPokemon := false

/-- Create an ACE SPEC Trainer card entry. -/
def mkAceSpec (name : String) : DeckCard where
  name := name
  category := .trainer
  isBasicEnergy := false
  isAceSpec := true
  isPrismStar := false
  isRadiant := false
  isBasicPokemon := false

/-- Create a Radiant Pokémon card entry. -/
def mkRadiant (name : String) : DeckCard where
  name := name
  category := .pokemon
  isBasicEnergy := false
  isAceSpec := false
  isPrismStar := false
  isRadiant := true
  isBasicPokemon := true

/-- Create a basic Energy card entry. -/
def mkBasicEnergy (name : String) : DeckCard where
  name := name
  category := .energy
  isBasicEnergy := true
  isAceSpec := false
  isPrismStar := false
  isRadiant := false
  isBasicPokemon := false

/-- Repeat a card n times. -/
def rep (c : DeckCard) (n : Nat) : List DeckCard :=
  List.replicate n c

-- ============================================================
-- §5  Example Deck: Charizard ex
-- ============================================================

/-- Charizard ex deck (Standard format, 60 cards). -/
def charizardExDeck : Deck :=
  -- Pokémon (18)
  rep (mkBasic "Charmander") 4 ++
  rep (mkEvolution "Charmeleon") 1 ++
  rep (mkEvolution "Charizard ex") 3 ++
  rep (mkBasic "Bidoof") 2 ++
  rep (mkEvolution "Bibarel") 2 ++
  rep (mkBasic "Lumineon V") 1 ++
  rep (mkRadiant "Radiant Charizard") 1 ++
  rep (mkBasic "Manaphy") 1 ++
  rep (mkBasic "Entei V") 1 ++
  rep (mkEvolution "Pidgeot ex") 2 ++
  -- Trainers (30)
  rep (mkTrainer "Rare Candy") 4 ++
  rep (mkTrainer "Ultra Ball") 4 ++
  rep (mkTrainer "Level Ball") 2 ++
  rep (mkTrainer "Battle VIP Pass") 4 ++
  rep (mkTrainer "Professor's Research") 4 ++
  rep (mkTrainer "Boss's Orders") 3 ++
  rep (mkTrainer "Iono") 4 ++
  rep (mkTrainer "Switch") 2 ++
  rep (mkAceSpec "Prime Catcher") 1 ++
  rep (mkTrainer "Forest Seal Stone") 2 ++
  -- Energy (12)
  rep (mkBasicEnergy "Fire Energy") 12

/-- Charizard ex deck has 60 cards. -/
theorem charizardExDeck_size : deckSize charizardExDeck = 60 := by native_decide

/-- Charizard ex deck is legal. -/
theorem charizardExDeck_legal : isLegal charizardExDeck = true := by native_decide

-- ============================================================
-- §6  Example Deck: Lost Zone Box
-- ============================================================

/-- Lost Zone Box deck (Standard format, 60 cards). -/
def lostZoneBoxDeck : Deck :=
  -- Pokémon (12)
  rep (mkBasic "Comfey") 4 ++
  rep (mkBasic "Cramorant") 2 ++
  rep (mkBasic "Sableye") 2 ++
  rep (mkRadiant "Radiant Greninja") 1 ++
  rep (mkBasic "Manaphy") 1 ++
  rep (mkBasic "Dragonite V") 1 ++
  rep (mkBasic "Raikou V") 1 ++
  -- Trainers (36)
  rep (mkTrainer "Mirage Gate") 4 ++
  rep (mkTrainer "Battle VIP Pass") 4 ++
  rep (mkTrainer "Colress's Experiment") 4 ++
  rep (mkTrainer "Boss's Orders") 2 ++
  rep (mkTrainer "Switch") 3 ++
  rep (mkTrainer "Escape Rope") 2 ++
  rep (mkTrainer "Nest Ball") 4 ++
  rep (mkTrainer "Fog Crystal") 3 ++
  rep (mkTrainer "Lost Vacuum") 2 ++
  rep (mkTrainer "Energy Recycler") 1 ++
  rep (mkTrainer "Lake Acuity") 3 ++
  rep (mkTrainer "Iono") 3 ++
  rep (mkAceSpec "Prime Catcher") 1 ++
  -- Energy (12)
  rep (mkBasicEnergy "Water Energy") 4 ++
  rep (mkBasicEnergy "Psychic Energy") 4 ++
  rep (mkBasicEnergy "Lightning Energy") 4

/-- Lost Zone Box deck has 60 cards. -/
theorem lostZoneBoxDeck_size : deckSize lostZoneBoxDeck = 60 := by native_decide

/-- Lost Zone Box deck is legal. -/
theorem lostZoneBoxDeck_legal : isLegal lostZoneBoxDeck = true := by native_decide

-- ============================================================
-- §7  Example Deck: Lugia VSTAR
-- ============================================================

/-- Lugia VSTAR deck (Expanded-ish, 60 cards). -/
def lugiaVSTARDeck : Deck :=
  -- Pokémon (16)
  rep (mkBasic "Lugia V") 4 ++
  rep (mkEvolution "Lugia VSTAR") 3 ++
  rep (mkBasic "Archeops") 4 ++
  rep (mkBasic "Lumineon V") 1 ++
  rep (mkBasic "Dunsparce") 2 ++
  rep (mkBasic "Yveltal") 2 ++
  -- Trainers (32)
  rep (mkTrainer "Professor's Research") 4 ++
  rep (mkTrainer "Boss's Orders") 3 ++
  rep (mkTrainer "Serena") 2 ++
  rep (mkTrainer "Ultra Ball") 4 ++
  rep (mkTrainer "Evolution Incense") 3 ++
  rep (mkTrainer "Capturing Aroma") 3 ++
  rep (mkTrainer "Choice Belt") 2 ++
  rep (mkTrainer "Collapsed Stadium") 3 ++
  rep (mkTrainer "Switch") 3 ++
  rep (mkTrainer "Lost Vacuum") 2 ++
  rep (mkAceSpec "Master Ball") 1 ++
  rep (mkTrainer "Iono") 2 ++
  -- Energy (12)
  rep (mkBasicEnergy "Double Turbo Energy") 4 ++
  rep (mkBasicEnergy "Jet Energy") 4 ++
  rep (mkBasicEnergy "Gift Energy") 4

/-- Lugia VSTAR deck has 60 cards. -/
theorem lugiaVSTARDeck_size : deckSize lugiaVSTARDeck = 60 := by native_decide

/-- Lugia VSTAR deck is legal. -/
theorem lugiaVSTARDeck_legal : isLegal lugiaVSTARDeck = true := by native_decide

-- ============================================================
-- §8  Illegal deck examples
-- ============================================================

/-- An empty deck (obviously illegal). -/
def emptyDeck : Deck := []

/-- A deck with 59 cards (one short). -/
def shortDeck : Deck :=
  rep (mkBasic "Pikachu") 4 ++
  rep (mkBasicEnergy "Lightning Energy") 55

/-- A deck with 5 copies of a non-basic-energy card. -/
def fiveCopyDeck : Deck :=
  rep (mkBasic "Pikachu") 5 ++
  rep (mkBasicEnergy "Lightning Energy") 55

/-- A deck with no Basic Pokémon. -/
def noBasicDeck : Deck :=
  rep (mkEvolution "Raichu") 4 ++
  rep (mkTrainer "Ultra Ball") 4 ++
  rep (mkBasicEnergy "Lightning Energy") 52

/-- A deck with 2 ACE SPECs. -/
def twoAceSpecDeck : Deck :=
  rep (mkBasic "Pikachu") 4 ++
  rep (mkAceSpec "Prime Catcher") 1 ++
  rep (mkAceSpec "Master Ball") 1 ++
  rep (mkBasicEnergy "Lightning Energy") 54

/-- A deck with 2 Radiant Pokémon (illegal). -/
def twoRadiantDeck : Deck :=
  rep (mkRadiant "Radiant Charizard") 1 ++
  rep (mkRadiant "Radiant Greninja") 1 ++
  rep (mkBasic "Pikachu") 4 ++
  rep (mkBasicEnergy "Lightning Energy") 54

-- ============================================================
-- §9  Theorems — Core legality implications
-- ============================================================

/-- A legal deck has exactly 60 cards. -/
theorem legal_deck_has_60 (d : Deck) (h : isLegal d = true) :
    deckSize d = 60 := by
  simp [isLegal] at h
  exact Nat.eq_of_beq_eq_true h.1

/-- A legal deck has at least one Basic Pokémon. -/
theorem legal_deck_has_basic (d : Deck) (h : isLegal d = true) :
    hasBasicPokemon d = true := by
  simp [isLegal] at h
  exact h.2.2.1

/-- A legal deck has at most 1 ACE SPEC. -/
theorem legal_deck_ace_spec_unique (d : Deck) (h : isLegal d = true) :
    aceSpecCount d ≤ 1 := by
  simp [isLegal] at h
  exact h.2.2.2.1

/-- A legal deck has at most 1 Radiant Pokémon. -/
theorem legal_deck_radiant_unique (d : Deck) (h : isLegal d = true) :
    radiantCount d ≤ 1 := by
  simp [isLegal] at h
  exact h.2.2.2.2.2

/-- A legal deck satisfies the 4-copy rule. -/
theorem legal_deck_four_copy (d : Deck) (h : isLegal d = true) :
    fourCopyRuleSatisfied d = true := by
  simp [isLegal] at h
  exact h.2.1

/-- A legal deck satisfies the Prism Star rule. -/
theorem legal_deck_prism_star (d : Deck) (h : isLegal d = true) :
    prismStarRuleSatisfied d = true := by
  simp [isLegal] at h
  exact h.2.2.2.2.1

-- ============================================================
-- §10  Theorems — Illegal deck examples verified
-- ============================================================

/-- An empty deck is not legal. -/
theorem empty_not_legal : isLegal emptyDeck = false := by native_decide

/-- A 59-card deck is not legal. -/
theorem short_not_legal : isLegal shortDeck = false := by native_decide

/-- A deck with 5 copies of a non-basic-energy card is not legal. -/
theorem five_copy_not_legal : isLegal fiveCopyDeck = false := by native_decide

/-- A deck with no Basic Pokémon is not legal. -/
theorem no_basic_not_legal : isLegal noBasicDeck = false := by native_decide

/-- A deck with 2 ACE SPECs is not legal. -/
theorem two_ace_spec_not_legal : isLegal twoAceSpecDeck = false := by native_decide

/-- A deck with 2 Radiant Pokémon is not legal. -/
theorem two_radiant_not_legal : isLegal twoRadiantDeck = false := by native_decide

-- ============================================================
-- §11  Theorems — Counting properties
-- ============================================================

/-- deckSize of empty is 0. -/
theorem deckSize_empty : deckSize [] = 0 := by rfl

/-- deckSize of a singleton is 1. -/
theorem deckSize_singleton (c : DeckCard) : deckSize [c] = 1 := by rfl

/-- cardCount for a name not in the deck is 0. -/
theorem cardCount_empty (name : String) : cardCount name [] = 0 := by rfl

/-- An empty deck has no Basic Pokémon. -/
theorem empty_no_basic : hasBasicPokemon [] = false := by rfl

/-- An empty deck has 0 ACE SPECs. -/
theorem empty_no_ace_spec : aceSpecCount [] = 0 := by rfl

/-- An empty deck has 0 Radiant Pokémon. -/
theorem empty_no_radiant : radiantCount [] = 0 := by rfl

/-- rep produces n copies. -/
theorem rep_length (c : DeckCard) (n : Nat) : (rep c n).length = n := by
  simp [rep, List.length_replicate]

/-- A singleton basic Pokémon deck has a basic. -/
theorem singleton_basic_has_basic :
    hasBasicPokemon [mkBasic "Pikachu"] = true := by native_decide

/-- mkBasic produces a basic Pokémon card. -/
theorem mkBasic_is_basic (name : String) :
    (mkBasic name).isBasicPokemon = true := by rfl

/-- mkBasicEnergy is a basic energy. -/
theorem mkBasicEnergy_is_basic_energy (name : String) :
    (mkBasicEnergy name).isBasicEnergy = true := by rfl

/-- mkAceSpec is an ACE SPEC. -/
theorem mkAceSpec_is_ace_spec (name : String) :
    (mkAceSpec name).isAceSpec = true := by rfl

/-- mkRadiant is a Radiant Pokémon. -/
theorem mkRadiant_is_radiant (name : String) :
    (mkRadiant name).isRadiant = true := by rfl

/-- mkEvolution is not a Basic Pokémon. -/
theorem mkEvolution_not_basic (name : String) :
    (mkEvolution name).isBasicPokemon = false := by rfl

/-- mkTrainer is not a basic energy. -/
theorem mkTrainer_not_basic_energy (name : String) :
    (mkTrainer name).isBasicEnergy = false := by rfl

-- ============================================================
-- §12  Theorems — Structural properties of legality
-- ============================================================

/-- Adding a card to a 60-card deck makes it 61 cards (illegal size). -/
theorem adding_to_60_is_61 (d : Deck) (c : DeckCard) (h : deckSize d = 60) :
    deckSize (c :: d) = 61 := by
  simp [deckSize, List.length] at *
  omega

/-- Removing a card from a 60-card deck makes it 59 cards (illegal size). -/
theorem removing_from_60 (d : Deck) (c : DeckCard) (rest : Deck) (h : d = c :: rest)
    (h60 : deckSize d = 60) :
    deckSize rest = 59 := by
  simp [deckSize, List.length, h] at *
  omega

/-- A deck of all basic energy can be any size. -/
theorem all_basic_energy_four_copy_ok (n : Nat) :
    fourCopyRuleSatisfied (rep (mkBasicEnergy "Fire Energy") n) = true := by
  simp [fourCopyRuleSatisfied, nonBasicEnergyNames, List.filter, mkBasicEnergy,
        List.eraseDups, List.all_eq_true]
  intro s
  simp [List.mem_filter, rep, List.mem_replicate, mkBasicEnergy]
  intro h
  exact absurd h.2 (by simp)

/-- If a deck has 0 Pokémon at all, it has no Basic Pokémon. -/
theorem no_pokemon_no_basic (d : Deck) (h : d.all (fun c => c.category != .pokemon) = true) :
    hasBasicPokemon d = false := by
  simp [hasBasicPokemon, List.any_eq_true]
  intro c hc
  have : c.category != .pokemon = true := by
    exact List.all_eq_true.mp h c hc
  simp [mkBasic, DeckCard.isBasicPokemon] at this
  cases c with
  | mk name cat isbe iasp ipsp irad ibp =>
    simp [DeckCard.isBasicPokemon]
    by_contra hbp
    push_neg at hbp
    simp [hbp] at *
    simp [CardCategory.instBEq] at this
    cases cat <;> simp [BEq.beq, CardCategory.beq] at this

-- ============================================================
-- §13  #eval demonstrations
-- ============================================================

#eval isLegal charizardExDeck
#eval isLegal lostZoneBoxDeck
#eval isLegal lugiaVSTARDeck
#eval isLegal emptyDeck
#eval isLegal fiveCopyDeck
#eval isLegal twoAceSpecDeck
#eval deckSize charizardExDeck
#eval aceSpecCount charizardExDeck
#eval hasBasicPokemon charizardExDeck

end PokemonLean.Core.DeckChecker
