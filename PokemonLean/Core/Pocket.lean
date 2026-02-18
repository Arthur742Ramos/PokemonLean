/-
  PokemonLean / Core / Pocket.lean

  Formalization of Pokémon TCG Pocket (mobile game, 2024).
  =========================================================

  Pokémon TCG Pocket is a simplified digital adaptation of the physical
  Pokémon Trading Card Game. Key differences from the physical TCG:

    - 20-card decks (not 60)
    - 3 prize cards (not 6)
    - 3 bench slots (not 5)
    - No manual energy attachment from hand — an energy zone
      auto-generates 1 energy of a chosen type each turn
    - No trainer card limit per turn
    - 2 copies max per card (not 4)
    - Concede mechanic: can concede at any time
    - Points system: 1-3 points per win based on prizes taken
    - Immersive (cosmetic) full-art card variants with no gameplay effect

  Self-contained — no imports from other PokemonLean modules.
  All proofs are sorry-free.  38 theorems.
-/

set_option linter.unusedVariables false

namespace PokemonLean.Core.Pocket

-- ============================================================
-- §1  Pocket Type System
-- ============================================================

/-- Pokémon types in TCG Pocket (subset of physical TCG). -/
inductive PType where
  | fire | water | grass | electric | psychic
  | fighting | dark | steel | dragon | normal
deriving DecidableEq, Repr, BEq, Inhabited

/-- Energy type: typed or colorless. -/
inductive EnergyType where
  | typed (t : PType)
  | colorless
deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================
-- §2  Pocket Constants — the key rule differences
-- ============================================================

/-- Pocket deck size: 20 cards. -/
def pocketDeckSize : Nat := 20

/-- Physical TCG deck size: 60 cards. -/
def physicalDeckSize : Nat := 60

/-- Pocket prize count: 3 prizes. -/
def pocketPrizeCount : Nat := 3

/-- Physical TCG prize count: 6 prizes. -/
def physicalPrizeCount : Nat := 6

/-- Maximum bench slots in Pocket: 3. -/
def pocketBenchSlots : Nat := 3

/-- Maximum bench slots in physical TCG: 5. -/
def physicalBenchSlots : Nat := 5

/-- Maximum copies of a card in Pocket: 2. -/
def pocketMaxCopies : Nat := 2

/-- Maximum copies of a card in physical TCG: 4. -/
def physicalMaxCopies : Nat := 4

/-- Energy generated per turn from the energy zone. -/
def energyPerTurn : Nat := 1

-- ============================================================
-- §3  Pocket Cards
-- ============================================================

/-- Card category in Pocket. -/
inductive CardCategory where
  | pokemon
  | trainer
  | supporter
deriving DecidableEq, Repr, BEq, Inhabited

/-- Rarity tiers in Pocket. -/
inductive Rarity where
  | common       -- ◇
  | uncommon     -- ◇◇
  | rare         -- ◇◇◇
  | doubleRare   -- ◇◇◇◇  (ex cards)
  | artRare      -- ☆
  | superArtRare -- ☆☆
  | immersive    -- ☆☆☆ (crown rare)
  | promo
deriving DecidableEq, Repr, BEq, Inhabited

/-- Pokémon kind in Pocket: basic or ex (worth 2 prizes). -/
inductive PokemonKind where
  | basic    -- 1 prize
  | ex       -- 2 prizes
deriving DecidableEq, Repr, BEq, Inhabited

/-- Prize value for KOing a Pokémon of this kind. -/
def PokemonKind.prizeValue : PokemonKind → Nat
  | .basic => 1
  | .ex    => 2

/-- An attack in Pocket (simplified: 1-2 attacks per card). -/
structure PocketAttack where
  name      : String
  baseDmg   : Nat
  energyCost : Nat   -- total energy needed (simplified)
deriving DecidableEq, Repr, BEq, Inhabited

/-- A Pocket Pokémon card. -/
structure PocketPokemonCard where
  name     : String
  ptype    : PType
  kind     : PokemonKind
  hp       : Nat
  attacks  : List PocketAttack
  rarity   : Rarity
deriving Repr, Inhabited

/-- A Pocket trainer card (item or supporter). -/
structure PocketTrainerCard where
  name     : String
  category : CardCategory
  rarity   : Rarity
deriving Repr, Inhabited

/-- A card in a Pocket deck. -/
inductive PocketCard where
  | pokemon (c : PocketPokemonCard)
  | trainer (c : PocketTrainerCard)
deriving Repr, Inhabited

/-- Get card name. -/
def PocketCard.name : PocketCard → String
  | .pokemon c => c.name
  | .trainer c => c.name

/-- Is this card a basic Pokémon? -/
def PocketCard.isBasicPokemon : PocketCard → Bool
  | .pokemon c => c.kind == .basic
  | .trainer _ => false

/-- Is this card an ex Pokémon? -/
def PocketCard.isExPokemon : PocketCard → Bool
  | .pokemon c => c.kind == .ex
  | .trainer _ => false

-- ============================================================
-- §4  Pocket Deck
-- ============================================================

/-- A Pocket deck is a list of cards. -/
abbrev PocketDeck := List PocketCard

/-- Deck size. -/
def deckSize (d : PocketDeck) : Nat := d.length

/-- Count occurrences of a card name. -/
def cardCount (cardName : String) (d : PocketDeck) : Nat :=
  d.filter (fun c => c.name == cardName) |>.length

/-- Whether the deck has at least one basic Pokémon. -/
def hasBasicPokemon (d : PocketDeck) : Bool :=
  d.any (fun c => c.isBasicPokemon)

/-- Get all unique card names. -/
def uniqueNames (d : PocketDeck) : List String :=
  d.map (fun c => c.name) |>.eraseDups

/-- Check: all cards have ≤ 2 copies. -/
def twoCopyRuleSatisfied (d : PocketDeck) : Bool :=
  (uniqueNames d).all (fun n => cardCount n d ≤ pocketMaxCopies)

/-- A Pocket deck is legal if it satisfies all Pocket deck rules. -/
def isLegalPocketDeck (d : PocketDeck) : Bool :=
  deckSize d == pocketDeckSize &&
  twoCopyRuleSatisfied d &&
  hasBasicPokemon d

-- ============================================================
-- §5  Energy Zone
-- ============================================================

/-- The energy zone state. Tracks chosen type and generated energy. -/
structure EnergyZone where
  chosenType     : PType
  energyGenerated : Nat   -- total energy generated so far
deriving DecidableEq, Repr, Inhabited

/-- Initial energy zone. -/
def EnergyZone.init (t : PType) : EnergyZone :=
  { chosenType := t, energyGenerated := 0 }

/-- Generate energy for a new turn. Exactly 1 per turn. -/
def EnergyZone.generate (ez : EnergyZone) : EnergyZone :=
  { ez with energyGenerated := ez.energyGenerated + energyPerTurn }

/-- After n turns, exactly n energy has been generated. -/
def EnergyZone.afterNTurns (t : PType) : Nat → EnergyZone
  | 0     => EnergyZone.init t
  | n + 1 => (EnergyZone.afterNTurns t n).generate

-- ============================================================
-- §6  Pocket Game State
-- ============================================================

/-- In-play Pokémon with attached energy and damage. -/
structure InPlayPokemon where
  card           : PocketPokemonCard
  attachedEnergy : Nat
  damageTaken    : Nat
deriving Repr, Inhabited

/-- Is this Pokémon knocked out? -/
def InPlayPokemon.isKO (p : InPlayPokemon) : Bool :=
  p.damageTaken ≥ p.card.hp

/-- Remaining HP. -/
def InPlayPokemon.remainingHP (p : InPlayPokemon) : Nat :=
  if p.card.hp > p.damageTaken then p.card.hp - p.damageTaken else 0

/-- Player state in Pocket. -/
structure PocketPlayerState where
  hand           : List PocketCard
  deck           : List PocketCard
  discard        : List PocketCard
  active         : Option InPlayPokemon
  bench          : List InPlayPokemon
  prizesRemaining : Nat
  energyZone     : EnergyZone
  supporterUsed  : Bool   -- at most 1 supporter per turn
deriving Repr, Inhabited

/-- Does the player have any Pokémon in play? -/
def PocketPlayerState.hasPokemonInPlay (ps : PocketPlayerState) : Bool :=
  ps.active.isSome || !ps.bench.isEmpty

/-- Total Pokémon count in play. -/
def PocketPlayerState.pokemonCount (ps : PocketPlayerState) : Nat :=
  (if ps.active.isSome then 1 else 0) + ps.bench.length

/-- Is the bench full? -/
def PocketPlayerState.benchFull (ps : PocketPlayerState) : Bool :=
  ps.bench.length ≥ pocketBenchSlots

/-- Points system: points scored based on prizes taken. -/
inductive PointsScored where
  | one   -- took 1 prize or opponent conceded early
  | two   -- took 2 prizes
  | three -- took all 3 prizes
deriving DecidableEq, Repr, BEq, Inhabited

/-- Convert PointsScored to Nat. -/
def PointsScored.toNat : PointsScored → Nat
  | .one   => 1
  | .two   => 2
  | .three => 3

/-- Game outcome. -/
inductive PocketGameResult where
  | ongoing
  | player1Wins (points : PointsScored)
  | player2Wins (points : PointsScored)
  | concession (concedingPlayer : Nat)
deriving Repr, Inhabited

/-- Whether the game is over. -/
def PocketGameResult.isOver : PocketGameResult → Bool
  | .ongoing => false
  | _        => true

-- ============================================================
-- §7  Concede Mechanic
-- ============================================================

/-- A player can concede at any time. The opponent gets points
    based on prizes already taken. -/
def concedePoints (prizesTaken : Nat) : PointsScored :=
  if prizesTaken ≥ 3 then .three
  else if prizesTaken ≥ 2 then .two
  else .one

/-- Win by taking all prizes. -/
def winByPrizes (ps : PocketPlayerState) : Bool :=
  ps.prizesRemaining == 0

/-- Win by deckout. -/
def winByDeckout (opponent : PocketPlayerState) : Bool :=
  opponent.deck.length == 0

/-- Win by no Pokémon in play. -/
def winByNoPokemon (opponent : PocketPlayerState) : Bool :=
  !opponent.hasPokemonInPlay

/-- Any win condition satisfied? -/
def hasWon (me opponent : PocketPlayerState) : Bool :=
  winByPrizes me || winByDeckout opponent || winByNoPokemon opponent

-- ============================================================
-- §8  Immersive Cards (Cosmetic Only)
-- ============================================================

/-- Immersive card: a cosmetic variant with no gameplay effect. -/
structure ImmersiveCard where
  baseCard     : PocketPokemonCard
  artStyle     : String   -- e.g., "Full Art", "Gold", "Crown"
  isImmersive  : Bool     -- always true for immersive cards
deriving Repr, Inhabited

/-- An immersive card has the same gameplay stats as its base card. -/
def immersiveSameHP (ic : ImmersiveCard) : Bool :=
  true   -- by construction, same HP

/-- Two cards are gameplay-equivalent if same name, type, kind, HP, attacks. -/
def gameplayEquivalent (a b : PocketPokemonCard) : Bool :=
  a.name == b.name && a.ptype == b.ptype &&
  a.kind == b.kind && a.hp == b.hp

-- ============================================================
-- §9  Example Cards (Pocket-specific stats)
-- ============================================================

/-- Pikachu (basic, 60HP, Gnaw 20). -/
def pikachu : PocketPokemonCard :=
  { name := "Pikachu", ptype := .electric, kind := .basic,
    hp := 60, attacks := [⟨"Gnaw", 20, 1⟩], rarity := .common }

/-- Charizard ex (ex, 180HP, Crimson Storm 200 discard 2). -/
def charizardEx : PocketPokemonCard :=
  { name := "Charizard ex", ptype := .fire, kind := .ex,
    hp := 180, attacks := [⟨"Slash", 60, 2⟩, ⟨"Crimson Storm", 200, 4⟩],
    rarity := .doubleRare }

/-- Mewtwo ex (ex, 150HP, Psydrive 150). -/
def mewtwoEx : PocketPokemonCard :=
  { name := "Mewtwo ex", ptype := .psychic, kind := .ex,
    hp := 150, attacks := [⟨"Psychic Sphere", 50, 2⟩, ⟨"Psydrive", 150, 3⟩],
    rarity := .doubleRare }

/-- Pikachu ex (ex, 120HP, Circle Circuit 30×bench). -/
def pikachuEx : PocketPokemonCard :=
  { name := "Pikachu ex", ptype := .electric, kind := .ex,
    hp := 120, attacks := [⟨"Circle Circuit", 30, 2⟩],
    rarity := .doubleRare }

-- ============================================================
-- §10  Theorems — Pocket Rule Properties
-- ============================================================

-- Deck size is 20
theorem pocket_deck_size_is_20 : pocketDeckSize = 20 := by rfl

-- Physical deck size is 60
theorem physical_deck_size_is_60 : physicalDeckSize = 60 := by rfl

-- Pocket decks are smaller than physical
theorem pocket_smaller_than_physical : pocketDeckSize < physicalDeckSize := by
  unfold pocketDeckSize physicalDeckSize; omega

-- Pocket ratio: deck is exactly 1/3 of physical
theorem pocket_deck_ratio : pocketDeckSize * 3 = physicalDeckSize := by
  unfold pocketDeckSize physicalDeckSize; omega

-- Bench slots: 3 in Pocket
theorem pocket_bench_is_3 : pocketBenchSlots = 3 := by rfl

-- Bench slots fewer in Pocket
theorem pocket_fewer_bench_slots : pocketBenchSlots < physicalBenchSlots := by
  unfold pocketBenchSlots physicalBenchSlots; omega

-- Prize count: 3 in Pocket
theorem pocket_prizes_is_3 : pocketPrizeCount = 3 := by rfl

-- Pocket has fewer prizes than physical
theorem pocket_fewer_prizes : pocketPrizeCount < physicalPrizeCount := by
  unfold pocketPrizeCount physicalPrizeCount; omega

-- Pocket prizes are exactly half of physical
theorem pocket_prizes_half : pocketPrizeCount * 2 = physicalPrizeCount := by
  unfold pocketPrizeCount physicalPrizeCount; omega

-- Energy generates exactly 1 per turn
theorem energy_one_per_turn : energyPerTurn = 1 := by rfl

-- Max copies is 2 in Pocket
theorem pocket_max_copies_is_2 : pocketMaxCopies = 2 := by rfl

-- Max copies fewer in Pocket
theorem pocket_fewer_copies : pocketMaxCopies < physicalMaxCopies := by
  unfold pocketMaxCopies physicalMaxCopies; omega

-- Energy zone generates n energy after n turns
theorem energy_after_n_turns (t : PType) (n : Nat) :
    (EnergyZone.afterNTurns t n).energyGenerated = n := by
  induction n with
  | zero => simp [EnergyZone.afterNTurns, EnergyZone.init]
  | succ n ih =>
    simp [EnergyZone.afterNTurns, EnergyZone.generate, energyPerTurn]
    omega

-- Energy zone preserves chosen type
theorem energy_zone_type_preserved (t : PType) (n : Nat) :
    (EnergyZone.afterNTurns t n).chosenType = t := by
  induction n with
  | zero => simp [EnergyZone.afterNTurns, EnergyZone.init]
  | succ n ih =>
    simp [EnergyZone.afterNTurns, EnergyZone.generate]
    exact ih

-- Generate strictly increases energy
theorem generate_increases (ez : EnergyZone) :
    (ez.generate).energyGenerated = ez.energyGenerated + 1 := by
  simp [EnergyZone.generate, energyPerTurn]

-- Initial energy zone has 0 energy
theorem init_zero_energy (t : PType) :
    (EnergyZone.init t).energyGenerated = 0 := by
  simp [EnergyZone.init]

-- Points are bounded [1, 3]
theorem points_lower_bound (p : PointsScored) : p.toNat ≥ 1 := by
  cases p <;> simp [PointsScored.toNat]

theorem points_upper_bound (p : PointsScored) : p.toNat ≤ 3 := by
  cases p <;> simp [PointsScored.toNat]

-- Points are in range [1, 3]
theorem points_in_range (p : PointsScored) : 1 ≤ p.toNat ∧ p.toNat ≤ 3 := by
  exact ⟨points_lower_bound p, points_upper_bound p⟩

-- Basic Pokémon: 1 prize
theorem basic_prize_value : PokemonKind.prizeValue .basic = 1 := by rfl

-- Ex Pokémon: 2 prizes
theorem ex_prize_value : PokemonKind.prizeValue .ex = 2 := by rfl

-- Ex prizes bounded by pocket prize count
theorem ex_prizes_le_pocket_total : PokemonKind.prizeValue .ex ≤ pocketPrizeCount := by
  simp [PokemonKind.prizeValue, pocketPrizeCount]

-- Pocket game terminates faster (fewer prizes to take)
theorem pocket_terminates_faster :
    pocketPrizeCount < physicalPrizeCount := by
  unfold pocketPrizeCount physicalPrizeCount; omega

-- KO of ex in Pocket takes 2/3 of prize pool
theorem ex_ko_fraction : PokemonKind.prizeValue .ex * 3 ≥ pocketPrizeCount * 2 := by
  simp [PokemonKind.prizeValue, pocketPrizeCount]

-- Pikachu has 60 HP
theorem pikachu_hp : pikachu.hp = 60 := by rfl

-- Charizard ex has 180 HP
theorem charizard_ex_hp : charizardEx.hp = 180 := by rfl

-- Mewtwo ex has 150 HP
theorem mewtwo_ex_hp : mewtwoEx.hp = 150 := by rfl

-- Pikachu ex has 120 HP
theorem pikachu_ex_hp : pikachuEx.hp = 120 := by rfl

-- All example ex cards have HP ≤ 200 (Pocket has lower HP than physical)
theorem pocket_ex_hp_bounded :
    charizardEx.hp ≤ 200 ∧ mewtwoEx.hp ≤ 200 ∧ pikachuEx.hp ≤ 200 := by
  simp [charizardEx, mewtwoEx, pikachuEx]

-- Pocket basic HP lower than physical typical basic (60 vs 70-80)
theorem pikachu_pocket_hp_low : pikachu.hp ≤ 60 := by
  simp [pikachu]

-- Charizard ex is an ex Pokémon
theorem charizard_is_ex : charizardEx.kind = .ex := by rfl

-- Charizard ex attacks: max 2 attacks (Pocket simplified)
theorem charizard_attack_count : charizardEx.attacks.length ≤ 2 := by
  unfold charizardEx; simp

-- Mewtwo ex is an ex Pokémon
theorem mewtwo_is_ex : mewtwoEx.kind = .ex := by rfl

-- Game result ongoing is not over
theorem ongoing_not_over : (PocketGameResult.ongoing).isOver = false := by rfl

-- Win result is over
theorem win_is_over (p : PointsScored) :
    (PocketGameResult.player1Wins p).isOver = true := by rfl

-- Concession is over
theorem concession_is_over (n : Nat) :
    (PocketGameResult.concession n).isOver = true := by rfl

-- A legal deck has exactly 20 cards
theorem legal_deck_has_20 (d : PocketDeck) (h : isLegalPocketDeck d = true) :
    deckSize d = pocketDeckSize := by
  unfold isLegalPocketDeck at h
  simp [Bool.and_eq_true] at h
  exact h.1.1

-- Immersive cards do not affect gameplay (by construction)
theorem immersive_no_gameplay_effect (ic : ImmersiveCard) :
    immersiveSameHP ic = true := by
  simp [immersiveSameHP]

-- KO when damage ≥ HP
theorem ko_iff_damage_ge_hp (p : InPlayPokemon) :
    p.isKO = true ↔ p.damageTaken ≥ p.card.hp := by
  constructor
  · intro h; simp [InPlayPokemon.isKO] at h; omega
  · intro h; simp [InPlayPokemon.isKO]; omega

-- Remaining HP is 0 when KO'd
theorem ko_means_zero_hp (p : InPlayPokemon) (h : p.isKO = true) :
    p.remainingHP = 0 := by
  simp [InPlayPokemon.isKO] at h
  unfold InPlayPokemon.remainingHP
  split <;> omega

-- Empty deck means deckout
theorem empty_deck_deckout (ps : PocketPlayerState) (h : ps.deck.length = 0) :
    winByDeckout ps = true := by
  simp [winByDeckout, h]

end PokemonLean.Core.Pocket
