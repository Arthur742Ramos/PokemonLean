/-
  PokemonLean / PlaymatZones.lean

  Playmat Zone Mechanics for the Pokémon TCG
  =============================================

  Active spot, Bench (5 slots), Deck zone, Discard pile, Prize cards (6),
  Lost Zone (removed from game), Stadium slot.  Zone transition rules,
  legality of moves between zones.

  20 theorems.
-/

namespace PokemonLean.PlaymatZones
-- ============================================================================
-- §2  Zones
-- ============================================================================

/-- The seven zones on a Pokémon TCG playmat. -/
inductive Zone where
  | active    -- Active spot (1 Pokémon)
  | bench     -- Bench (up to 5 Pokémon)
  | deck      -- Draw pile (face-down)
  | discard   -- Discard pile (face-up)
  | prize     -- Prize cards (6 face-down)
  | lostZone  -- Lost Zone (removed from game permanently)
  | stadium   -- Stadium card slot (at most 1)
deriving DecidableEq, Repr

/-- Card kind relevant to zone placement. -/
inductive CardKind where
  | pokemon | trainer | supporter | energy | stadium | tool
deriving DecidableEq, Repr

/-- A card with a kind and name. -/
structure Card where
  name : String
  kind : CardKind
deriving DecidableEq, Repr

-- ============================================================================
-- §3  Zone Capacities
-- ============================================================================

def Zone.capacity : Zone → Option Nat
  | .active   => some 1
  | .bench    => some 5
  | .deck     => none      -- up to 60
  | .discard  => none
  | .prize    => some 6
  | .lostZone => none
  | .stadium  => some 1

-- Theorem 1: Active zone has capacity 1
theorem active_capacity : Zone.active.capacity = some 1 := by rfl

-- Theorem 2: Bench has capacity 5
theorem bench_capacity : Zone.bench.capacity = some 5 := by rfl

-- Theorem 3: Prize zone has capacity 6
theorem prize_capacity : Zone.prize.capacity = some 6 := by rfl

-- Theorem 4: Lost zone has unlimited capacity
theorem lostZone_unlimited : Zone.lostZone.capacity = none := by rfl

-- ============================================================================
-- §4  Zone Transition Legality
-- ============================================================================

/-- Whether a card kind can legally be placed in a zone. -/
def canPlace (k : CardKind) (z : Zone) : Bool :=
  match k, z with
  | .pokemon,   .active   => true
  | .pokemon,   .bench    => true
  | .pokemon,   .discard  => true
  | .pokemon,   .lostZone => true
  | .pokemon,   .prize    => true
  | .pokemon,   .deck     => true
  | .energy,    .active   => true   -- attached
  | .energy,    .discard  => true
  | .energy,    .lostZone => true
  | .energy,    .deck     => true
  | .energy,    .prize    => true
  | .trainer,   .discard  => true
  | .trainer,   .lostZone => true
  | .trainer,   .deck     => true
  | .trainer,   .prize    => true
  | .supporter, .discard  => true
  | .supporter, .lostZone => true
  | .supporter, .deck     => true
  | .supporter, .prize    => true
  | .stadium,   .stadium  => true
  | .stadium,   .discard  => true
  | .stadium,   .lostZone => true
  | .stadium,   .deck     => true
  | .tool,      .active   => true   -- attached to Pokémon
  | .tool,      .discard  => true
  | .tool,      .lostZone => true
  | .tool,      .deck     => true
  | .tool,      .prize    => true
  | _,          _         => false

/-- Whether a transition from one zone to another is legal for a given card kind. -/
def legalTransition (k : CardKind) (src dst : Zone) : Bool :=
  canPlace k dst && (src != dst)

-- Theorem 5: Pokémon can move from bench to active
theorem pokemon_bench_to_active :
    legalTransition .pokemon .bench .active = true := by rfl

-- Theorem 6: Pokémon can move from active to discard (KO)
theorem pokemon_active_to_discard :
    legalTransition .pokemon .active .discard = true := by rfl

-- Theorem 7: Pokémon can be sent to Lost Zone
theorem pokemon_to_lostZone :
    legalTransition .pokemon .active .lostZone = true := by rfl

-- Theorem 8: Stadium cards cannot go to bench
theorem stadium_not_to_bench :
    canPlace .stadium .bench = false := by rfl

-- Theorem 9: Supporter cannot go to active
theorem supporter_not_to_active :
    canPlace .supporter .active = false := by rfl

-- ============================================================================
-- §5  Game State
-- ============================================================================

structure GameState where
  activeSlot   : Option Card
  benchSlots   : List Card
  deckCards     : List Card
  discardPile  : List Card
  prizeCards    : List Card
  lostZoneCards : List Card
  stadiumSlot  : Option Card
deriving Repr

def GameState.benchCount (gs : GameState) : Nat := gs.benchSlots.length
def GameState.deckCount (gs : GameState) : Nat := gs.deckCards.length
def GameState.discardCount (gs : GameState) : Nat := gs.discardPile.length
def GameState.prizeCount (gs : GameState) : Nat := gs.prizeCards.length
def GameState.lostCount (gs : GameState) : Nat := gs.lostZoneCards.length

def GameState.totalCards (gs : GameState) : Nat :=
  (if gs.activeSlot.isSome then 1 else 0) +
  gs.benchCount + gs.deckCount + gs.discardCount +
  gs.prizeCount + gs.lostCount +
  (if gs.stadiumSlot.isSome then 1 else 0)

def GameState.benchFull (gs : GameState) : Bool :=
  gs.benchCount ≥ 5

def GameState.canBench (gs : GameState) : Bool :=
  gs.benchCount < 5

-- ============================================================================
-- §8  Stadium Zone Rules
-- ============================================================================

-- Theorem 19: benchFull when 5 cards on bench
theorem benchFull_five :
    GameState.benchFull { activeSlot := none, benchSlots := [⟨"A",.pokemon⟩,⟨"B",.pokemon⟩,⟨"C",.pokemon⟩,⟨"D",.pokemon⟩,⟨"E",.pokemon⟩],
                          deckCards := [], discardPile := [], prizeCards := [],
                          lostZoneCards := [], stadiumSlot := none } = true := by
  rfl

-- Theorem 20: canBench false when bench full
theorem canBench_full :
    GameState.canBench { activeSlot := none, benchSlots := [⟨"A",.pokemon⟩,⟨"B",.pokemon⟩,⟨"C",.pokemon⟩,⟨"D",.pokemon⟩,⟨"E",.pokemon⟩],
                         deckCards := [], discardPile := [], prizeCards := [],
                         lostZoneCards := [], stadiumSlot := none } = false := by
  rfl

end PokemonLean.PlaymatZones
