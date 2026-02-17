/-
  PokemonLean / SideboardMechanics.lean

  Pokémon TCG sideboard / best-of-three mechanics formalised via computational
  paths.  Covers: 15-card sideboard, sideboarding between games, maintaining
  60-card deck after sideboarding, tech cards, matchup-specific swaps,
  sideboard strategies (anti-meta, consistency, tech), sideboard validation.

-/

set_option linter.unusedVariables false

namespace SideboardMechanics
-- ============================================================
-- §2  Card and Deck Structures
-- ============================================================

inductive CardKind where
  | pokemon | trainer | supporter | item | tool | energy | stadium
deriving DecidableEq, Repr

structure Card where
  name : String
  kind : CardKind
deriving DecidableEq, Repr

/-- Standard deck size in competitive Pokémon TCG. -/
def standardDeckSize : Nat := 60

/-- Maximum sideboard size (best-of-three formats). -/
def maxSideboardSize : Nat := 15

-- ============================================================
-- §3  Sideboard State
-- ============================================================

/-- Full tournament deck state: main deck + sideboard. -/
structure DeckState where
  mainDeck  : List Card
  sideboard : List Card
  gameNumber : Nat        -- 1, 2, or 3 in a best-of-three
deriving Repr

def DeckState.mainSize (ds : DeckState) : Nat := ds.mainDeck.length
def DeckState.sideSize (ds : DeckState) : Nat := ds.sideboard.length
def DeckState.totalCards (ds : DeckState) : Nat := ds.mainSize + ds.sideSize

-- Example cards
def bossOrders : Card := ⟨"Boss's Orders", .supporter⟩
def enhancedHammer : Card := ⟨"Enhanced Hammer", .item⟩
def toolScrapper : Card := ⟨"Tool Scrapper", .item⟩
def marnie : Card := ⟨"Marnie", .supporter⟩
def fieldBlower : Card := ⟨"Field Blower", .item⟩
def choiceBelt : Card := ⟨"Choice Belt", .tool⟩
def bigCharm : Card := ⟨"Big Charm", .tool⟩
def templeOfSinnoh : Card := ⟨"Temple of Sinnoh", .stadium⟩
def lostVacuum : Card := ⟨"Lost Vacuum", .item⟩
def roxanne : Card := ⟨"Roxanne", .supporter⟩
def avery : Card := ⟨"Avery", .supporter⟩
def cherenscare : Card := ⟨"Cheren's Care", .supporter⟩

-- ============================================================
-- §4  Swap Operation
-- ============================================================

/-- A sideboard swap: one card in, one card out. -/
structure Swap where
  cardIn  : Card   -- from sideboard into main deck
  cardOut : Card   -- from main deck into sideboard
deriving DecidableEq, Repr

/-- Apply a single swap to a DeckState. -/
def applySwap (ds : DeckState) (sw : Swap) : DeckState :=
  { mainDeck  := sw.cardIn :: ds.mainDeck.filter (· != sw.cardOut)
    sideboard := sw.cardOut :: ds.sideboard.filter (· != sw.cardIn)
    gameNumber := ds.gameNumber }

/-- Apply a list of swaps. -/
def applySwaps (ds : DeckState) : List Swap → DeckState
  | []      => ds
  | sw :: rest => applySwaps (applySwap ds sw) rest

-- ============================================================
-- §5  Validation
-- ============================================================

/-- Sideboard is valid: at most 15 cards. -/
def validSideboard (ds : DeckState) : Prop := ds.sideSize ≤ maxSideboardSize

/-- Main deck is valid: exactly 60 cards. -/
def validMainDeck (ds : DeckState) : Prop := ds.mainSize = standardDeckSize

/-- Full tournament legality. -/
def tournamentLegal (ds : DeckState) : Prop :=
  validMainDeck ds ∧ validSideboard ds

-- ============================================================
-- §6  Strategy Tags
-- ============================================================

inductive Strategy where
  | antiMeta     -- counters popular decks
  | consistency  -- improves draw/search
  | tech         -- niche counters for specific matchups
  | aggression   -- speeds up win condition
  | control      -- slows opponent
  | hybrid       -- combination
deriving DecidableEq, Repr

structure TechCard where
  card     : Card
  strategy : Strategy
  matchup  : String    -- what matchup it's good against
deriving Repr

-- Example tech cards
def techEnhancedHammer : TechCard :=
  ⟨enhancedHammer, .antiMeta, "Special Energy decks"⟩
def techRoxanne : TechCard :=
  ⟨roxanne, .control, "When behind on prizes"⟩
def techToolScrapper : TechCard :=
  ⟨toolScrapper, .tech, "Tool-heavy decks"⟩

-- ============================================================
-- §7  Sideboard Axiom Steps
-- ============================================================


-- ============================================================
-- §8  Path Constructions
-- ============================================================

-- ============================================================
-- §9  Sideboard Validation Theorems
-- ============================================================


/-- Theorem 10: Empty swap list is identity. -/
theorem applySwaps_nil (ds : DeckState) :
    applySwaps ds [] = ds := by
  simp [applySwaps]

/-- Theorem 11: Max sideboard size is 15. -/
theorem sideboard_max : maxSideboardSize = 15 := by rfl

/-- Theorem 12: Standard deck size is 60. -/
theorem deck_standard : standardDeckSize = 60 := by rfl

/-- Theorem 13: Sideboard size bound — empty sideboard is valid. -/
theorem empty_sideboard_valid (main : List Card) (g : Nat) :
    validSideboard ⟨main, [], g⟩ := by
  simp [validSideboard, DeckState.sideSize, maxSideboardSize, List.length]


end SideboardMechanics
