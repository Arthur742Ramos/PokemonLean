/-
  PokemonLean / ACESpecCards.lean

  ACE SPEC cards formalised in Lean 4.
  Covers: the one-ACE-SPEC-per-deck rule, card definitions
  (Computer Search, Dowsing Machine, Master Ball, Scoop Up Cyclone,
  Life Dew, G Booster, G Scope, Rock Guard), deck validation,
  effect modelling, attachment rules, prize interaction.

  All proofs are sorry-free.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

-- ============================================================
-- §1  ACE SPEC card definitions
-- ============================================================

/-- Known ACE SPEC cards. -/
inductive ACESpecName where
  | computerSearch
  | dowsingMachine
  | masterBall
  | scoopUpCyclone
  | lifeDew
  | gBooster
  | gScope
  | rockGuard
  | scrambleSwitch
  | crystalWall
  | goldPotion
  | victoryPiece
deriving DecidableEq, Repr, BEq

/-- ACE SPEC sub-kind: Item-like or Tool-like (attach to Pokémon). -/
inductive ACEKind where
  | item   -- played from hand, discarded after use
  | tool   -- attached to a Pokémon
deriving DecidableEq, Repr

/-- An ACE SPEC card. -/
structure ACESpecCard where
  name : ACESpecName
  kind : ACEKind
deriving DecidableEq, Repr

-- Canonical card instances
def computerSearch   : ACESpecCard := ⟨.computerSearch,   .item⟩
def dowsingMachine   : ACESpecCard := ⟨.dowsingMachine,   .item⟩
def masterBall       : ACESpecCard := ⟨.masterBall,       .item⟩
def scoopUpCyclone   : ACESpecCard := ⟨.scoopUpCyclone,   .item⟩
def lifeDew          : ACESpecCard := ⟨.lifeDew,          .tool⟩
def gBooster         : ACESpecCard := ⟨.gBooster,         .tool⟩
def gScope           : ACESpecCard := ⟨.gScope,           .tool⟩
def rockGuard        : ACESpecCard := ⟨.rockGuard,        .tool⟩
def scrambleSwitch   : ACESpecCard := ⟨.scrambleSwitch,   .item⟩
def crystalWall      : ACESpecCard := ⟨.crystalWall,      .tool⟩
def goldPotion       : ACESpecCard := ⟨.goldPotion,       .item⟩
def victoryPiece     : ACESpecCard := ⟨.victoryPiece,     .tool⟩

-- ============================================================
-- §2  Deck representation
-- ============================================================

/-- A generic card — either an ACE SPEC or a regular card. -/
inductive DeckCard where
  | aceSpec : ACESpecCard → DeckCard
  | regular : String → DeckCard
deriving DecidableEq, Repr

/-- A deck is a list of cards. -/
abbrev Deck := List DeckCard

/-- Count how many ACE SPEC cards are in a deck. -/
def aceSpecCount (d : Deck) : Nat :=
  d.filter (fun c => match c with | .aceSpec _ => true | .regular _ => false) |>.length

/-- A deck is ACE-SPEC-valid iff it contains at most one ACE SPEC card. -/
def aceSpecValid (d : Deck) : Prop := aceSpecCount d ≤ 1

instance : Decidable (aceSpecValid d) := inferInstanceAs (Decidable (aceSpecCount d ≤ 1))

-- ============================================================
-- §3  Basic ACE SPEC validation theorems
-- ============================================================

/-- Theorem 1: An empty deck is ACE SPEC valid. -/
theorem empty_deck_valid : aceSpecValid [] := by
  simp [aceSpecValid, aceSpecCount, List.filter, List.length]

/-- Theorem 2: A deck with only regular cards is valid. -/
theorem regular_only_valid (cards : List String) :
    aceSpecValid (cards.map DeckCard.regular) := by
  induction cards with
  | nil => exact empty_deck_valid
  | cons c cs ih =>
    simp [aceSpecValid, aceSpecCount, List.filter, List.map] at *
    exact ih

/-- Theorem 3: A singleton ACE SPEC deck is valid. -/
theorem singleton_ace_valid (c : ACESpecCard) :
    aceSpecValid [.aceSpec c] := by
  simp [aceSpecValid, aceSpecCount, List.filter]

/-- Theorem 4: Two ACE SPEC cards in a deck make it invalid. -/
theorem two_ace_invalid (c₁ c₂ : ACESpecCard) (rest : Deck) :
    ¬ aceSpecValid (.aceSpec c₁ :: .aceSpec c₂ :: rest) := by
  simp [aceSpecValid, aceSpecCount, List.filter]

-- ============================================================
-- §4  ACE SPEC card effects
-- ============================================================

/-- Simplified game state for effect modelling. -/
structure GameState where
  hand       : List String
  deck       : List String
  discard    : List String
  prizes     : Nat
  benchSize  : Nat
deriving Repr

/-- Computer Search: discard 2 cards from hand, search deck for any 1 card. -/
def computerSearchEffect (gs : GameState) (discards : List String) (target : String) : Option GameState :=
  if discards.length == 2 && gs.hand.length ≥ 2 && target ∈ gs.deck then
    some { gs with
      hand := target :: (gs.hand.filter (· ∉ discards))
      deck := gs.deck.filter (· ≠ target)
      discard := discards ++ gs.discard }
  else none

/-- Dowsing Machine: discard 2 cards, recover a Trainer from discard pile. -/
def dowsingMachineEffect (gs : GameState) (discards : List String) (target : String) : Option GameState :=
  if discards.length == 2 && gs.hand.length ≥ 2 && target ∈ gs.discard then
    some { gs with
      hand := target :: (gs.hand.filter (· ∉ discards))
      discard := discards ++ (gs.discard.filter (· ≠ target)) }
  else none

/-- Master Ball: look at top 7 cards of deck, take a Pokémon. -/
def masterBallEffect (gs : GameState) (target : String) : Option GameState :=
  if target ∈ gs.deck.take 7 then
    some { gs with
      hand := target :: gs.hand
      deck := gs.deck.filter (· ≠ target) }
  else none

/-- Scoop Up Cyclone: return a Pokémon in play to hand. -/
def scoopUpEffect (gs : GameState) (pokemonName : String) : GameState :=
  { gs with hand := pokemonName :: gs.hand, benchSize := gs.benchSize - 1 }

/-- Life Dew: when the Pokémon this is attached to is KO'd, opponent takes one fewer prize. -/
def lifeDewPrizeReduction (normalPrizes : Nat) : Nat :=
  normalPrizes - 1

/-- G Booster: 200 damage, ignores effects on the Defending Pokémon. -/
def gBoosterDamage : Nat := 200

/-- G Scope: attacks hit the Bench for normal damage. -/
def gScopeBenchHit (attackDamage : Nat) : Nat := attackDamage

/-- Rock Guard: when opponent's Pokémon attacks the Rock Guard holder, do 60 damage back. -/
def rockGuardCounter : Nat := 60

-- ============================================================
-- §5  Effect theorems
-- ============================================================

/-- Theorem 5: Computer Search requires exactly 2 discards. -/
theorem computer_search_needs_two (gs : GameState) (ds : List String) (t : String) :
    ds.length ≠ 2 → computerSearchEffect gs ds t = none := by
  intro h
  simp [computerSearchEffect]
  intro heq
  exact absurd heq h

/-- Theorem 6: Master Ball only finds cards in top 7. -/
theorem master_ball_top_seven (gs : GameState) (t : String)
    (h : t ∉ gs.deck.take 7) : masterBallEffect gs t = none := by
  simp [masterBallEffect, h]

/-- Theorem 7: G Booster always does 200 damage. -/
theorem g_booster_damage_fixed : gBoosterDamage = 200 := rfl

/-- Theorem 8: Rock Guard always counters for 60. -/
theorem rock_guard_counter_fixed : rockGuardCounter = 60 := rfl

/-- Theorem 9: Life Dew reduces prizes by 1. -/
theorem life_dew_reduces (n : Nat) (h : n ≥ 1) :
    lifeDewPrizeReduction n = n - 1 := rfl

/-- Theorem 10: G Scope preserves damage value. -/
theorem g_scope_preserves (dmg : Nat) : gScopeBenchHit dmg = dmg := rfl

-- ============================================================
-- §6  Tool attachment rules for ACE SPEC tools
-- ============================================================

/-- A Pokémon in play with optional tool. -/
structure PokemonInPlay where
  name : String
  hp   : Nat
  tool : Option ACESpecCard
deriving Repr

/-- Can attach a tool-kind ACE SPEC if the Pokémon has no tool. -/
def canAttachACETool (p : PokemonInPlay) (c : ACESpecCard) : Prop :=
  c.kind = .tool ∧ p.tool = none

/-- Attach a tool. -/
def attachACETool (p : PokemonInPlay) (c : ACESpecCard) : PokemonInPlay :=
  { p with tool := some c }

/-- Theorem 11: After attachment, the tool is present. -/
theorem tool_after_attach (p : PokemonInPlay) (c : ACESpecCard) :
    (attachACETool p c).tool = some c := by
  simp [attachACETool]

/-- Theorem 12: Can't attach to a Pokémon that already has a tool. -/
theorem no_double_tool (p : PokemonInPlay) (c₁ c₂ : ACESpecCard)
    (h : p.tool = some c₁) : ¬ canAttachACETool p c₂ := by
  simp [canAttachACETool, h]

/-- Theorem 13: Item ACE SPECs can't be attached as tools. -/
theorem item_not_attachable (p : PokemonInPlay) (c : ACESpecCard)
    (hk : c.kind = .item) : ¬ canAttachACETool p c := by
  simp [canAttachACETool, hk]

-- ============================================================
-- §7  Deck building with ACE SPECs
-- ============================================================

/-- Add a card to a deck. -/
def addCard (d : Deck) (c : DeckCard) : Deck := c :: d

/-- Theorem 14: Adding a regular card to a valid deck keeps it valid. -/
theorem add_regular_preserves_valid (d : Deck) (name : String)
    (hv : aceSpecValid d) : aceSpecValid (addCard d (.regular name)) := by
  simp [addCard, aceSpecValid, aceSpecCount, List.filter] at *
  exact hv

/-- Helper: aceSpecCount of cons with aceSpec. -/
private theorem aceSpecCount_cons_ace (c : ACESpecCard) (d : Deck) :
    aceSpecCount (.aceSpec c :: d) = 1 + aceSpecCount d := by
  simp [aceSpecCount, List.filter, Nat.add_comm]

/-- Helper: aceSpecCount of cons with regular. -/
private theorem aceSpecCount_cons_reg (s : String) (d : Deck) :
    aceSpecCount (.regular s :: d) = aceSpecCount d := by
  simp [aceSpecCount, List.filter]

/-- Theorem 15: Adding an ACE SPEC to a deck with zero ACE SPECs is valid. -/
theorem add_ace_to_zero (d : Deck) (c : ACESpecCard)
    (hz : aceSpecCount d = 0) : aceSpecValid (addCard d (.aceSpec c)) := by
  simp [aceSpecValid, addCard, aceSpecCount_cons_ace, hz]

/-- Theorem 16: Adding an ACE SPEC to a deck that already has one is invalid. -/
theorem add_ace_to_one_invalid (d : Deck) (c : ACESpecCard)
    (ho : aceSpecCount d ≥ 1) : ¬ aceSpecValid (addCard d (.aceSpec c)) := by
  simp [aceSpecValid, addCard, aceSpecCount_cons_ace]
  omega

-- ============================================================
-- §8  Card-specific kind classifications
-- ============================================================

/-- Theorem 17: Computer Search is an item. -/
theorem computer_search_is_item : computerSearch.kind = .item := rfl

/-- Theorem 18: Life Dew is a tool. -/
theorem life_dew_is_tool : lifeDew.kind = .tool := rfl

/-- Theorem 19: G Booster is a tool. -/
theorem g_booster_is_tool : gBooster.kind = .tool := rfl

/-- Theorem 20: Rock Guard is a tool. -/
theorem rock_guard_is_tool : rockGuard.kind = .tool := rfl

/-- Theorem 21: Dowsing Machine is an item. -/
theorem dowsing_machine_is_item : dowsingMachine.kind = .item := rfl

/-- Theorem 22: Master Ball is an item. -/
theorem master_ball_is_item : masterBall.kind = .item := rfl

/-- Theorem 23: All item ACE SPECs are items (batch witness). -/
theorem all_items_are_items :
    computerSearch.kind = .item ∧ dowsingMachine.kind = .item ∧
    masterBall.kind = .item ∧ scoopUpCyclone.kind = .item ∧
    scrambleSwitch.kind = .item ∧ goldPotion.kind = .item :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Theorem 24: All tool ACE SPECs are tools (batch witness). -/
theorem all_tools_are_tools :
    lifeDew.kind = .tool ∧ gBooster.kind = .tool ∧
    gScope.kind = .tool ∧ rockGuard.kind = .tool ∧
    crystalWall.kind = .tool ∧ victoryPiece.kind = .tool :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================
-- §9  ACE SPEC distinctness
-- ============================================================

/-- Theorem 25: Computer Search ≠ Dowsing Machine. -/
theorem cs_ne_dm : computerSearch ≠ dowsingMachine := by decide

/-- Theorem 26: G Booster ≠ G Scope. -/
theorem gb_ne_gs : gBooster ≠ gScope := by decide

/-- Theorem 27: Life Dew ≠ Rock Guard. -/
theorem ld_ne_rg : lifeDew ≠ rockGuard := by decide

/-- Theorem 28: Master Ball ≠ Scoop Up Cyclone. -/
theorem mb_ne_suc : masterBall ≠ scoopUpCyclone := by decide

-- ============================================================
-- §10  Prize and damage interactions
-- ============================================================

/-- Theorem 29: Life Dew on a 2-prize Pokémon yields 1 prize. -/
theorem life_dew_two_to_one : lifeDewPrizeReduction 2 = 1 := rfl

/-- Theorem 30: Life Dew on a 1-prize Pokémon yields 0 prizes. -/
theorem life_dew_one_to_zero : lifeDewPrizeReduction 1 = 0 := rfl

/-- Theorem 31: G Booster KOs anything with ≤ 200 HP. -/
theorem g_booster_kos (hp : Nat) (h : hp ≤ 200) :
    hp ≤ gBoosterDamage := by
  simp [gBoosterDamage]; omega

/-- Theorem 32: Rock Guard + 200 from G Booster = 260 total. -/
theorem rock_guard_plus_g_booster :
    rockGuardCounter + gBoosterDamage = 260 := rfl
