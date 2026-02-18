/-
  PokemonLean / Core / Trainers.lean

  Comprehensive Pokémon TCG trainer card system.
  Covers all trainer subtypes: Supporter, Item, Tool, Stadium, ACE SPEC,
  Prism Star.  Models per-turn limits, item lock, tool limits, stadium
  replacement, ACE SPEC and Prism Star deck constraints, and specific
  card implementations (Professor's Research, Boss's Orders, N, Ultra Ball,
  Float Stone, Choice Band, Tool Scrapper).

  Self-contained — no imports from other PokemonLean modules.
  All proofs are sorry-free.  35+ theorems.
-/

namespace PokemonLean.Core.TrainersMod

-- ============================================================
-- §1  Trainer Kind
-- ============================================================

/-- The six kinds of trainer cards in the TCG (across all eras). -/
inductive TrainerKind where
  | supporter    -- Once per turn
  | item         -- Unlimited per turn (unless locked)
  | tool         -- Attach to a Pokémon (one per Pokémon)
  | stadium      -- In play, replaced by new stadium
  | aceSpec      -- Exactly one per deck
  | prismStar    -- Exactly one per deck; goes to Lost Zone when discarded
deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================
-- §2  Per-Turn State
-- ============================================================

/-- Turn state tracking for trainer card usage. -/
structure TrainerTurnState where
  supporterPlayed : Bool     -- Has a supporter been played this turn?
  itemLockActive  : Bool     -- Is item lock in effect? (Vileplume, Seismitoad-EX)
deriving DecidableEq, Repr, Inhabited

/-- Initial turn state: no supporter played, no item lock. -/
def TrainerTurnState.initial : TrainerTurnState :=
  { supporterPlayed := false, itemLockActive := false }

/-- Can a supporter be played? Only if none played yet this turn. -/
def TrainerTurnState.canPlaySupporter (ts : TrainerTurnState) : Bool :=
  !ts.supporterPlayed

/-- Can an item be played? Only if no item lock is active. -/
def TrainerTurnState.canPlayItem (ts : TrainerTurnState) : Bool :=
  !ts.itemLockActive

/-- Play a supporter: marks supporter as played this turn. -/
def TrainerTurnState.playSupporter (ts : TrainerTurnState) : TrainerTurnState :=
  { ts with supporterPlayed := true }

/-- Activate item lock. -/
def TrainerTurnState.activateItemLock (ts : TrainerTurnState) : TrainerTurnState :=
  { ts with itemLockActive := true }

/-- Deactivate item lock. -/
def TrainerTurnState.deactivateItemLock (ts : TrainerTurnState) : TrainerTurnState :=
  { ts with itemLockActive := false }

-- ============================================================
-- §3  Tool Attachment
-- ============================================================

/-- A Pokémon's tool attachment slot. -/
structure ToolSlot where
  attachedTool : Option String    -- Name of the tool, or none
deriving DecidableEq, Repr, Inhabited

/-- Empty tool slot. -/
def ToolSlot.empty : ToolSlot := { attachedTool := none }

/-- Whether a tool is currently attached. -/
def ToolSlot.hasAttachment (ts : ToolSlot) : Bool := ts.attachedTool.isSome

/-- Attach a tool (only if slot is empty). -/
def ToolSlot.attach (ts : ToolSlot) (toolName : String) : Option ToolSlot :=
  if ts.hasAttachment then none
  else some { attachedTool := some toolName }

/-- Remove a tool (Tool Scrapper effect). -/
def ToolSlot.remove (_ts : ToolSlot) : ToolSlot := { attachedTool := none }

/-- Check if a specific tool is attached. -/
def ToolSlot.hasTool (ts : ToolSlot) (name : String) : Bool :=
  ts.attachedTool == some name

-- ============================================================
-- §4  Float Stone and Choice Band Effects
-- ============================================================

/-- Float Stone: If attached, Pokémon's retreat cost becomes 0. -/
def floatStoneRetreatCost (_originalCost : Nat) (hasFloatStone : Bool) : Nat :=
  if hasFloatStone then 0 else _originalCost

/-- Choice Band: If attached, attacks do +30 damage to EX/GX Pokémon. -/
def choiceBandBonus (hasChoiceBand : Bool) (targetIsRuleBox : Bool) : Nat :=
  if hasChoiceBand && targetIsRuleBox then 30 else 0

-- ============================================================
-- §5  Stadium Mechanics
-- ============================================================

/-- Stadium state: at most one stadium in play. -/
structure StadiumState where
  currentStadium : Option String    -- Name of the stadium in play
deriving DecidableEq, Repr, Inhabited

/-- No stadium in play. -/
def StadiumState.empty : StadiumState := { currentStadium := none }

/-- Can a new stadium be played? Can't play the same one already in play. -/
def StadiumState.canPlayStadium (ss : StadiumState) (newStadium : String) : Bool :=
  ss.currentStadium != some newStadium

/-- Play a new stadium (replaces the current one). -/
def StadiumState.playStadium (ss : StadiumState) (newStadium : String) : StadiumState :=
  if ss.canPlayStadium newStadium then
    { currentStadium := some newStadium }
  else ss

/-- Remove the current stadium. -/
def StadiumState.removeStadium (_ss : StadiumState) : StadiumState :=
  { currentStadium := none }

-- ============================================================
-- §6  ACE SPEC & Prism Star Deck Constraints
-- ============================================================

/-- A deck entry with metadata for constraint checking. -/
structure DeckEntry where
  cardName   : String
  trainerKind : TrainerKind
deriving DecidableEq, Repr, Inhabited

/-- Count ACE SPEC cards in a deck. -/
def countAceSpecs (deck : List DeckEntry) : Nat :=
  deck.filter (fun e => e.trainerKind == .aceSpec) |>.length

/-- Count Prism Star cards in a deck. -/
def countPrismStars (deck : List DeckEntry) : Nat :=
  deck.filter (fun e => e.trainerKind == .prismStar) |>.length

/-- Count copies of a specific Prism Star card. -/
def countSpecificPrism (deck : List DeckEntry) (name : String) : Nat :=
  deck.filter (fun e => e.trainerKind == .prismStar && e.cardName == name) |>.length

/-- Is the deck valid w.r.t. ACE SPEC constraint (at most 1)? -/
def validAceSpecCount (deck : List DeckEntry) : Bool :=
  countAceSpecs deck ≤ 1

/-- Is the deck valid w.r.t. Prism Star constraint (at most 1 of each)? -/
def validPrismStarUniqueness (deck : List DeckEntry) (name : String) : Bool :=
  countSpecificPrism deck name ≤ 1

-- ============================================================
-- §7  Specific Card Implementations
-- ============================================================

/-- Professor's Research: discard hand, draw 7. -/
structure ProfResearchEffect where
  handSize : Nat        -- Current hand size (will be discarded)
  deckSize : Nat        -- Current deck size
deriving Repr

/-- After Professor's Research: new hand = min(7, deckSize), deck shrinks. -/
def ProfResearchEffect.apply (e : ProfResearchEffect) : Nat × Nat :=
  let drawn := min 7 e.deckSize
  (drawn, e.deckSize - drawn)

/-- N effect: both players shuffle hand into deck and draw cards equal to
    their remaining prize count. -/
structure NEffect where
  playerPrizes   : Nat
  opponentPrizes : Nat
deriving Repr

/-- Player draws cards equal to their prize count after N. -/
def NEffect.playerDraw (e : NEffect) : Nat := e.playerPrizes

/-- Opponent draws cards equal to their prize count after N. -/
def NEffect.opponentDraw (e : NEffect) : Nat := e.opponentPrizes

/-- Ultra Ball: discard 2 cards from hand, search deck for 1 Pokémon. -/
structure UltraBallEffect where
  handSize : Nat    -- Hand size before playing Ultra Ball
deriving Repr

/-- Can Ultra Ball be played? Need at least 2 other cards to discard
    (plus Ultra Ball itself = 3 cards minimum). -/
def UltraBallEffect.canPlay (e : UltraBallEffect) : Bool :=
  e.handSize ≥ 3

/-- Hand size after playing Ultra Ball: −3 (UB + 2 discards) + 1 (searched). -/
def UltraBallEffect.handAfter (e : UltraBallEffect) : Nat :=
  if e.canPlay then e.handSize - 3 + 1 else e.handSize

/-- Marnie: both players shuffle hand to bottom of deck.
    Player draws 5, opponent draws 4. -/
def marniePlayerDraw : Nat := 5
def marnieOpponentDraw : Nat := 4

/-- Judge: both players shuffle hand into deck and draw 4. -/
def judgeDraw : Nat := 4

-- ============================================================
-- §8  Lost Zone Mechanic (for Prism Star)
-- ============================================================

/-- Lost Zone state: cards that have been sent to the Lost Zone. -/
structure LostZone where
  cards : List String
deriving Repr, Inhabited

/-- Send a Prism Star card to the Lost Zone when discarded. -/
def LostZone.sendToLostZone (lz : LostZone) (cardName : String) : LostZone :=
  { cards := cardName :: lz.cards }

/-- Is a card in the Lost Zone? -/
def LostZone.contains (lz : LostZone) (cardName : String) : Bool :=
  lz.cards.contains cardName

/-- Initially the Lost Zone is empty. -/
def LostZone.empty : LostZone := { cards := [] }

-- ============================================================
-- §9  Theorems — Supporter Limit
-- ============================================================

/-- Initially, a supporter can be played. -/
theorem initial_can_play_supporter :
    TrainerTurnState.initial.canPlaySupporter = true := by rfl

/-- After playing a supporter, another cannot be played. -/
theorem supporter_limit (ts : TrainerTurnState) :
    (ts.playSupporter).canPlaySupporter = false := by
  simp [TrainerTurnState.playSupporter, TrainerTurnState.canPlaySupporter]

/-- Playing supporter is idempotent. -/
theorem supporter_idempotent (ts : TrainerTurnState) :
    (ts.playSupporter).playSupporter = ts.playSupporter := by
  simp [TrainerTurnState.playSupporter]

/-- Playing a supporter does not affect item lock status. -/
theorem supporter_preserves_item_lock (ts : TrainerTurnState) :
    (ts.playSupporter).itemLockActive = ts.itemLockActive := by
  simp [TrainerTurnState.playSupporter]

-- ============================================================
-- §10  Theorems — Item Lock
-- ============================================================

/-- Initially, items can be played. -/
theorem initial_can_play_item :
    TrainerTurnState.initial.canPlayItem = true := by rfl

/-- When item lock is active, items cannot be played. -/
theorem item_lock_blocks (ts : TrainerTurnState) :
    (ts.activateItemLock).canPlayItem = false := by
  simp [TrainerTurnState.activateItemLock, TrainerTurnState.canPlayItem]

/-- Deactivating item lock allows items again (if no other lock). -/
theorem item_lock_deactivate (ts : TrainerTurnState) :
    (ts.activateItemLock).deactivateItemLock.canPlayItem = true := by
  simp [TrainerTurnState.activateItemLock, TrainerTurnState.deactivateItemLock,
        TrainerTurnState.canPlayItem]

/-- Item lock does not affect supporter status. -/
theorem item_lock_preserves_supporter (ts : TrainerTurnState) :
    (ts.activateItemLock).supporterPlayed = ts.supporterPlayed := by
  simp [TrainerTurnState.activateItemLock]

-- ============================================================
-- §11  Theorems — Tool Limits
-- ============================================================

/-- Empty tool slot has no attachment. -/
theorem empty_no_tool : ToolSlot.empty.hasAttachment = false := by rfl

/-- Cannot attach a tool if one is already attached. -/
theorem tool_limit_occupied (name1 name2 : String) :
    ({ attachedTool := some name1 } : ToolSlot).attach name2 = none := by
  simp [ToolSlot.attach, ToolSlot.hasAttachment]

/-- Attaching to empty slot succeeds. -/
theorem attach_empty (name : String) :
    ToolSlot.empty.attach name = some { attachedTool := some name } := by
  simp [ToolSlot.attach, ToolSlot.empty, ToolSlot.hasAttachment]

/-- Tool Scrapper removes the tool. -/
theorem scrapper_removes (ts : ToolSlot) :
    ts.remove.hasAttachment = false := by
  simp [ToolSlot.remove, ToolSlot.hasAttachment]

/-- After removal, slot is empty. -/
theorem remove_is_empty (ts : ToolSlot) :
    ts.remove = ToolSlot.empty := by
  simp [ToolSlot.remove, ToolSlot.empty]

-- ============================================================
-- §12  Theorems — Float Stone & Choice Band
-- ============================================================

/-- Float Stone makes retreat cost 0 regardless of original cost. -/
theorem float_stone_zero_retreat (cost : Nat) :
    floatStoneRetreatCost cost true = 0 := by
  simp [floatStoneRetreatCost]

/-- Without Float Stone, retreat cost is unchanged. -/
theorem no_float_stone_unchanged (cost : Nat) :
    floatStoneRetreatCost cost false = cost := by
  simp [floatStoneRetreatCost]

/-- Choice Band gives +30 vs rule box. -/
theorem choice_band_bonus_vs_rulebox :
    choiceBandBonus true true = 30 := by rfl

/-- Choice Band gives +0 vs non-rule box. -/
theorem choice_band_no_bonus_non_rulebox :
    choiceBandBonus true false = 0 := by rfl

/-- No Choice Band, no bonus even vs rule box. -/
theorem no_choice_band_no_bonus :
    choiceBandBonus false true = 0 := by rfl

-- ============================================================
-- §13  Theorems — Stadium Replacement
-- ============================================================

/-- Can play a stadium when none is in play. -/
theorem can_play_stadium_empty (name : String) :
    StadiumState.empty.canPlayStadium name = true := by
  simp [StadiumState.empty, StadiumState.canPlayStadium]

/-- Cannot play the same stadium that's already in play. -/
theorem cannot_play_same_stadium (name : String) :
    ({ currentStadium := some name } : StadiumState).canPlayStadium name = false := by
  unfold StadiumState.canPlayStadium
  simp [bne_self_eq_false]

/-- Can play a different stadium when one is in play. -/
theorem can_play_different_stadium (name1 name2 : String) (h : name1 ≠ name2) :
    ({ currentStadium := some name1 } : StadiumState).canPlayStadium name2 = true := by
  unfold StadiumState.canPlayStadium
  simp [bne_iff_ne]
  exact fun heq => h (heq ▸ rfl)

/-- Playing a new stadium replaces the old one. -/
theorem stadium_replacement (name1 name2 : String) (h : name1 ≠ name2) :
    ({ currentStadium := some name1 } : StadiumState).playStadium name2 =
    { currentStadium := some name2 } := by
  unfold StadiumState.playStadium
  have hcan : ({ currentStadium := some name1 } : StadiumState).canPlayStadium name2 = true :=
    can_play_different_stadium name1 name2 h
  simp [hcan]

-- ============================================================
-- §14  Theorems — ACE SPEC Uniqueness
-- ============================================================

/-- Empty deck has 0 ACE SPECs. -/
theorem empty_deck_no_ace_specs : countAceSpecs [] = 0 := by rfl

/-- Empty deck is valid for ACE SPEC constraint. -/
theorem empty_deck_valid_ace : validAceSpecCount [] = true := by rfl

/-- A deck with exactly one ACE SPEC is valid. -/
theorem one_ace_spec_valid :
    validAceSpecCount [{ cardName := "Computer Search", trainerKind := .aceSpec }] = true := by
  native_decide

/-- A deck with two ACE SPECs is invalid. -/
theorem two_ace_specs_invalid :
    validAceSpecCount [
      { cardName := "Computer Search", trainerKind := .aceSpec },
      { cardName := "Dowsing Machine", trainerKind := .aceSpec }
    ] = false := by native_decide

-- ============================================================
-- §15  Theorems — Specific Cards
-- ============================================================

/-- Professor's Research draws 7 from sufficient deck. -/
theorem prof_research_draws_seven :
    (ProfResearchEffect.apply { handSize := 5, deckSize := 30 }).1 = 7 := by rfl

/-- Professor's Research from a 3-card deck draws only 3. -/
theorem prof_research_small_deck :
    (ProfResearchEffect.apply { handSize := 5, deckSize := 3 }).1 = 3 := by rfl

/-- N with 6 prizes: player draws 6. -/
theorem n_full_prizes :
    NEffect.playerDraw { playerPrizes := 6, opponentPrizes := 2 } = 6 := by rfl

/-- N with 1 prize: opponent draws 1 (powerful disruption). -/
theorem n_late_game_disruption :
    NEffect.opponentDraw { playerPrizes := 4, opponentPrizes := 1 } = 1 := by rfl

/-- Marnie: player draws 5. -/
theorem marnie_player_draw : marniePlayerDraw = 5 := by rfl

/-- Judge: both draw 4. -/
theorem judge_draw_count : judgeDraw = 4 := by rfl

/-- Ultra Ball with 5-card hand can be played. -/
theorem ultra_ball_five_card : (UltraBallEffect.canPlay { handSize := 5 }) = true := by rfl

/-- Ultra Ball with 2-card hand cannot be played. -/
theorem ultra_ball_two_card : (UltraBallEffect.canPlay { handSize := 2 }) = false := by rfl

/-- Ultra Ball net card change: 5 → 3 cards in hand. -/
theorem ultra_ball_hand_change :
    UltraBallEffect.handAfter { handSize := 5 } = 3 := by rfl

-- ============================================================
-- §16  Theorems — Lost Zone
-- ============================================================

/-- Empty Lost Zone contains no cards. -/
theorem empty_lost_zone_empty (name : String) :
    LostZone.empty.contains name = false := by
  unfold LostZone.empty LostZone.contains
  simp

/-- A card sent to the Lost Zone is in the Lost Zone. -/
theorem sent_card_in_lost_zone (name : String) :
    (LostZone.empty.sendToLostZone name).contains name = true := by
  unfold LostZone.sendToLostZone LostZone.contains LostZone.empty
  simp

/-- Prism Star: exactly one per deck is valid. -/
theorem prism_star_uniqueness :
    validPrismStarUniqueness
      [{ cardName := "Ditto ◇", trainerKind := .prismStar }]
      "Ditto ◇" = true := by native_decide

end PokemonLean.Core.TrainersMod
