/-
  PokemonLean / HandManagement.lean

  Pokémon TCG hand management mechanics formalised via computational paths.
  Covers: draw phase, hand size limits, Supporter/Item/Tool play restrictions,
  hand disruption (N, Judge, Marnie), top-deck effects, hand advantage theory.

  All proofs are sorry-free.  15+ theorems.
-/

-- ============================================================
-- §1  Computational Paths Infrastructure
-- ============================================================

namespace HandManagement

inductive Step (α : Type) : α → α → Type where
  | refl : (a : α) → Step α a a
  | rule : (name : String) → (a b : α) → Step α a b

inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

def Path.trans : Path α a b → Path α b c → Path α a c
  | .nil _,    q => q
  | .cons s p, q => .cons s (p.trans q)

def Path.single (s : Step α a b) : Path α a b :=
  .cons s (.nil _)

def Step.symm : Step α a b → Step α b a
  | .refl a     => .refl a
  | .rule n a b => .rule (n ++ "⁻¹") b a

def Path.symm : Path α a b → Path α b a
  | .nil a    => .nil a
  | .cons s p => p.symm.trans (.cons s.symm (.nil _))

def Path.length : Path α a b → Nat
  | .nil _    => 0
  | .cons _ p => 1 + p.length

theorem path_trans_assoc (p : Path α a b) (q : Path α b c) (r : Path α c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  induction p with
  | nil _ => simp [Path.trans]
  | cons s _ ih => simp [Path.trans, ih]

theorem path_trans_nil_right (p : Path α a b) :
    Path.trans p (.nil b) = p := by
  induction p with
  | nil _ => simp [Path.trans]
  | cons s _ ih => simp [Path.trans, ih]

theorem path_length_trans (p : Path α a b) (q : Path α b c) :
    (Path.trans p q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [Path.trans, Path.length]
  | cons s _ ih => simp [Path.trans, Path.length, ih, Nat.add_assoc]

-- ============================================================
-- §2  Card Types
-- ============================================================

/-- Card categories relevant to hand management. -/
inductive CardKind where
  | pokemon    -- Pokémon card
  | supporter  -- Supporter (one per turn)
  | item       -- Item (free play, multiple per turn)
  | tool       -- Pokémon Tool
  | energy     -- Energy card
deriving DecidableEq, Repr

/-- A card in hand. -/
structure Card where
  name : String
  kind : CardKind
deriving DecidableEq, Repr

-- Example cards
def profResearch : Card := ⟨"Professor's Research", .supporter⟩
def cynthia : Card := ⟨"Cynthia", .supporter⟩
def cardN : Card := ⟨"N", .supporter⟩
def judge : Card := ⟨"Judge", .supporter⟩
def marnie : Card := ⟨"Marnie", .supporter⟩
def ultraBall : Card := ⟨"Ultra Ball", .item⟩
def nestBall : Card := ⟨"Nest Ball", .item⟩
def choiceBelt : Card := ⟨"Choice Belt", .tool⟩

-- ============================================================
-- §3  Hand and Game State
-- ============================================================

/-- The game state relevant to hand management. -/
structure HandState where
  hand : List Card
  deck : List Card
  discard : List Card
  prizes : Nat
  supporterPlayed : Bool
  itemLocked : Bool     -- e.g., Vileplume's Allergy Flower
  turnNumber : Nat
deriving Repr

def HandState.handSize (s : HandState) : Nat := s.hand.length

def HandState.deckSize (s : HandState) : Nat := s.deck.length

/-- Maximum hand size at end of turn (some formats). -/
def maxHandSize : Nat := 7

-- ============================================================
-- §4  Draw Phase
-- ============================================================

/-- Draw one card from deck to hand. -/
def drawOne (s : HandState) : HandState :=
  match s.deck with
  | []     => s
  | c :: rest =>
    { s with hand := s.hand ++ [c], deck := rest }

/-- Draw n cards. -/
def drawN (s : HandState) : Nat → HandState
  | 0     => s
  | n + 1 => drawN (drawOne s) n

/-- Theorem 1: Drawing from empty deck is identity. -/
theorem draw_empty_deck (s : HandState) (h : s.deck = []) :
    drawOne s = s := by
  simp [drawOne, h]

/-- Theorem 2: Drawing one increases hand size by 1 (when deck non-empty). -/
theorem draw_one_hand_size (s : HandState) (c : Card) (rest : List Card)
    (h : s.deck = c :: rest) :
    (drawOne s).handSize = s.handSize + 1 := by
  simp [drawOne, h, HandState.handSize, List.length_append]

/-- Theorem 3: Drawing preserves total card count (hand + deck). -/
theorem draw_preserves_total (s : HandState) (c : Card) (rest : List Card)
    (h : s.deck = c :: rest) :
    (drawOne s).handSize + (drawOne s).deckSize = s.handSize + s.deckSize := by
  simp [drawOne, h, HandState.handSize, HandState.deckSize, List.length_append]
  omega

-- ============================================================
-- §5  Draw Phase Path
-- ============================================================

/-- Path representing the mandatory draw at turn start. -/
def drawPhasePath (s : HandState) (c : Card) (rest : List Card)
    (_ : s.deck = c :: rest) : Path HandState s (drawOne s) :=
  Path.single (Step.rule "draw_for_turn" s (drawOne s))

/-- Multi-draw path (e.g. Professor's Research = draw 7). -/
def multiDrawPath : (s : HandState) → (n : Nat) → Path HandState s (drawN s n)
  | s, 0     => Path.nil s
  | s, n + 1 =>
    let step := Step.rule "draw_card" s (drawOne s)
    (Path.single step).trans (multiDrawPath (drawOne s) n)

/-- Theorem 4: Multi-draw path of 0 has length 0. -/
theorem multi_draw_zero (s : HandState) :
    (multiDrawPath s 0).length = 0 := by
  simp [multiDrawPath, Path.length]

/-- Theorem 5: Multi-draw path of 1 has length 1. -/
theorem multi_draw_one (s : HandState) :
    (multiDrawPath s 1).length = 1 := by
  simp [multiDrawPath, Path.trans, Path.single, Path.length]

-- ============================================================
-- §6  Supporter Play Restrictions
-- ============================================================

/-- Can we play a Supporter? -/
def canPlaySupporter (s : HandState) : Bool :=
  !s.supporterPlayed

/-- Play a Supporter from hand. -/
def playSupporter (s : HandState) (c : Card) (_ : c.kind = .supporter)
    (_ : c ∈ s.hand) (_ : canPlaySupporter s = true) : HandState :=
  { s with
    hand := s.hand.filter (· != c)
    supporterPlayed := true }

/-- Theorem 6: Playing a Supporter sets supporterPlayed to true. -/
theorem supporter_sets_flag (s : HandState) (c : Card) (hk : c.kind = .supporter)
    (hm : c ∈ s.hand) (hc : canPlaySupporter s = true) :
    (playSupporter s c hk hm hc).supporterPlayed = true := by
  simp [playSupporter]

/-- Theorem 7: Playing a Supporter decreases hand size. -/
theorem supporter_decreases_hand (s : HandState) (c : Card) (hk : c.kind = .supporter)
    (hm : c ∈ s.hand) (hc : canPlaySupporter s = true) :
    (playSupporter s c hk hm hc).handSize ≤ s.handSize := by
  simp [playSupporter, HandState.handSize]
  exact List.length_filter_le _ _

-- ============================================================
-- §7  Item Play Restrictions
-- ============================================================

/-- Can we play an Item? -/
def canPlayItem (s : HandState) : Bool :=
  !s.itemLocked

/-- Play an Item from hand. -/
def playItem (s : HandState) (c : Card) (_ : c.kind = .item)
    (_ : c ∈ s.hand) (_ : canPlayItem s = true) : HandState :=
  { s with
    hand := s.hand.filter (· != c)
    discard := c :: s.discard }

/-- Theorem 8: Item lock prevents Item play. -/
theorem item_lock_blocks (s : HandState) (h : s.itemLocked = true) :
    canPlayItem s = false := by
  simp [canPlayItem, h]

-- ============================================================
-- §8  Hand Disruption (N, Judge, Marnie)
-- ============================================================

/-- N effect: each player shuffles hand into deck, draws cards equal to prizes. -/
def applyN (s : HandState) : HandState :=
  { s with
    hand := []
    deck := s.deck ++ s.hand  -- simplified shuffle
    supporterPlayed := true }

/-- After N, hand is empty (before redraw). -/
def applyN_thenDraw (s : HandState) : HandState :=
  drawN (applyN s) s.prizes

/-- Judge effect: both players shuffle hands, draw 4. -/
def applyJudge (s : HandState) : HandState :=
  let shuffled := { s with hand := [], deck := s.deck ++ s.hand, supporterPlayed := true }
  drawN shuffled 4

/-- Marnie effect: opponent puts hand on bottom of deck, draws 4;
    you put hand on bottom, draw 5. -/
def applyMarnie (s : HandState) : HandState :=
  let bottomDecked := { s with hand := [], deck := s.deck ++ s.hand, supporterPlayed := true }
  drawN bottomDecked 5

/-- Theorem 9: After N, hand is initially empty. -/
theorem n_empties_hand (s : HandState) :
    (applyN s).hand = [] := by
  simp [applyN]

/-- Theorem 10: N sets supporterPlayed. -/
theorem n_sets_supporter (s : HandState) :
    (applyN s).supporterPlayed = true := by
  simp [applyN]

/-- Path representing N disruption. -/
def nDisruptionPath (s : HandState) : Path HandState s (applyN s) :=
  let s1 := Step.rule "shuffle_hand_to_deck" s (applyN s)
  Path.single s1

-- ============================================================
-- §9  Hand Disruption Paths (multi-step)
-- ============================================================

/-- Judge disruption as a 2-step path: shuffle then draw 4. -/
def judgeDisruptionPath (s : HandState) : Path HandState s (applyJudge s) :=
  let intermediate := { s with hand := [], deck := s.deck ++ s.hand, supporterPlayed := true }
  let s1 := Step.rule "judge_shuffle" s intermediate
  let s2 := Step.rule "judge_draw_4" intermediate (applyJudge s)
  (Path.single s1).trans (Path.single s2)

/-- Theorem 11: Judge disruption path has length 2. -/
theorem judge_path_length (s : HandState) :
    (judgeDisruptionPath s).length = 2 := by
  simp [judgeDisruptionPath, Path.trans, Path.single, Path.length]

/-- Marnie disruption as a 2-step path: bottom-deck then draw 5. -/
def marnieDisruptionPath (s : HandState) : Path HandState s (applyMarnie s) :=
  let intermediate := { s with hand := [], deck := s.deck ++ s.hand, supporterPlayed := true }
  let s1 := Step.rule "marnie_bottom_deck" s intermediate
  let s2 := Step.rule "marnie_draw_5" intermediate (applyMarnie s)
  (Path.single s1).trans (Path.single s2)

/-- Theorem 12: Marnie disruption path has length 2. -/
theorem marnie_path_length (s : HandState) :
    (marnieDisruptionPath s).length = 2 := by
  simp [marnieDisruptionPath, Path.trans, Path.single, Path.length]

-- ============================================================
-- §10  Top-Deck Effects
-- ============================================================

/-- Peek at top card of deck. -/
def peekTop (s : HandState) : Option Card :=
  s.deck.head?

/-- Top-deck a card from hand (put on top of deck). -/
def topDeck (s : HandState) (c : Card) (_ : c ∈ s.hand) : HandState :=
  { s with
    hand := s.hand.filter (· != c)
    deck := c :: s.deck }

/-- Theorem 13: Top-decking increases deck size. -/
theorem topDeck_increases_deck (s : HandState) (c : Card) (hm : c ∈ s.hand) :
    (topDeck s c hm).deckSize = s.deckSize + 1 := by
  simp [topDeck, HandState.deckSize]

/-- Theorem 14: Top-decked card is on top. -/
theorem topDeck_on_top (s : HandState) (c : Card) (hm : c ∈ s.hand) :
    peekTop (topDeck s c hm) = some c := by
  simp [topDeck, peekTop]

-- ============================================================
-- §11  Hand Advantage Theory
-- ============================================================

/-- Hand advantage = handSize - opponent's hand size (simplified). -/
def handAdvantage (myHand oppHand : Nat) : Int :=
  (myHand : Int) - (oppHand : Int)

/-- Net card advantage from a Supporter. -/
def netCardAdvantage (cardsDrawn cardsDiscarded : Nat) : Int :=
  (cardsDrawn : Int) - (cardsDiscarded : Int) - 1  -- minus 1 for playing the Supporter itself

/-- Theorem 15: Professor's Research net advantage = draw 7 - discard hand - 1. -/
theorem prof_research_advantage (handSize : Nat) :
    netCardAdvantage 7 handSize = 6 - (handSize : Int) := by
  simp [netCardAdvantage]
  omega

/-- Theorem 16: Cynthia (shuffle then draw 6) is always +5 net. -/
theorem cynthia_advantage :
    netCardAdvantage 6 0 = 5 := by
  simp [netCardAdvantage]

-- ============================================================
-- §12  Hand Size Limit Path
-- ============================================================

/-- Discard down to max hand size at end of turn. -/
def discardToLimit (s : HandState) : HandState :=
  if s.handSize ≤ maxHandSize then s
  else { s with
    hand := s.hand.take maxHandSize
    discard := s.discard ++ s.hand.drop maxHandSize }

/-- Theorem 17: After discarding to limit, hand size ≤ max. -/
theorem discard_limit_ok (s : HandState) :
    (discardToLimit s).handSize ≤ maxHandSize := by
  simp [discardToLimit, HandState.handSize, maxHandSize]
  split
  · assumption
  · simp [List.length_take]
    omega

/-- End-of-turn path: discard to limit. -/
def endOfTurnPath (s : HandState) : Path HandState s (discardToLimit s) :=
  Path.single (Step.rule "end_of_turn_discard" s (discardToLimit s))

-- ============================================================
-- §13  Full Turn Hand Management Path
-- ============================================================

/-- A full turn of hand management: draw → play cards → end of turn. -/
def fullTurnPath (s : HandState) :
    Path HandState s s :=
  let s1 := Step.rule "draw_phase" s s
  let s2 := Step.rule "play_phase" s s
  let s3 := Step.rule "end_of_turn" s s
  (Path.single s1).trans ((Path.single s2).trans (Path.single s3))

/-- Theorem 18: Full turn path has 3 steps. -/
theorem full_turn_length (s : HandState) :
    (fullTurnPath s).length = 3 := by
  simp [fullTurnPath, Path.trans, Path.single, Path.length]

/-- Theorem 19: Full turn path reversed also has 3 steps. -/
theorem full_turn_symm_length (s : HandState) :
    (fullTurnPath s).symm.length = 3 := by
  simp [fullTurnPath, Path.symm, Path.trans, Path.single, Path.length, Step.symm]

/-- Theorem 20: Composing two turns gives 6 steps. -/
theorem two_turns_length (s : HandState) :
    ((fullTurnPath s).trans (fullTurnPath s)).length = 6 := by
  rw [path_length_trans]
  simp [full_turn_length]

end HandManagement
