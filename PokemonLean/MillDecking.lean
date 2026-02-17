/-
  PokemonLean / MillDecking.lean

  Covers:
  - aggro mill (Durant, Wailord)
  - control mill (Sableye, Bunnelby)
  - mill win condition (0 cards in deck = lose)
  - force-draw cards (N, Iono)
  - deck thinning
  - mill-vs-aggro matchup analysis

-/

namespace MillDecking

-- ============================================================
-- §2  Core cards and strategy labels
-- ============================================================

inductive MillCard where
  | durant
  | wailord
  | sableye
  | bunnelby
  | cardN
  | iono
  | filler (name : String)
deriving DecidableEq, Repr

def isAggroMillCard : MillCard → Bool
  | .durant => true
  | .wailord => true
  | _ => false

def isControlMillCard : MillCard → Bool
  | .sableye => true
  | .bunnelby => true
  | _ => false

theorem durant_is_aggro : isAggroMillCard .durant = true := rfl
theorem wailord_is_aggro : isAggroMillCard .wailord = true := rfl
theorem sableye_is_control : isControlMillCard .sableye = true := rfl
theorem bunnelby_is_control : isControlMillCard .bunnelby = true := rfl

-- ============================================================
-- §3  Match state and mill win condition
-- ============================================================

structure MatchState where
  millDeck : Nat
  millHand : Nat
  oppDeck : Nat
  oppHand : Nat
  aggroPrizeRate : Nat
  turn : Nat
deriving DecidableEq, Repr

def deckOutLoss (deckCount : Nat) : Prop := deckCount = 0

def opponentLoses (s : MatchState) : Prop := deckOutLoss s.oppDeck

theorem deckout_zero : deckOutLoss 0 := rfl

theorem deckout_succ_false (n : Nat) : ¬ deckOutLoss (n + 1) := by
  simp [deckOutLoss]

theorem opponent_loses_when_zero (s : MatchState) (h : s.oppDeck = 0) :
    opponentLoses s := by
  simpa [opponentLoses, deckOutLoss] using h

-- ============================================================
-- §4  Mill operations
-- ============================================================

def durantMill (s : MatchState) (durants : Nat) : MatchState :=
  { s with oppDeck := s.oppDeck - durants }

def wailordStall (s : MatchState) : MatchState :=
  { s with aggroPrizeRate := s.aggroPrizeRate - 1 }

def sableyeControl (s : MatchState) : MatchState :=
  { s with oppHand := s.oppHand - 1 }

def bunnelbyControl (s : MatchState) : MatchState :=
  { s with oppDeck := s.oppDeck - 1 }

def forceDraw (s : MatchState) (cards : Nat) : MatchState :=
  { s with oppDeck := s.oppDeck - cards, oppHand := s.oppHand + cards }

def playN (s : MatchState) (prizesRemaining : Nat) : MatchState :=
  forceDraw s prizesRemaining

def playIono (s : MatchState) (prizesRemaining : Nat) : MatchState :=
  forceDraw s prizesRemaining

def thinDeck (s : MatchState) (cards : Nat) : MatchState :=
  let moved := min cards s.millDeck
  { s with millDeck := s.millDeck - moved, millHand := s.millHand + moved }

def naturalOppDraw (s : MatchState) : MatchState :=
  { s with oppDeck := s.oppDeck - 1, oppHand := s.oppHand + 1, turn := s.turn + 1 }

theorem durant_nonincreasing (s : MatchState) (d : Nat) :
    (durantMill s d).oppDeck ≤ s.oppDeck :=
  Nat.sub_le _ _

theorem wailord_stall_nonincreasing (s : MatchState) :
    (wailordStall s).aggroPrizeRate ≤ s.aggroPrizeRate :=
  Nat.sub_le _ _

theorem sableye_nonincreasing_hand (s : MatchState) :
    (sableyeControl s).oppHand ≤ s.oppHand :=
  Nat.sub_le _ _

theorem bunnelby_nonincreasing (s : MatchState) :
    (bunnelbyControl s).oppDeck ≤ s.oppDeck :=
  Nat.sub_le _ _

theorem n_forces_draw (s : MatchState) (p : Nat) :
    playN s p = forceDraw s p := rfl

theorem iono_forces_draw (s : MatchState) (p : Nat) :
    playIono s p = forceDraw s p := rfl

theorem n_and_iono_same (s : MatchState) (p : Nat) :
    playN s p = playIono s p := rfl

theorem force_draw_nonincreasing (s : MatchState) (n : Nat) :
    (forceDraw s n).oppDeck ≤ s.oppDeck :=
  Nat.sub_le _ _

theorem thin_zero (s : MatchState) : thinDeck s 0 = s := by
  simp [thinDeck]

theorem thin_deck_nonincreasing (s : MatchState) (cards : Nat) :
    (thinDeck s cards).millDeck ≤ s.millDeck := by
  simp [thinDeck]

theorem thin_deck_increases_hand (s : MatchState) (cards : Nat) :
    s.millHand ≤ (thinDeck s cards).millHand := by
  simp [thinDeck]

theorem natural_draw_turn (s : MatchState) :
    (naturalOppDraw s).turn = s.turn + 1 := rfl

theorem natural_draw_deck (s : MatchState) :
    (naturalOppDraw s).oppDeck = s.oppDeck - 1 := rfl

-- ============================================================
-- §5  Strategy paths (aggro, control, thinning)
-- ============================================================


theorem durant_then_draw_exact_zero (s : MatchState) (d : Nat)
    (h : s.oppDeck = d + 1) :
    (naturalOppDraw (durantMill s d)).oppDeck = 0 := by
  simp [naturalOppDraw, durantMill, h]

-- ============================================================
-- §6  Mill-vs-aggro matchup analysis
-- ============================================================

def totalMillPerTurn (durants forcedDrawCards : Nat) : Nat :=
  1 + durants + forcedDrawCards

def deckAfterTurns (startingDeck millRate turns : Nat) : Nat :=
  startingDeck - millRate * turns

def aggroPrizesAfter (prizeRate turns : Nat) : Nat :=
  prizeRate * turns

def millFavored (startingDeck millRate prizeRate turns : Nat) : Bool :=
  deckAfterTurns startingDeck millRate turns = 0 &&
  aggroPrizesAfter prizeRate turns < 6

theorem four_durant_rate : totalMillPerTurn 4 0 = 5 := rfl

theorem deckout_in_twelve_turns :
    deckAfterTurns 60 (totalMillPerTurn 4 0) 12 = 0 := by
  simp [deckAfterTurns, totalMillPerTurn]

theorem aggro_two_prize_rate :
    aggroPrizesAfter 2 3 = 6 := by
  simp [aggroPrizesAfter]

theorem mill_favored_false_vs_fast_aggro :
    millFavored 60 (totalMillPerTurn 4 0) 2 12 = false := by
  simp [millFavored, deckAfterTurns, totalMillPerTurn, aggroPrizesAfter]

theorem mill_favored_true_vs_slow_aggro :
    millFavored 25 (totalMillPerTurn 4 0) 1 5 = true := by
  simp [millFavored, deckAfterTurns, totalMillPerTurn, aggroPrizesAfter]

end MillDecking
