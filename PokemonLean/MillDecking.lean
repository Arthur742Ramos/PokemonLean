/-
  PokemonLean / MillDecking.lean

  Mill / deck-out strategy formalised via computational paths.
  Covers:
  - aggro mill (Durant, Wailord)
  - control mill (Sableye, Bunnelby)
  - mill win condition (0 cards in deck = lose)
  - force-draw cards (N, Iono)
  - deck thinning
  - mill-vs-aggro matchup analysis

  All proofs are sorry-free.  15+ theorems.
-/

namespace MillDecking

-- ============================================================
-- §1  Computational paths infrastructure
-- ============================================================

inductive Step (α : Type) : α → α → Type where
  | refl : (a : α) → Step α a a
  | rule : (name : String) → (a b : α) → Step α a b

inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

def Path.trans : Path α a b → Path α b c → Path α a c
  | .nil _, q => q
  | .cons s p, q => .cons s (p.trans q)

def Path.single (s : Step α a b) : Path α a b :=
  .cons s (.nil _)

def Step.symm : Step α a b → Step α b a
  | .refl a => .refl a
  | .rule n a b => .rule n b a

def Path.symm : Path α a b → Path α b a
  | .nil a => .nil a
  | .cons s p => p.symm.trans (.cons s.symm (.nil _))

def Path.length : Path α a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

theorem step_symm_symm (s : Step α a b) : s.symm.symm = s := by
  cases s <;> rfl

theorem path_trans_assoc (p : Path α a b) (q : Path α b c) (r : Path α c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  induction p with
  | nil _ => simp [Path.trans]
  | cons s p ih => simp [Path.trans, ih]

theorem path_trans_nil_right (p : Path α a b) :
    Path.trans p (.nil b) = p := by
  induction p with
  | nil _ => simp [Path.trans]
  | cons s p ih => simp [Path.trans, ih]

theorem path_length_trans (p : Path α a b) (q : Path α b c) :
    (Path.trans p q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [Path.trans, Path.length]
  | cons s p ih => simp [Path.trans, Path.length, ih, Nat.add_assoc]

theorem path_single_length (s : Step α a b) :
    (Path.single s).length = 1 := rfl

theorem path_length_symm (p : Path α a b) :
    p.symm.length = p.length := by
  induction p with
  | nil _ => simp [Path.symm, Path.length]
  | cons s p ih =>
      simp [Path.symm, Path.length, path_length_trans, ih, Nat.add_comm]

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

def stepDurant (s : MatchState) (d : Nat) :
    Step MatchState s (durantMill s d) :=
  Step.rule "durant_devour" s (durantMill s d)

def stepWailord (s : MatchState) :
    Step MatchState s (wailordStall s) :=
  Step.rule "wailord_stall" s (wailordStall s)

def stepSableye (s : MatchState) :
    Step MatchState s (sableyeControl s) :=
  Step.rule "sableye_control" s (sableyeControl s)

def stepBunnelby (s : MatchState) :
    Step MatchState s (bunnelbyControl s) :=
  Step.rule "bunnelby_burrow" s (bunnelbyControl s)

def stepN (s : MatchState) (p : Nat) :
    Step MatchState s (playN s p) :=
  Step.rule "play_N" s (playN s p)

def stepIono (s : MatchState) (p : Nat) :
    Step MatchState s (playIono s p) :=
  Step.rule "play_Iono" s (playIono s p)

def stepThin (s : MatchState) (n : Nat) :
    Step MatchState s (thinDeck s n) :=
  Step.rule "thin_deck" s (thinDeck s n)

def stepNatural (s : MatchState) :
    Step MatchState s (naturalOppDraw s) :=
  Step.rule "opp_draw_for_turn" s (naturalOppDraw s)

def aggroMillTurnPath (s : MatchState) (d : Nat) :
    Path MatchState s (naturalOppDraw (durantMill s d)) :=
  (Path.single (stepDurant s d)).trans
    (Path.single (stepNatural (durantMill s d)))

def controlMillTurnPath (s : MatchState) (p : Nat) :
    Path MatchState s (bunnelbyControl (playIono (sableyeControl s) p)) :=
  ((Path.single (stepSableye s)).trans
    (Path.single (stepIono (sableyeControl s) p))).trans
      (Path.single (stepBunnelby (playIono (sableyeControl s) p)))

def thinningSetupPath (s : MatchState) (n : Nat) :
    Path MatchState s (durantMill (thinDeck s n) 1) :=
  (Path.single (stepThin s n)).trans
    (Path.single (stepDurant (thinDeck s n) 1))

theorem aggro_turn_path_length (s : MatchState) (d : Nat) :
    (aggroMillTurnPath s d).length = 2 := by
  simp [aggroMillTurnPath, Path.trans, Path.single, Path.length]

theorem control_turn_path_length (s : MatchState) (p : Nat) :
    (controlMillTurnPath s p).length = 3 := by
  simp [controlMillTurnPath, Path.trans, Path.single, Path.length]

theorem thinning_setup_length (s : MatchState) (n : Nat) :
    (thinningSetupPath s n).length = 2 := by
  simp [thinningSetupPath, Path.trans, Path.single, Path.length]

theorem aggro_turn_symm_length (s : MatchState) (d : Nat) :
    (aggroMillTurnPath s d).symm.length = 2 := by
  rw [path_length_symm]
  exact aggro_turn_path_length s d

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
