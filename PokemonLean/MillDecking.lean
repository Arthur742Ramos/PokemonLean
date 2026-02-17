/-
  PokemonLean / MillDecking.lean

  Mill / deck-out strategy formalized with computational paths.
  Focus:
  - aggro mill (Durant, Wailord)
  - control mill (Sableye, Bunnelby)
  - mill as win condition (0 cards in deck means loss)
  - force-draw supporters (N, Iono)
  - deck thinning
  - mill-vs-aggro matchup analysis

  Complete proofs with path-native constructions only.
-/

namespace PokemonLean.MillDecking

-- ============================================================
-- §1  Computational paths
-- ============================================================

inductive Step (α : Type) : α → α → Type where
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
  | .rule name a b => .rule (name ++ "_inv") b a

def Path.symm : Path α a b → Path α b a
  | .nil a => .nil a
  | .cons s p => p.symm.trans (Path.single s.symm)

def Path.length : Path α a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

theorem path_trans_assoc (p : Path α a b) (q : Path α b c) (r : Path α c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => rfl
  | cons _ _ ih =>
      simp [Path.trans, ih]

theorem path_trans_nil_right (p : Path α a b) :
    p.trans (.nil b) = p := by
  induction p with
  | nil _ => rfl
  | cons _ _ ih =>
      simp [Path.trans, ih]

theorem path_length_trans (p : Path α a b) (q : Path α b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ =>
      simp [Path.trans, Path.length]
  | cons _ _ ih =>
      simp [Path.trans, Path.length, ih, Nat.add_assoc]

theorem path_symm_length (p : Path α a b) :
    p.symm.length = p.length := by
  induction p with
  | nil _ =>
      rfl
  | cons s p ih =>
      rw [Path.symm, path_length_trans, ih]
      simp [Path.single, Path.length, Nat.add_comm]

-- ============================================================
-- §2  Mill archetypes
-- ============================================================

inductive MillPlan where
  | durantAggro
  | wailordAggro
  | sableyeControl
  | bunnelbyControl
deriving DecidableEq, Repr

def isAggro : MillPlan → Bool
  | .durantAggro  => true
  | .wailordAggro => true
  | _             => false

def isControl : MillPlan → Bool
  | .sableyeControl  => true
  | .bunnelbyControl => true
  | _                => false

theorem durant_is_aggro : isAggro .durantAggro = true := rfl
theorem wailord_is_aggro : isAggro .wailordAggro = true := rfl
theorem sableye_is_control : isControl .sableyeControl = true := rfl
theorem bunnelby_is_control : isControl .bunnelbyControl = true := rfl

-- ============================================================
-- §3  Core state and deck-out win condition
-- ============================================================

structure MillState where
  myDeck    : Nat
  oppDeck   : Nat
  myHand    : Nat
  oppHand   : Nat
  myPrizes  : Nat
  oppPrizes : Nat
  turn      : Nat
deriving DecidableEq, Repr

/-- In this model, having 0 cards in deck means that player loses by deck-out. -/
def deckOutLoss (deckCards : Nat) : Prop :=
  deckCards = 0

theorem zero_cards_loses : deckOutLoss 0 := rfl

theorem positive_cards_not_loses (n : Nat) :
    ¬ deckOutLoss (n + 1) := by
  simp [deckOutLoss]

theorem opp_zero_cards_loses (s : MillState) (h : s.oppDeck = 0) :
    deckOutLoss s.oppDeck := h

-- ============================================================
-- §4  Force-draw cards: N and Iono
-- ============================================================

/-- N: both players draw equal to their prize count (simplified). -/
def playN (s : MillState) : MillState :=
  { s with myHand := s.myPrizes, oppHand := s.oppPrizes }

/-- Iono: both players draw equal to prize count (simplified). -/
def playIono (s : MillState) : MillState :=
  { s with myHand := s.myPrizes, oppHand := s.oppPrizes }

theorem n_sets_opp_hand (s : MillState) :
    (playN s).oppHand = s.oppPrizes := rfl

theorem n_sets_my_hand (s : MillState) :
    (playN s).myHand = s.myPrizes := rfl

theorem iono_sets_opp_hand (s : MillState) :
    (playIono s).oppHand = s.oppPrizes := rfl

theorem iono_sets_my_hand (s : MillState) :
    (playIono s).myHand = s.myPrizes := rfl

theorem n_and_iono_same_model (s : MillState) :
    playN s = playIono s := rfl

-- ============================================================
-- §5  Deck thinning and milling operations
-- ============================================================

def thinDeck (s : MillState) (n : Nat) : MillState :=
  { s with myDeck := s.myDeck - n }

def millOppDeck (s : MillState) (n : Nat) : MillState :=
  { s with oppDeck := s.oppDeck - n }

theorem thin_zero (s : MillState) : thinDeck s 0 = s := by
  cases s <;> simp [thinDeck]

theorem thin_nonincreasing (s : MillState) (n : Nat) :
    (thinDeck s n).myDeck ≤ s.myDeck :=
  Nat.sub_le _ _

theorem thin_all_to_zero (s : MillState) :
    (thinDeck s s.myDeck).myDeck = 0 := by
  simp [thinDeck]

theorem mill_zero (s : MillState) : millOppDeck s 0 = s := by
  cases s <;> simp [millOppDeck]

theorem mill_nonincreasing (s : MillState) (n : Nat) :
    (millOppDeck s n).oppDeck ≤ s.oppDeck :=
  Nat.sub_le _ _

theorem mill_all_decks_out (s : MillState) :
    deckOutLoss (millOppDeck s s.oppDeck).oppDeck := by
  simp [deckOutLoss, millOppDeck]

-- ============================================================
-- §6  Aggro/control mill rates
-- ============================================================

def activeMillRate : MillPlan → Nat
  | .durantAggro    => 4
  | .wailordAggro   => 3
  | .sableyeControl => 2
  | .bunnelbyControl => 2

/-- Natural draw contributes 1 card per turn to deck-out pressure. -/
def totalMillRate (p : MillPlan) : Nat :=
  activeMillRate p + 1

theorem durant_total_rate : totalMillRate .durantAggro = 5 := rfl
theorem wailord_total_rate : totalMillRate .wailordAggro = 4 := rfl
theorem sableye_total_rate : totalMillRate .sableyeControl = 3 := rfl
theorem bunnelby_total_rate : totalMillRate .bunnelbyControl = 3 := rfl

-- ============================================================
-- §7  Turns-to-deck-out and matchup analysis
-- ============================================================

def turnsToDeckOut (deckCards totalRate : Nat) : Nat :=
  if totalRate = 0 then 0 else (deckCards + totalRate - 1) / totalRate

theorem turns_zero_deck (rate : Nat) :
    turnsToDeckOut 0 rate = 0 := by
  cases rate with
  | zero =>
      simp [turnsToDeckOut]
  | succ n =>
      simp [turnsToDeckOut]

theorem durant_deckout_60 :
    turnsToDeckOut 60 (totalMillRate .durantAggro) = 12 := by
  simp [turnsToDeckOut, totalMillRate, activeMillRate]

theorem wailord_deckout_60 :
    turnsToDeckOut 60 (totalMillRate .wailordAggro) = 15 := by
  simp [turnsToDeckOut, totalMillRate, activeMillRate]

theorem control_deckout_60 :
    turnsToDeckOut 60 (totalMillRate .sableyeControl) = 20 := by
  simp [turnsToDeckOut, totalMillRate, activeMillRate]

/-- Simplified aggro clock: aggro takes 14 turns to close game. -/
def aggroClock : Nat := 14

def millFavoredIntoAggro (plan : MillPlan) (oppDeckCards : Nat) : Prop :=
  turnsToDeckOut oppDeckCards (totalMillRate plan) ≤ aggroClock

theorem durant_favored_into_aggro :
    millFavoredIntoAggro .durantAggro 60 := by
  simp [millFavoredIntoAggro, turnsToDeckOut, totalMillRate, activeMillRate, aggroClock]

theorem wailord_not_favored_into_aggro :
    ¬ millFavoredIntoAggro .wailordAggro 60 := by
  simp [millFavoredIntoAggro, turnsToDeckOut, totalMillRate, activeMillRate, aggroClock]

theorem control_not_favored_into_aggro :
    ¬ millFavoredIntoAggro .sableyeControl 60 := by
  simp [millFavoredIntoAggro, turnsToDeckOut, totalMillRate, activeMillRate, aggroClock]

-- ============================================================
-- §8  Strategy lines as computational paths
-- ============================================================

abbrev MillPath := Path MillState

/-- Aggro line: N (force draw) then Durant mill for 2 cards. -/
def nThenMillPath (s : MillState) : MillPath s (millOppDeck (playN s) 2) :=
  (Path.single (Step.rule "N_force_draw" s (playN s))).trans
    (Path.single (Step.rule "Durant_mill_2" (playN s) (millOppDeck (playN s) 2)))

/-- Control line: Iono (force draw) -> Bunnelby thinning -> Sableye mill. -/
def controlLoopPath (s : MillState) :
    MillPath s (millOppDeck (thinDeck (playIono s) 1) 2) :=
  (Path.single (Step.rule "Iono_force_draw" s (playIono s))).trans
    ((Path.single (Step.rule "Bunnelby_thin_1" (playIono s) (thinDeck (playIono s) 1))).trans
      (Path.single
        (Step.rule "Sableye_mill_2"
          (thinDeck (playIono s) 1)
          (millOppDeck (thinDeck (playIono s) 1) 2))))

theorem n_then_mill_length (s : MillState) :
    (nThenMillPath s).length = 2 := by
  simp [nThenMillPath, Path.trans, Path.single, Path.length]

theorem control_loop_length (s : MillState) :
    (controlLoopPath s).length = 3 := by
  simp [controlLoopPath, Path.trans, Path.single, Path.length]

theorem n_then_mill_symm_length (s : MillState) :
    (nThenMillPath s).symm.length = 2 := by
  rw [path_symm_length, n_then_mill_length]

theorem control_loop_roundtrip_length (s : MillState) :
    ((controlLoopPath s).trans (controlLoopPath s).symm).length = 6 := by
  rw [path_length_trans, path_symm_length]
  simp [control_loop_length]

end PokemonLean.MillDecking
