/-
  PokemonLean / MillDecking.lean

  Mill / deck-out strategy in the Pokémon TCG:
  Aggro mill (Durant, Wailord), control mill (Sableye/Bunnelby),
  mill as win condition (0 cards in deck = lose), cards that force
  draw (N, Iono), deck thinning, mill-vs-aggro matchup analysis.

  All proofs are sorry-free.  24 theorems.
-/

set_option linter.unusedVariables false

-- ============================================================
-- §1  Core types
-- ============================================================

namespace MillDecking

/-- Card category. -/
inductive CardCat where
  | pokemon  | trainer | energy
  deriving DecidableEq, Repr

/-- A card in the deck. -/
structure Card where
  name     : String
  cat      : CardCat
  deriving DecidableEq, Repr

/-- Game zone sizes for mill tracking. -/
structure GameState where
  deckSize      : Nat
  handSize      : Nat
  discardSize   : Nat
  prizeCards    : Nat
  deriving DecidableEq, Repr

-- ============================================================
-- §2  Win / loss conditions
-- ============================================================

def isDeckOut (gs : GameState) : Bool := gs.deckSize == 0

def millWin (opponentState : GameState) : Bool := isDeckOut opponentState

-- ============================================================
-- §3  Mill actions as rewrite steps
-- ============================================================

/-- Mill action: a single game action that changes the game state. -/
inductive MillAction : GameState → GameState → Prop where
  | drawCard (d h di p : Nat) (hd : d > 0) :
      MillAction ⟨d, h, di, p⟩ ⟨d - 1, h + 1, di, p⟩
  | millCards (d h di p n : Nat) (hd : d ≥ n) :
      MillAction ⟨d, h, di, p⟩ ⟨d - n, h, di + n, p⟩
  | discardHand (d h di p : Nat) :
      MillAction ⟨d, h, di, p⟩ ⟨d, 0, di + h, p⟩
  | shuffleNDraw (d h di p n : Nat) (hd : d + h ≥ n) :
      MillAction ⟨d, h, di, p⟩ ⟨d + h - n, n, di, p⟩
  | thinDeck (d h di p n : Nat) (hd : d ≥ n) :
      MillAction ⟨d, h, di, p⟩ ⟨d - n, h + n, di, p⟩
  | takePrize (d h di p : Nat) (hp : p > 0) :
      MillAction ⟨d, h, di, p⟩ ⟨d, h + 1, di, p - 1⟩

/-- Multi-step mill path. -/
inductive MillPath : GameState → GameState → Prop where
  | refl  (s : GameState) : MillPath s s
  | step  {s₁ s₂ s₃ : GameState} :
      MillAction s₁ s₂ → MillPath s₂ s₃ → MillPath s₁ s₃

-- ============================================================
-- §4  Path combinators
-- ============================================================

/-- Theorem 1: Transitivity of mill paths. -/
theorem MillPath.trans {a b c : GameState}
    (p : MillPath a b) (q : MillPath b c) : MillPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact MillPath.step s (ih q)

/-- Theorem 2: Single action as path. -/
theorem MillPath.single {a b : GameState} (s : MillAction a b) : MillPath a b :=
  MillPath.step s (MillPath.refl _)

/-- Theorem 3: Append action to path. -/
theorem MillPath.append {a b c : GameState}
    (p : MillPath a b) (s : MillAction b c) : MillPath a c :=
  MillPath.trans p (MillPath.single s)

-- ============================================================
-- §5  Mill strategy types
-- ============================================================

/-- Mill strategy archetype. -/
inductive MillStrategy where
  | aggroMill    -- Durant-style: mill many cards per turn
  | controlMill  -- Sableye/Bunnelby: mill slowly, control board
  | lockMill     -- Wailord-style: tank damage, opponent decks out naturally
  deriving DecidableEq, Repr

/-- Cards per turn milled by strategy. -/
def cardsPerTurn : MillStrategy → Nat
  | .aggroMill   => 4
  | .controlMill => 1
  | .lockMill    => 0

-- ============================================================
-- §6  Core mill theorems
-- ============================================================

/-- Theorem 4: Deck-out check is correct at 0. -/
theorem deckout_at_zero : isDeckOut ⟨0, 7, 0, 6⟩ = true := rfl

/-- Theorem 5: Non-empty deck is not deck-out. -/
theorem no_deckout_one : isDeckOut ⟨1, 7, 0, 6⟩ = false := rfl

/-- Theorem 6: Mill win when opponent has 0 cards. -/
theorem mill_wins_at_zero : millWin ⟨0, 5, 30, 4⟩ = true := rfl

/-- Theorem 7: Drawing from a 1-card deck leads to deck-out state. -/
theorem draw_to_deckout :
    MillAction ⟨1, 6, 0, 6⟩ ⟨0, 7, 0, 6⟩ :=
  MillAction.drawCard 1 6 0 6 (by omega)

/-- Theorem 8: Milling 4 cards (Durant) from a 4-card deck to deck-out. -/
theorem durant_finish :
    MillPath ⟨4, 7, 46, 6⟩ ⟨0, 7, 50, 6⟩ :=
  MillPath.single (MillAction.millCards 4 7 46 6 4 (by omega))

/-- Theorem 9: Aggro mill strategy: Durant mills 4 per turn. -/
theorem durant_rate : cardsPerTurn .aggroMill = 4 := rfl

/-- Theorem 10: Control mill rate. -/
theorem bunnelby_rate : cardsPerTurn .controlMill = 1 := rfl

-- ============================================================
-- §7  Disruption: N / Iono paths
-- ============================================================

/-- Theorem 11: Iono with 1 prize: opponent draws only 1 card. -/
theorem iono_late_game :
    MillAction ⟨20, 5, 20, 1⟩ ⟨24, 1, 20, 1⟩ :=
  MillAction.shuffleNDraw 20 5 20 1 1 (by omega)

/-- Theorem 12: N early game: opponent shuffles hand, draws 6. -/
theorem n_early_game :
    MillAction ⟨40, 7, 0, 6⟩ ⟨41, 6, 0, 6⟩ :=
  MillAction.shuffleNDraw 40 7 0 6 6 (by omega)

-- ============================================================
-- §8  Deck thinning analysis
-- ============================================================

/-- Theorem 13: Deck thinning (Ultra Ball search) reduces deck by 1. -/
theorem ultra_ball_thin :
    MillAction ⟨50, 6, 0, 6⟩ ⟨49, 7, 0, 6⟩ :=
  MillAction.thinDeck 50 6 0 6 1 (by omega)

/-- Theorem 14: Multiple thinning steps path. -/
theorem double_thin :
    MillPath ⟨50, 6, 0, 6⟩ ⟨48, 8, 0, 6⟩ :=
  MillPath.trans
    (MillPath.single (MillAction.thinDeck 50 6 0 6 1 (by omega)))
    (MillPath.single (MillAction.thinDeck 49 7 0 6 1 (by omega)))

-- ============================================================
-- §9  Mill vs aggro matchup
-- ============================================================

/-- Matchup result. -/
structure MatchupResult where
  millTurns  : Nat
  aggroTurns : Nat
  millFavored : Bool
  deriving DecidableEq, Repr

def analyzeMatchup (millRate : Nat) (oppDeck : Nat) (aggroSpeed : Nat) : MatchupResult :=
  let mt := if millRate == 0 then oppDeck else (oppDeck + millRate - 1) / millRate
  ⟨mt, aggroSpeed, decide (mt < aggroSpeed)⟩

/-- Theorem 15: Durant (4/turn) vs slow aggro (12 turns): mill favored. -/
theorem durant_vs_slow_aggro :
    (analyzeMatchup 4 40 12).millFavored = true := by native_decide

/-- Theorem 16: Control mill (1/turn) vs fast aggro (4 turns): not favored. -/
theorem control_vs_fast_aggro :
    (analyzeMatchup 1 40 4).millFavored = false := by native_decide

-- ============================================================
-- §10  Full game path examples
-- ============================================================

/-- Theorem 17: Full mill game: 10 cards left, mill 4+4+2 to deck-out. -/
theorem full_mill_10 :
    MillPath ⟨10, 7, 40, 6⟩ ⟨0, 7, 50, 6⟩ :=
  MillPath.trans
    (MillPath.single (MillAction.millCards 10 7 40 6 4 (by omega)))
    (MillPath.trans
      (MillPath.single (MillAction.millCards 6 7 44 6 4 (by omega)))
      (MillPath.single (MillAction.millCards 2 7 48 6 2 (by omega))))

/-- Theorem 18: Discard hand then mill: control strategy path. -/
theorem control_discard_then_mill :
    MillPath ⟨20, 5, 20, 4⟩ ⟨19, 0, 26, 4⟩ :=
  MillPath.trans
    (MillPath.single (MillAction.discardHand 20 5 20 4))
    (MillPath.single (MillAction.millCards 20 0 25 4 1 (by omega)))

/-- Theorem 19: Prize take does not change deck size. -/
theorem prize_preserves_deck (d h di p : Nat) (hp : p > 0) :
    GameState.deckSize ⟨d, h + 1, di, p - 1⟩ = d := rfl

-- ============================================================
-- §11  Card resource conservation
-- ============================================================

def totalCards (gs : GameState) : Nat :=
  gs.deckSize + gs.handSize + gs.discardSize

/-- Theorem 20: Drawing conserves total cards. -/
theorem draw_conserves (d h di p : Nat) (hd : d > 0) :
    totalCards ⟨d - 1, h + 1, di, p⟩ = totalCards ⟨d, h, di, p⟩ := by
  simp [totalCards]; omega

/-- Theorem 21: Milling conserves total cards. -/
theorem mill_conserves (d h di p n : Nat) (hd : d ≥ n) :
    totalCards ⟨d - n, h, di + n, p⟩ = totalCards ⟨d, h, di, p⟩ := by
  simp [totalCards]; omega

/-- Theorem 22: Discarding hand conserves total cards. -/
theorem discard_conserves (d h di p : Nat) :
    totalCards ⟨d, 0, di + h, p⟩ = totalCards ⟨d, h, di, p⟩ := by
  simp [totalCards]; omega

/-- Theorem 23: Deck thinning conserves total cards. -/
theorem thin_conserves (d h di p n : Nat) (hd : d ≥ n) :
    totalCards ⟨d - n, h + n, di, p⟩ = totalCards ⟨d, h, di, p⟩ := by
  simp [totalCards]; omega

/-- Theorem 24: Shuffle-draw conserves total cards. -/
theorem shuffle_conserves (d h di p n : Nat) (hd : d + h ≥ n) :
    totalCards ⟨d + h - n, n, di, p⟩ = totalCards ⟨d, h, di, p⟩ := by
  simp [totalCards]; omega

end MillDecking
