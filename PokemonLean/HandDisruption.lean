import PokemonLean.Basic

namespace PokemonLean.HandDisruption

open PokemonLean

-- ============================================================================
-- SUPPORTER HAND DISRUPTION TYPES
-- ============================================================================

/-- Supporter cards that disrupt the opponent's hand -/
inductive DisruptionSupporter where
  | judge         -- both players shuffle hand, draw 4
  | marshadow     -- opponent shuffles hand, draws 4
  | marnie        -- self draws 5, opponent draws 4 (bottom of deck)
  | ionoSelf (prizes : Nat)  -- draw cards = prizes remaining (self)
  | ionoOpp (prizes : Nat)   -- opponent draws cards = their prizes remaining
  | nSelf (prizes : Nat)     -- N: draw cards = prizes remaining
  | nOpp (prizes : Nat)
  | acerolasPrivilege  -- draw until 6 cards
  | professorOak       -- discard hand, draw 7
  | copycat (oppHand : Nat)  -- shuffle hand, draw = opponent's hand size
  deriving Repr, BEq, DecidableEq

/-- Cards drawn by a disruption supporter -/
def disruptionDrawCount : DisruptionSupporter → Nat
  | .judge => 4
  | .marshadow => 4
  | .marnie => 5
  | .ionoSelf prizes => prizes
  | .ionoOpp prizes => prizes
  | .nSelf prizes => prizes
  | .nOpp prizes => prizes
  | .acerolasPrivilege => 6
  | .professorOak => 7
  | .copycat oppHand => oppHand

/-- Cards the opponent draws from disruption -/
def opponentDrawCount : DisruptionSupporter → Nat
  | .judge => 4
  | .marshadow => 4
  | .marnie => 4
  | .ionoSelf _ => 0    -- ionoSelf only affects self
  | .ionoOpp prizes => prizes
  | .nSelf _ => 0
  | .nOpp prizes => prizes
  | .acerolasPrivilege => 0
  | .professorOak => 0
  | .copycat _ => 0

-- ============================================================================
-- DRAW COUNT THEOREMS
-- ============================================================================


-- ============================================================================
-- IONO / N PRIZE-BASED MECHANICS
-- ============================================================================

/-- Standard prize count -/
def standardPrizeCount' : Nat := 6

/-- Iono hand size when you have taken k prizes -/
def ionoHandSize (prizesTaken : Nat) : Nat :=
  standardPrizeCount' - prizesTaken

/-- N hand size: prizes remaining -/
def nHandSize (prizesRemaining : Nat) : Nat := prizesRemaining


theorem iono_decreasing (a b : Nat) (h : a ≤ b) (hb : b ≤ standardPrizeCount') :
    ionoHandSize b ≤ ionoHandSize a := by
  simp only [ionoHandSize, standardPrizeCount']; omega

theorem iono_le_six (n : Nat) : ionoHandSize n ≤ 6 := by
  simp only [ionoHandSize, standardPrizeCount']; omega


-- ============================================================================
-- HAND SIZE DISRUPTION ANALYSIS
-- ============================================================================

/-- The disruption impact: how many cards the opponent loses -/
def disruptionImpact (oppHandBefore : Nat) (oppDrawsAfter : Nat) : Int :=
  (oppHandBefore : Int) - (oppDrawsAfter : Int)

/-- Whether a disruption is net negative for the opponent -/
def isNetDisruption (oppHandBefore oppDrawsAfter : Nat) : Bool :=
  decide (oppHandBefore > oppDrawsAfter)

theorem disruption_impact_positive_when_larger (before after : Nat) (h : before > after) :
    disruptionImpact before after > 0 := by
  simp [disruptionImpact]
  omega

theorem disruption_impact_zero_when_equal (n : Nat) :
    disruptionImpact n n = 0 := by
  simp [disruptionImpact]

theorem disruption_impact_negative_when_smaller (before after : Nat) (h : before < after) :
    disruptionImpact before after < 0 := by
  simp [disruptionImpact]
  omega

theorem is_net_disruption_iff (before after : Nat) :
    isNetDisruption before after = true ↔ before > after := by
  simp only [isNetDisruption, decide_eq_true_eq]

-- ============================================================================
-- MARNIE MECHANICS
-- ============================================================================

/-- Marnie: self draws 5, opponent draws 4 (from bottom) -/
def marnieSelfDraw : Nat := 5
def marnieOppDraw : Nat := 4

/-- Marnie is always disruption if opponent has > 4 cards -/
theorem marnie_disrupts_large_hand (oppHand : Nat) (h : oppHand > 4) :
    isNetDisruption oppHand marnieOppDraw = true := by
  simp [isNetDisruption, marnieOppDraw]
  omega

/-- Marnie doesn't disrupt if opponent has ≤ 4 cards -/
theorem marnie_no_disruption_small_hand (oppHand : Nat) (h : oppHand ≤ 4) :
    isNetDisruption oppHand marnieOppDraw = false := by
  simp [isNetDisruption, marnieOppDraw]
  omega

-- Marnie self draw is strictly better than opponent draw

-- ============================================================================
-- JUDGE MECHANICS
-- ============================================================================

def judgeDraw : Nat := 4

-- Judge is symmetric: both draw 4

/-- Judge disrupts if opponent has > 4 cards -/
theorem judge_disrupts_large_hand (oppHand : Nat) (h : oppHand > 4) :
    isNetDisruption oppHand judgeDraw = true := by
  simp [isNetDisruption, judgeDraw]
  omega

/-- Judge doesn't disrupt small hands -/
theorem judge_no_disruption_small_hand (oppHand : Nat) (h : oppHand ≤ 4) :
    isNetDisruption oppHand judgeDraw = false := by
  simp [isNetDisruption, judgeDraw]
  omega

-- ============================================================================
-- N STRATEGY THEOREMS
-- ============================================================================

-- N is best when opponent has few prizes left (lots taken)

/-- N weakens as opponent takes fewer prizes from pool -/
theorem n_weakens_early (a b : Nat) (h : a < b) :
    nHandSize a < nHandSize b := h

-- N to 1 is the strongest disruption

-- N gives 6 at start

-- ============================================================================
-- IONO STRATEGY THEOREMS
-- ============================================================================

-- Iono is strongest when opponent has taken 5 prizes (1 left)

-- Iono is weakest at start of game

/-- Iono + prizes taken determines hand size -/
theorem iono_plus_prizes (taken : Nat) (h : taken ≤ 6) :
    ionoHandSize taken + taken = standardPrizeCount' := by
  simp [ionoHandSize, standardPrizeCount']
  omega

-- ============================================================================
-- DISRUPTION SEQUENCING
-- ============================================================================

/-- Disruption value: combining impact with timing -/
structure DisruptionPlay where
  supporter : DisruptionSupporter
  oppHandBefore : Nat
  oppPrizesRemaining : Nat
  deriving Repr, BEq, DecidableEq

/-- Net cards opponent loses from a disruption play -/
def netCardsLost (dp : DisruptionPlay) : Int :=
  disruptionImpact dp.oppHandBefore (opponentDrawCount dp.supporter)

/-- A play is effective if opponent loses cards -/
def isEffectiveDisruption (dp : DisruptionPlay) : Bool :=
  decide (netCardsLost dp > 0)

theorem effective_iff_net_positive (dp : DisruptionPlay) :
    isEffectiveDisruption dp = true ↔ netCardsLost dp > 0 := by
  simp only [isEffectiveDisruption, decide_eq_true_eq]

-- ============================================================================
-- HAND LOCK STRATEGY
-- ============================================================================

/-- A hand lock reduces opponent to very few options -/
def isHandLock (oppHandAfter : Nat) : Bool :=
  decide (oppHandAfter ≤ 2)

-- Iono to 1 is a hand lock

-- Iono to 2 is a hand lock

-- Iono to 3 is NOT a hand lock

-- N to 1 is a hand lock

-- ============================================================================
-- DECK SHUFFLE INTERACTION
-- ============================================================================

/-- After disruption, opponent's deck gains cards from hand -/
def deckSizeAfterShuffle (deckBefore handBefore drawCount : Nat) : Nat :=
  deckBefore + handBefore - drawCount

/-- The total cards (deck + hand) is preserved -/
theorem total_cards_preserved (deckBefore handBefore drawCount : Nat)
    (h : drawCount ≤ deckBefore + handBefore) :
    deckSizeAfterShuffle deckBefore handBefore drawCount + drawCount =
      deckBefore + handBefore := by
  simp [deckSizeAfterShuffle]
  omega

/-- Disruption doesn't create or destroy cards -/
theorem disruption_card_conservation (deckBefore handBefore deckAfter handAfter : Nat)
    (h : deckBefore + handBefore = deckAfter + handAfter) :
    (deckBefore : Int) - deckAfter = (handAfter : Int) - handBefore := by
  omega

-- ============================================================================
-- MULTI-DISRUPTION ANALYSIS
-- ============================================================================

/-- Cumulative disruption over multiple turns -/
def cumulativeDisruption (impacts : List Int) : Int :=
  impacts.foldl (· + ·) 0


theorem cumulative_singleton (x : Int) : cumulativeDisruption [x] = x := by
  simp [cumulativeDisruption, List.foldl]

/-- Count of disruption supporters in a deck -/
def disruptionCount (judges marnies ionos ns : Nat) : Nat :=
  judges + marnies + ionos + ns

theorem disruption_count_ge_component (j m i n : Nat) :
    disruptionCount j m i n ≥ j := by
  simp [disruptionCount]
  omega

theorem disruption_count_ge_iono (j m i n : Nat) :
    disruptionCount j m i n ≥ i := by
  simp [disruptionCount]
  omega

-- ============================================================================
-- TIMING THEOREMS (when to play disruption)
-- ============================================================================

/-- Disruption is best when opponent has large hand -/
def disruptionTiming (oppHand oppPrizes : Nat) : Nat :=
  (if oppHand > 6 then 3 else if oppHand > 4 then 2 else 0) +
  (if oppPrizes ≤ 2 then 3 else if oppPrizes ≤ 4 then 1 else 0)


theorem timing_nonneg (h p : Nat) : 0 ≤ disruptionTiming h p := Nat.zero_le _

theorem timing_le_six (h p : Nat) : disruptionTiming h p ≤ 6 := by
  unfold disruptionTiming
  by_cases h1 : h > 6
  · simp [h1]
    by_cases h2 : p ≤ 2 <;> simp [h2]
    by_cases h3 : p ≤ 4 <;> simp [h3]
  · simp [h1]
    by_cases h1a : h > 4
    · simp [h1a]
      by_cases h2 : p ≤ 2 <;> simp [h2]
      by_cases h3 : p ≤ 4 <;> simp [h3]
    · simp [h1a]
      by_cases h2 : p ≤ 2 <;> simp [h2]
      by_cases h3 : p ≤ 4 <;> simp [h3]

end PokemonLean.HandDisruption
