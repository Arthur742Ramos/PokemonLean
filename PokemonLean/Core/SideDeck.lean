/-
  PokemonLean / Core / SideDeck.lean

  Tech card analysis for Best-of-3 (Bo3) formats in Pokémon TCG.
  ===============================================================

  Models:
    - Tech card slots and consistency costs
    - Simplified hypergeometric draw probability (Nat-scaled)
    - Monotonicity: more copies ⟹ higher draw probability
    - Specific tech cards: Temple of Sinnoh, Path to the Peak, Drapion V
    - Matchup-specific tech effectiveness
    - Side-boarding strategy modeling

  Self-contained — no imports beyond Lean's core.
  All proofs are sorry-free.  25+ theorems.
-/

set_option linter.unusedVariables false

namespace PokemonLean.Core.SideDeck

-- ============================================================
-- §1  Deck & draw parameters
-- ============================================================

/-- Standard deck size in Pokémon TCG. -/
def deckSize : Nat := 60

/-- Standard opening hand size. -/
def handSize : Nat := 7

/-- Maximum copies of a non-basic-energy card. -/
def maxCopies : Nat := 4

-- [T1]
theorem deck_gt_hand : deckSize > handSize := by native_decide

-- [T2]
theorem max_copies_le_deck : maxCopies ≤ deckSize := by native_decide

-- [T3]
theorem hand_positive : handSize > 0 := by native_decide

-- ============================================================
-- §2  Simplified draw probability
-- ============================================================

/--
  Simplified probability of drawing at least one copy of a card
  in a 7-card hand from a 60-card deck, scaled to [0, 10000]
  (basis points: 10000 = 100%).

  P(at least 1) ≈ 1 - ((60-k)/60)^7  (with replacement approximation)

  We use an integer approximation:
    prob(k) = 10000 - ((60 - k) * 10000 / 60) ^ 7 would overflow,
  so we use the simpler linear approximation:
    prob_approx(k) = k * handSize * 10000 / deckSize
  which is a first-order approximation valid for small k.
  This gives: 1 copy → ~1166, 2 → ~2333, 3 → ~3500, 4 → ~4666.
-/
def drawProbApprox (copies : Nat) : Nat :=
  copies * handSize * 10000 / deckSize

-- [T4]
theorem draw_prob_zero : drawProbApprox 0 = 0 := by native_decide

-- [T5]
theorem draw_prob_one : drawProbApprox 1 = 1166 := by native_decide

-- [T6]
theorem draw_prob_two : drawProbApprox 2 = 2333 := by native_decide

-- [T7]
theorem draw_prob_three : drawProbApprox 3 = 3500 := by native_decide

-- [T8]
theorem draw_prob_four : drawProbApprox 4 = 4666 := by native_decide

-- [T9] 0 copies means 0 probability.
theorem zero_copies_zero_prob (k : Nat) (h : k = 0) : drawProbApprox k = 0 := by
  subst h; native_decide

-- ============================================================
-- §3  Monotonicity of draw probability
-- ============================================================

/-- Helper: drawProbApprox is just a linear function. -/
theorem draw_prob_linear (k : Nat) :
    drawProbApprox k = k * 7 * 10000 / 60 := by
  simp [drawProbApprox, handSize, deckSize]

-- [T10] More copies ⟹ higher or equal draw probability.
theorem draw_prob_monotone (a b : Nat) (h : a ≤ b) :
    drawProbApprox a ≤ drawProbApprox b := by
  simp [drawProbApprox, handSize, deckSize]
  exact Nat.div_le_div_right (Nat.mul_le_mul_right 10000 (Nat.mul_le_mul_right 7 h))

-- [T11] Strictly more copies ⟹ strictly higher probability (for k ≤ maxCopies).
theorem draw_prob_strict_mono_4 (a b : Nat) (ha : a ≤ 4) (hb : b ≤ 4) (h : a < b) :
    drawProbApprox a < drawProbApprox b := by
  simp only [drawProbApprox, handSize, deckSize]; omega

-- ============================================================
-- §4  Probability bounding
-- ============================================================

-- [T12] Draw probability with max copies is bounded.
theorem draw_prob_bounded_4 : drawProbApprox maxCopies ≤ 10000 := by native_decide

-- [T13] Draw probability for max copies.
theorem draw_prob_max_copies : drawProbApprox maxCopies = 4666 := by native_decide

-- ============================================================
-- §5  Tech card definitions
-- ============================================================

/-- Archetype that the tech targets. -/
inductive TargetArchetype where
  | vstarCombo   -- Targets VSTAR-based combo decks
  | abilityCombo -- Targets ability-reliant decks
  | fusionStrike -- Targets Fusion Strike engine
  | darkType     -- Targets Darkness-weak Pokémon
  | general      -- General utility
  deriving DecidableEq, Repr, BEq

/-- A tech card for Bo3 side-decking strategy. -/
structure TechSlot where
  cardName     : String
  copies       : Nat
  target       : TargetArchetype
  winRateBoost : Nat  -- basis points improvement
  deriving Repr

/-- Validate that copies are within legal limits. -/
def TechSlot.isLegal (t : TechSlot) : Bool :=
  t.copies ≤ maxCopies

-- Specific meta-relevant tech cards (SV era)
def templeOfSinnoh : TechSlot := ⟨"Temple of Sinnoh", 2, .vstarCombo, 1500⟩
def pathToThePeak : TechSlot := ⟨"Path to the Peak", 3, .abilityCombo, 2000⟩
def drapionV : TechSlot := ⟨"Drapion V", 1, .fusionStrike, 1200⟩
def lostVacuum : TechSlot := ⟨"Lost Vacuum", 2, .general, 800⟩
def enhancedHammer : TechSlot := ⟨"Enhanced Hammer", 2, .general, 600⟩

-- [T14]
theorem temple_legal : templeOfSinnoh.isLegal = true := by native_decide
-- [T15]
theorem path_legal : pathToThePeak.isLegal = true := by native_decide
-- [T16]
theorem drapion_legal : drapionV.isLegal = true := by native_decide

-- ============================================================
-- §6  Expected matchup improvement
-- ============================================================

/-- Expected improvement = P(draw) × boost / 10000. -/
def expectedImprovement (t : TechSlot) : Nat :=
  drawProbApprox t.copies * t.winRateBoost / 10000

-- [T17]
theorem temple_improvement : expectedImprovement templeOfSinnoh = 349 := by native_decide
-- [T18]
theorem path_improvement : expectedImprovement pathToThePeak = 700 := by native_decide

-- [T19] Zero copies gives zero improvement.
theorem zero_copies_no_improvement (name : String) (tgt : TargetArchetype) (boost : Nat) :
    expectedImprovement ⟨name, 0, tgt, boost⟩ = 0 := by
  simp [expectedImprovement, drawProbApprox, handSize, deckSize]

-- ============================================================
-- §7  Side-deck plan
-- ============================================================

/-- A side-deck plan: cards to add and remove between games. -/
structure SidePlan where
  cardsIn  : List TechSlot
  cardsOut : List String
  deriving Repr

/-- Total cards being sided in. -/
def SidePlan.totalIn (p : SidePlan) : Nat :=
  p.cardsIn.foldl (fun acc t => acc + t.copies) 0

/-- Side plan is balanced: same number in and out. -/
def SidePlan.isBalanced (p : SidePlan) : Bool :=
  p.totalIn = p.cardsOut.length

-- An example side plan vs ability-combo
def vsAbilityPlan : SidePlan :=
  ⟨[pathToThePeak, ⟨"Spiritomb", 1, .abilityCombo, 800⟩],
   ["Boss's Orders", "Boss's Orders", "Iono", "Rare Candy"]⟩

-- [T20]
theorem vs_ability_plan_balanced : vsAbilityPlan.isBalanced = true := by native_decide

-- ============================================================
-- §8  Consistency cost modeling
-- ============================================================

/-- Consistency metric: fraction of "core" slots remaining (out of 60). -/
def consistencyRating (techSlots : Nat) : Nat :=
  (deckSize - min techSlots deckSize) * 100 / deckSize

-- [T21] No techs = full consistency.
theorem no_techs_full_consistency : consistencyRating 0 = 100 := by native_decide

-- [T22] More techs = less consistency.
theorem techs_reduce_consistency (a b : Nat) (h : a ≤ b) (hb : b ≤ deckSize) :
    consistencyRating b ≤ consistencyRating a := by
  simp [consistencyRating, deckSize]
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul_right
  simp [Nat.min_def]
  split <;> (rename_i h1; split <;> rename_i h2 <;> omega)

-- ============================================================
-- §9  Game 2/3 adaptation
-- ============================================================

/-- Win probability for a series (Bo3), given G1 and post-side G2/G3 rates.
    Scaled by 10000. Returns the probability of winning the series. -/
def bo3WinRate (g1Rate g23Rate : Nat) : Nat :=
  -- P(win series) = P(win G1)×P(win G2) + P(win G1)×P(lose G2)×P(win G3)
  --               + P(lose G1)×P(win G2)×P(win G3)
  -- Simplified: using 10000 scale
  let ww := g1Rate * g23Rate / 10000
  let wlw := g1Rate * (10000 - min g23Rate 10000) / 10000 * g23Rate / 10000
  let lww := (10000 - min g1Rate 10000) * g23Rate / 10000 * g23Rate / 10000
  ww + wlw + lww

-- [T23] 100% G1 and G2/G3 rates → series win.
theorem bo3_certain_win : bo3WinRate 10000 10000 = 10000 := by native_decide

-- [T24] 0% rates → 0% series win.
theorem bo3_certain_loss : bo3WinRate 0 0 = 0 := by native_decide

-- ============================================================
-- §10  Tech synergy
-- ============================================================

/-- Two techs targeting the same archetype have combined benefit. -/
def combinedBoost (t1 t2 : TechSlot) : Nat :=
  t1.winRateBoost + t2.winRateBoost

-- [T25] Combined boost is at least each individual boost.
theorem combined_ge_first (t1 t2 : TechSlot) :
    combinedBoost t1 t2 ≥ t1.winRateBoost := Nat.le_add_right _ _

-- [T26] Combined boost is at least each individual boost.
theorem combined_ge_second (t1 t2 : TechSlot) :
    combinedBoost t1 t2 ≥ t2.winRateBoost := Nat.le_add_left _ _

-- ============================================================
-- §11  Format legality
-- ============================================================

/-- Total tech copies in a side plan must fit in the deck. -/
def SidePlan.fitsInDeck (p : SidePlan) : Bool :=
  p.totalIn ≤ deckSize

-- [T27]
theorem ability_plan_fits : vsAbilityPlan.fitsInDeck = true := by native_decide

-- ============================================================
-- §12  All tech slots legal
-- ============================================================

def allLegal (techs : List TechSlot) : Bool :=
  techs.all (fun t => t.isLegal)

-- [T28]
theorem example_techs_legal :
    allLegal [templeOfSinnoh, pathToThePeak, drapionV, lostVacuum] = true := by native_decide

-- ============================================================
-- §13  Draw probability with prize cards
-- ============================================================

/-- Adjusted deck size after setting aside prize cards. -/
def effectiveDeckSize : Nat := deckSize - 6  -- 54 cards after 6 prizes

/-- Draw probability adjusted for prizes (still an approximation). -/
def drawProbPrizeAdj (copies : Nat) : Nat :=
  copies * handSize * 10000 / effectiveDeckSize

-- [T29] Prize-adjusted probability is higher than naive (smaller effective deck).
theorem prize_adj_ge_naive (k : Nat) :
    drawProbPrizeAdj k ≥ drawProbApprox k := by
  simp [drawProbPrizeAdj, drawProbApprox, effectiveDeckSize, deckSize, handSize]
  exact Nat.div_le_div_left (by decide : (54:Nat) ≤ 60) (by decide : 0 < 54)

-- [T30] Prize-adjusted also monotone.
theorem prize_adj_monotone (a b : Nat) (h : a ≤ b) :
    drawProbPrizeAdj a ≤ drawProbPrizeAdj b := by
  simp [drawProbPrizeAdj, effectiveDeckSize, deckSize, handSize]
  exact Nat.div_le_div_right (Nat.mul_le_mul_right 10000 (Nat.mul_le_mul_right 7 h))

-- ============================================================
-- §14  Card advantage from techs
-- ============================================================

/-- Net card advantage: improvement minus consistency loss. -/
def netAdvantage (boost consistencyCost : Nat) : Int :=
  (boost : Int) - (consistencyCost : Int)

-- [T31] Positive net advantage when boost exceeds cost.
theorem net_advantage_positive (b c : Nat) (h : b > c) :
    netAdvantage b c > 0 := by
  simp [netAdvantage]; omega

-- ============================================================
-- §15  Metagame call accuracy
-- ============================================================

/-- If you correctly predict the metagame, your techs are effective.
    Model: correctPrediction means full boost; incorrect means 0. -/
def techEffectiveness (boost : Nat) (correctCall : Bool) : Nat :=
  if correctCall then boost else 0

-- [T32] Correct call gives full boost.
theorem correct_call_full (b : Nat) : techEffectiveness b true = b := rfl

-- [T33] Incorrect call gives nothing.
theorem incorrect_call_zero (b : Nat) : techEffectiveness b false = 0 := rfl

-- ============================================================
-- §16  Total expected improvement across matchups
-- ============================================================

/-- Sum of expected improvements across all tech slots. -/
def totalImprovement (techs : List TechSlot) : Nat :=
  techs.foldl (fun acc t => acc + expectedImprovement t) 0

-- [T34] Empty tech list gives zero improvement.
theorem total_improvement_empty : totalImprovement [] = 0 := by
  simp [totalImprovement, List.foldl]

-- [T35] Single tech gives its own improvement.
theorem total_improvement_single (t : TechSlot) :
    totalImprovement [t] = expectedImprovement t := by
  simp [totalImprovement, List.foldl]

end PokemonLean.Core.SideDeck
