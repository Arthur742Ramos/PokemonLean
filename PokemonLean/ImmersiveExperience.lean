/-
  PokemonLean / ImmersiveExperience.lean

  Immersive / Illustration Rare mechanics for modern Pokémon TCG sets.
  Covers: special art rarities (IR, SIR, SAR, UR, Hyper Rare),
  pull rates per box, grading factors (PSA/CGC tiers), raw vs graded
  value ratios, expected value calculations.

  All proofs are sorry-free.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

-- ============================================================
-- §1  Rarity tiers
-- ============================================================

/-- Modern special art rarities. -/
inductive SpecialRarity where
  | illustrationRare    -- IR  (formerly "Full Art" in some sets)
  | specialIllustration -- SIR (immersive full-art cards)
  | specialArtRare      -- SAR (alternate art, Japanese sets)
  | ultraRare           -- UR  (gold cards)
  | hyperRare           -- HR  (textured / secret rare)
deriving DecidableEq, Repr, BEq

/-- Shorthand names. -/
abbrev IR  := SpecialRarity.illustrationRare
abbrev SIR := SpecialRarity.specialIllustration
abbrev SAR := SpecialRarity.specialArtRare
abbrev UR  := SpecialRarity.ultraRare
abbrev HR  := SpecialRarity.hyperRare

/-- Rarity ordering: higher = scarcer = more valuable (as Nat encoding). -/
def SpecialRarity.tier : SpecialRarity → Nat
  | .illustrationRare    => 1
  | .specialIllustration => 2
  | .specialArtRare      => 3
  | .ultraRare           => 4
  | .hyperRare           => 5

/-- Theorem 1: IR is the lowest special rarity tier. -/
theorem ir_lowest_tier : SpecialRarity.tier IR ≤ SpecialRarity.tier r := by
  cases r <;> simp [SpecialRarity.tier]

/-- Theorem 2: HR is the highest special rarity tier. -/
theorem hr_highest_tier : SpecialRarity.tier r ≤ SpecialRarity.tier HR := by
  cases r <;> simp [SpecialRarity.tier]

/-- Theorem 3: Tier is injective (distinct rarities have distinct tiers). -/
theorem tier_injective (a b : SpecialRarity) (h : a.tier = b.tier) : a = b := by
  cases a <;> cases b <;> simp [SpecialRarity.tier] at h <;> rfl

-- ============================================================
-- §2  Pull rates
-- ============================================================

/-- Pull rates per booster box (36 packs). Denominator = packs needed on average. -/
structure PullRate where
  rarity       : SpecialRarity
  packsPerPull : Nat   -- average packs per 1 pull (higher = rarer)
  hPos         : packsPerPull > 0
deriving Repr

/-- Canonical approximate pull rates (Scarlet & Violet era, per box ~36 packs). -/
def irPullRate  : PullRate := ⟨IR,  6,  by omega⟩   -- ~6 per box
def sirPullRate : PullRate := ⟨SIR, 18, by omega⟩   -- ~2 per box
def sarPullRate : PullRate := ⟨SAR, 36, by omega⟩   -- ~1 per box
def urPullRate  : PullRate := ⟨UR,  72, by omega⟩   -- ~1 per 2 boxes
def hrPullRate  : PullRate := ⟨HR, 144, by omega⟩   -- ~1 per 4 boxes

/-- Expected pulls from n packs. -/
def expectedPulls (pr : PullRate) (nPacks : Nat) : Nat :=
  nPacks / pr.packsPerPull

/-- Theorem 4: A full box (36 packs) yields ~6 IR pulls. -/
theorem ir_per_box : expectedPulls irPullRate 36 = 6 := by
  native_decide

/-- Theorem 5: A full box yields ~2 SIR pulls. -/
theorem sir_per_box : expectedPulls sirPullRate 36 = 2 := by
  native_decide

/-- Theorem 6: A full box yields ~1 SAR pull. -/
theorem sar_per_box : expectedPulls sarPullRate 36 = 1 := by
  native_decide

/-- Theorem 7: Rarer cards require more packs — monotonicity of pull rate with tier. -/
theorem higher_tier_fewer_pulls :
    irPullRate.packsPerPull ≤ sirPullRate.packsPerPull ∧
    sirPullRate.packsPerPull ≤ sarPullRate.packsPerPull ∧
    sarPullRate.packsPerPull ≤ urPullRate.packsPerPull ∧
    urPullRate.packsPerPull ≤ hrPullRate.packsPerPull := by
  simp [irPullRate, sirPullRate, sarPullRate, urPullRate, hrPullRate]

-- ============================================================
-- §3  Grading tiers (PSA / CGC)
-- ============================================================

/-- PSA grades 1–10. -/
structure PSAGrade where
  grade : Nat
  hRange : 1 ≤ grade ∧ grade ≤ 10
deriving Repr

/-- CGC grades use half-point scale: stored as 2× actual (so 19 = CGC 9.5). -/
structure CGCGrade where
  doubled : Nat   -- 2 × actual grade
  hRange  : 2 ≤ doubled ∧ doubled ≤ 20
deriving Repr

def psa10 : PSAGrade := ⟨10, by omega⟩
def psa9  : PSAGrade := ⟨9,  by omega⟩
def psa8  : PSAGrade := ⟨8,  by omega⟩
def cgc10 : CGCGrade := ⟨20, by omega⟩
def cgc95 : CGCGrade := ⟨19, by omega⟩
def cgc9  : CGCGrade := ⟨18, by omega⟩

/-- Theorem 8: PSA 10 is the maximum grade. -/
theorem psa10_is_max (g : PSAGrade) : g.grade ≤ psa10.grade := by
  exact g.hRange.2

/-- Theorem 9: CGC 10 (doubled=20) is the maximum. -/
theorem cgc10_is_max (g : CGCGrade) : g.doubled ≤ cgc10.doubled := by
  exact g.hRange.2

-- ============================================================
-- §4  Value modelling: raw vs graded
-- ============================================================

/-- Card value in cents to avoid floats. -/
structure CardValue where
  rawCents     : Nat
  gradedCents  : Nat  -- value if graded PSA 10
deriving DecidableEq, Repr

/-- Value multiplier (×100) for graded over raw. -/
def valueMultiplier100 (v : CardValue) : Nat :=
  if v.rawCents = 0 then 0 else (v.gradedCents * 100) / v.rawCents

/-- Example: a SIR card raw $50 (5000c), PSA 10 $200 (20000c). -/
def exampleSIR : CardValue := ⟨5000, 20000⟩

/-- Theorem 10: Graded value ≥ raw value for our example SIR. -/
theorem graded_ge_raw_example : exampleSIR.gradedCents ≥ exampleSIR.rawCents := by
  native_decide

/-- Theorem 11: Value multiplier for example SIR is 400 (= 4×). -/
theorem sir_multiplier : valueMultiplier100 exampleSIR = 400 := by
  native_decide

/-- A high-value HR example: raw $100 (10000c), PSA 10 $800 (80000c). -/
def exampleHR : CardValue := ⟨10000, 80000⟩

/-- Theorem 12: HR multiplier is 800 (= 8×). -/
theorem hr_multiplier : valueMultiplier100 exampleHR = 800 := by
  native_decide

-- ============================================================
-- §5  Grading cost analysis
-- ============================================================

/-- Grading cost in cents (PSA standard ≈ $25 = 2500 cents). -/
def psaStandardCostCents : Nat := 2500

/-- Net profit from grading = graded value − raw value − grading cost. -/
def gradingProfit (v : CardValue) (costCents : Nat) : Int :=
  (v.gradedCents : Int) - (v.rawCents : Int) - (costCents : Int)

/-- Theorem 13: Grading the example SIR is profitable. -/
theorem sir_grading_profitable :
    gradingProfit exampleSIR psaStandardCostCents > 0 := by
  native_decide

/-- Theorem 14: Grading the example HR is highly profitable. -/
theorem hr_grading_profitable :
    gradingProfit exampleHR psaStandardCostCents > 0 := by
  native_decide

/-- Theorem 15: Grading profit for HR exceeds SIR. -/
theorem hr_profit_exceeds_sir :
    gradingProfit exampleHR psaStandardCostCents >
    gradingProfit exampleSIR psaStandardCostCents := by
  native_decide

-- ============================================================
-- §6  Expected box value
-- ============================================================

/-- Simplified expected value from a 36-pack box given average card values per rarity. -/
def expectedBoxValue (irVal sirVal sarVal : Nat) : Nat :=
  expectedPulls irPullRate 36 * irVal +
  expectedPulls sirPullRate 36 * sirVal +
  expectedPulls sarPullRate 36 * sarVal

/-- Theorem 16: Box EV with IR=$5, SIR=$50, SAR=$100 = $230. -/
theorem box_ev_example :
    expectedBoxValue 500 5000 10000 = 23000 := by
  native_decide

/-- Theorem 17: Box EV scales linearly with SAR value. -/
theorem box_ev_sar_linear (irVal sirVal s1 s2 : Nat) :
    expectedBoxValue irVal sirVal (s1 + s2) =
    expectedBoxValue irVal sirVal s1 + expectedPulls sarPullRate 36 * s2 := by
  simp [expectedBoxValue, Nat.mul_add, Nat.add_assoc]

-- ============================================================
-- §7  Collection completeness
-- ============================================================

/-- Minimum boxes to expect at least one of each rarity tier (worst = HR). -/
def minBoxesForComplete : Nat := hrPullRate.packsPerPull / 36 + 1

/-- Theorem 18: Need ≥ 5 boxes to expect at least one HR. -/
theorem min_boxes_five : minBoxesForComplete = 5 := by
  native_decide

/-- Theorem 19: Pull rates are all positive. -/
theorem all_pull_rates_pos :
    irPullRate.packsPerPull > 0 ∧
    sirPullRate.packsPerPull > 0 ∧
    sarPullRate.packsPerPull > 0 ∧
    urPullRate.packsPerPull > 0 ∧
    hrPullRate.packsPerPull > 0 := by
  simp [irPullRate, sirPullRate, sarPullRate, urPullRate, hrPullRate]

/-- Theorem 20: PSA grade difference is meaningful — PSA 10 vs 9 gap. -/
theorem psa_grade_gap : psa10.grade - psa9.grade = 1 := by
  native_decide
