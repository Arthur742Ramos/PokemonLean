import PokemonLean.Basic

namespace PokemonLean.RetreatMechanics

open PokemonLean

-- ============================================================================
-- RETREAT COST TYPES
-- ============================================================================

structure RetreatCost where
  cost : Nat
  deriving Repr, BEq, DecidableEq

def RetreatCost.free : RetreatCost := ⟨0⟩
def RetreatCost.one : RetreatCost := ⟨1⟩
def RetreatCost.two : RetreatCost := ⟨2⟩
def RetreatCost.three : RetreatCost := ⟨3⟩
def RetreatCost.four : RetreatCost := ⟨4⟩
def RetreatCost.five : RetreatCost := ⟨5⟩

def isFreeRetreat (rc : RetreatCost) : Bool := rc.cost == 0
def isHeavyRetreat (rc : RetreatCost) : Bool := decide (rc.cost ≥ 3)
def isLightRetreat (rc : RetreatCost) : Bool := decide (rc.cost ≤ 1)

-- ============================================================================
-- RETREAT COST BASIC THEOREMS
-- ============================================================================


-- ============================================================================
-- SWITCH EFFECTS
-- ============================================================================

inductive SwitchEffect where
  | switch | escapeRope | bossOrders | guzma | airBalloon
  | floatStone | jetEnergy | counterCatcher | luxuryBall | pivotEnergy
  deriving Repr, BEq, DecidableEq

def isGustEffect : SwitchEffect → Bool
  | .bossOrders => true
  | .guzma => true
  | .counterCatcher => true
  | _ => false

def providesFreeRetreat : SwitchEffect → Bool
  | .switch => true
  | .floatStone => true
  | .jetEnergy => true
  | _ => false

def retreatReduction : SwitchEffect → Nat
  | .airBalloon => 2
  | .floatStone => 100
  | .jetEnergy => 100
  | _ => 0

-- ============================================================================
-- SWITCH EFFECT THEOREMS
-- ============================================================================


-- ============================================================================
-- EFFECTIVE RETREAT COST
-- ============================================================================

def effectiveRetreatCost (base : RetreatCost) (reductions : List SwitchEffect) : Nat :=
  let totalReduction := (reductions.map retreatReduction).foldl (· + ·) 0
  if totalReduction ≥ base.cost then 0 else base.cost - totalReduction

def canRetreatFree (base : RetreatCost) (reductions : List SwitchEffect) : Bool :=
  effectiveRetreatCost base reductions == 0

theorem effective_cost_le_base (base : RetreatCost) (reductions : List SwitchEffect) :
    effectiveRetreatCost base reductions ≤ base.cost := by
  simp only [effectiveRetreatCost]
  split
  · exact Nat.zero_le _
  · exact Nat.sub_le _ _


theorem effective_cost_no_reductions (base : RetreatCost) :
    effectiveRetreatCost base [] = base.cost := by
  simp only [effectiveRetreatCost, List.map_nil, List.foldl_nil]
  split
  · rename_i h; omega
  · rfl


-- ============================================================================
-- PIVOT POKEMON STRATEGY
-- ============================================================================

structure PivotPokemon where
  card : Card
  retreatCost : RetreatCost
  isStarter : Bool
  deriving Repr, BEq, DecidableEq

def isValidPivot (p : PivotPokemon) : Bool := decide (p.retreatCost.cost ≤ 1)

def pivotValue (p : PivotPokemon) : Nat :=
  if p.retreatCost.cost == 0 then 3
  else if p.retreatCost.cost == 1 then 2
  else 0

def bestPivotValue (pivots : List PivotPokemon) : Nat :=
  (pivots.map pivotValue).foldl max 0

theorem pivot_value_le_three (p : PivotPokemon) : pivotValue p ≤ 3 := by
  unfold pivotValue
  split
  · exact Nat.le_refl _
  · split <;> omega

theorem pivot_value_zero_of_heavy (p : PivotPokemon) (h : p.retreatCost.cost ≥ 2) :
    pivotValue p = 0 := by
  unfold pivotValue
  have h0 : (p.retreatCost.cost == 0) = false := by rw [beq_eq_false_iff_ne]; omega
  have h1 : (p.retreatCost.cost == 1) = false := by rw [beq_eq_false_iff_ne]; omega
  rw [h0, h1]; rfl


-- ============================================================================
-- STRANDING MECHANICS
-- ============================================================================

structure StrandingState where
  retreatCost : Nat
  hasSwitchCard : Bool
  hasFloatStone : Bool
  availableEnergy : Nat
  deriving Repr, BEq, DecidableEq

def isStranded (s : StrandingState) : Bool :=
  !s.hasSwitchCard && !s.hasFloatStone && decide (s.availableEnergy < s.retreatCost)

def strandingScore (s : StrandingState) : Nat :=
  if isStranded s then
    s.retreatCost - s.availableEnergy + (if decide (s.retreatCost ≥ 3) then 5 else 0)
  else 0

theorem not_stranded_with_switch (rc energy : Nat) :
    isStranded { retreatCost := rc, hasSwitchCard := true, hasFloatStone := false, availableEnergy := energy } = false := by
  simp [isStranded]

theorem not_stranded_with_float_stone (rc energy : Nat) :
    isStranded { retreatCost := rc, hasSwitchCard := false, hasFloatStone := true, availableEnergy := energy } = false := by
  simp [isStranded]

theorem not_stranded_enough_energy (rc energy : Nat) (h : energy ≥ rc) :
    isStranded { retreatCost := rc, hasSwitchCard := false, hasFloatStone := false, availableEnergy := energy } = false := by
  simp only [isStranded, Bool.not_false, Bool.true_and]
  rw [decide_eq_false_iff_not]; omega

theorem stranding_score_zero_if_not_stranded (s : StrandingState) (h : isStranded s = false) :
    strandingScore s = 0 := by
  simp [strandingScore, h]

-- ============================================================================
-- RETREAT ENERGY PAYMENT
-- ============================================================================

def canPayRetreat (energyCount retreatCost : Nat) : Bool := decide (energyCount ≥ retreatCost)

def energyAfterRetreat (energyCount retreatCost : Nat) : Nat :=
  if canPayRetreat energyCount retreatCost then energyCount - retreatCost else energyCount

theorem can_pay_zero_cost (n : Nat) : canPayRetreat n 0 = true := by
  simp [canPayRetreat]

theorem cannot_pay_no_energy (cost : Nat) (h : cost > 0) : canPayRetreat 0 cost = false := by
  simp only [canPayRetreat]; rw [decide_eq_false_iff_not]; omega

theorem energy_after_retreat_le (e c : Nat) : energyAfterRetreat e c ≤ e := by
  unfold energyAfterRetreat; split
  · exact Nat.sub_le _ _
  · exact Nat.le_refl _

theorem energy_after_free_retreat (n : Nat) : energyAfterRetreat n 0 = n := by
  simp [energyAfterRetreat, canPayRetreat]

-- ============================================================================
-- GUST TARGET VALUE
-- ============================================================================

def gustTargetValue (damage : Nat) (retreatCost : Nat) (energyAttached : Nat) : Nat :=
  (if damage > 0 then 3 else 0) +
  (if retreatCost ≥ 3 then 5 else if retreatCost ≥ 2 then 3 else 0) +
  (if energyAttached > 0 then 2 else 0)

theorem gust_value_nonneg (d r e : Nat) : 0 ≤ gustTargetValue d r e := Nat.zero_le _


-- ============================================================================
-- RETREAT SEQUENCING
-- ============================================================================

inductive RetreatStep where
  | payEnergy (count : Nat)
  | moveToActive (benchIdx : Nat)
  | moveToBench
  deriving Repr, BEq, DecidableEq

structure RetreatAction where
  steps : List RetreatStep
  energyPaid : Nat
  newActiveIdx : Nat
  deriving Repr, BEq, DecidableEq

def isValidRetreatAction (ra : RetreatAction) : Bool := ra.steps.length == 3

def totalEnergyInSteps (steps : List RetreatStep) : Nat :=
  steps.foldl (fun acc s => match s with | .payEnergy n => acc + n | _ => acc) 0

theorem valid_retreat_three_steps (ra : RetreatAction) (h : isValidRetreatAction ra = true) :
    ra.steps.length = 3 := by
  simp [isValidRetreatAction] at h; exact h


theorem total_energy_nonneg (steps : List RetreatStep) : 0 ≤ totalEnergyInSteps steps :=
  Nat.zero_le _

-- ============================================================================
-- SWITCH CARD COUNTS
-- ============================================================================

structure SwitchCardCounts where
  switchCards : Nat
  escapeRopes : Nat
  bossOrders : Nat
  counterCatchers : Nat
  deriving Repr, BEq, DecidableEq

def totalGustCards (sc : SwitchCardCounts) : Nat := sc.bossOrders + sc.counterCatchers
def totalSelfSwitch (sc : SwitchCardCounts) : Nat := sc.switchCards + sc.escapeRopes
def totalSwitchCards (sc : SwitchCardCounts) : Nat := totalSelfSwitch sc + totalGustCards sc

theorem total_switch_is_sum (sc : SwitchCardCounts) :
    totalSwitchCards sc = sc.switchCards + sc.escapeRopes + sc.bossOrders + sc.counterCatchers := by
  unfold totalSwitchCards totalSelfSwitch totalGustCards; omega

theorem total_switch_ge_gust (sc : SwitchCardCounts) :
    totalSwitchCards sc ≥ totalGustCards sc := by
  unfold totalSwitchCards; exact Nat.le_add_left _ _

theorem total_switch_ge_self (sc : SwitchCardCounts) :
    totalSwitchCards sc ≥ totalSelfSwitch sc := by
  unfold totalSwitchCards; exact Nat.le_add_right _ _

theorem gust_cards_le_total (sc : SwitchCardCounts) :
    totalGustCards sc ≤ totalSwitchCards sc := total_switch_ge_gust sc

theorem self_switch_le_total (sc : SwitchCardCounts) :
    totalSelfSwitch sc ≤ totalSwitchCards sc := total_switch_ge_self sc

-- ============================================================================
-- RETREAT COST COMPARISON THEOREMS
-- ============================================================================

theorem retreat_cost_eq_iff (a b : RetreatCost) : a = b ↔ a.cost = b.cost := by
  constructor
  · intro h; cases h; rfl
  · intro h; cases a; cases b; simp at h; subst h; rfl

theorem retreat_cost_le_iff (a b : RetreatCost) :
    a.cost ≤ b.cost ↔ ¬(b.cost < a.cost) := by omega

theorem heavy_implies_not_light (rc : RetreatCost) (h : isHeavyRetreat rc = true) :
    isLightRetreat rc = false := by
  unfold isHeavyRetreat at h; unfold isLightRetreat
  rw [decide_eq_true_eq] at h; rw [decide_eq_false_iff_not]; omega

theorem light_implies_not_heavy (rc : RetreatCost) (h : isLightRetreat rc = true) :
    isHeavyRetreat rc = false := by
  unfold isLightRetreat at h; unfold isHeavyRetreat
  rw [decide_eq_true_eq] at h; rw [decide_eq_false_iff_not]; omega

theorem free_implies_light (rc : RetreatCost) (h : isFreeRetreat rc = true) :
    isLightRetreat rc = true := by
  unfold isFreeRetreat at h; unfold isLightRetreat
  rw [beq_iff_eq] at h; rw [decide_eq_true_eq]; omega

theorem free_implies_not_heavy (rc : RetreatCost) (h : isFreeRetreat rc = true) :
    isHeavyRetreat rc = false :=
  light_implies_not_heavy rc (free_implies_light rc h)

end PokemonLean.RetreatMechanics
