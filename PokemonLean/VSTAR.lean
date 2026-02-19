import PokemonLean.Basic

namespace PokemonLean.VSTAR

open PokemonLean

-- ============================================================================
-- RULE BOX CLASSIFICATION
-- ============================================================================

inductive RuleBoxKind
  | noRuleBox
  | pokemonV
  | pokemonVSTAR
  | pokemonVMAX
  | pokemonVUNION
  | pokemonGX
  deriving Repr, BEq, DecidableEq

def hasRuleBox : RuleBoxKind → Bool
  | .noRuleBox => false
  | _ => true

def prizesForRuleBox : RuleBoxKind → Nat
  | .noRuleBox => 1
  | .pokemonV => 2
  | .pokemonVSTAR => 2
  | .pokemonVMAX => 3
  | .pokemonVUNION => 3
  | .pokemonGX => 2

@[simp] theorem hasRuleBox_noRuleBox : hasRuleBox .noRuleBox = false := rfl
@[simp] theorem hasRuleBox_pokemonV : hasRuleBox .pokemonV = true := rfl
@[simp] theorem hasRuleBox_pokemonVSTAR : hasRuleBox .pokemonVSTAR = true := rfl
@[simp] theorem hasRuleBox_pokemonVMAX : hasRuleBox .pokemonVMAX = true := rfl
@[simp] theorem hasRuleBox_pokemonVUNION : hasRuleBox .pokemonVUNION = true := rfl
@[simp] theorem hasRuleBox_pokemonGX : hasRuleBox .pokemonGX = true := rfl

@[simp] theorem prizes_noRuleBox : prizesForRuleBox .noRuleBox = 1 := rfl
@[simp] theorem prizes_pokemonV : prizesForRuleBox .pokemonV = 2 := rfl
@[simp] theorem prizes_pokemonVSTAR : prizesForRuleBox .pokemonVSTAR = 2 := rfl
@[simp] theorem prizes_pokemonVMAX : prizesForRuleBox .pokemonVMAX = 3 := rfl
@[simp] theorem prizes_pokemonVUNION : prizesForRuleBox .pokemonVUNION = 3 := rfl
@[simp] theorem prizes_pokemonGX : prizesForRuleBox .pokemonGX = 2 := rfl

theorem prizesForRuleBox_pos (kind : RuleBoxKind) : prizesForRuleBox kind > 0 := by
  cases kind <;> decide

theorem prizesForRuleBox_le_three (kind : RuleBoxKind) : prizesForRuleBox kind ≤ 3 := by
  cases kind <;> decide

theorem prizesForRuleBox_ge_one (kind : RuleBoxKind) : prizesForRuleBox kind ≥ 1 := by
  exact Nat.succ_le_of_lt (prizesForRuleBox_pos kind)

theorem v_and_vstar_same_prize : prizesForRuleBox .pokemonV = prizesForRuleBox .pokemonVSTAR := by
  rfl

theorem vmax_prize_gt_v_prize : prizesForRuleBox .pokemonV < prizesForRuleBox .pokemonVMAX := by
  decide

theorem hasRuleBox_false_iff (kind : RuleBoxKind) :
    hasRuleBox kind = false ↔ kind = .noRuleBox := by
  cases kind <;> simp [hasRuleBox]

theorem hasRuleBox_true_iff (kind : RuleBoxKind) :
    hasRuleBox kind = true ↔ kind ≠ .noRuleBox := by
  cases kind <;> simp [hasRuleBox]

-- ============================================================================
-- RULE BOX LOCK EFFECTS
-- ============================================================================

def ruleBoxSuppressed (globalRuleBoxLock : Bool) (kind : RuleBoxKind) : Bool :=
  hasRuleBox kind && globalRuleBoxLock

def ruleBoxEnabled (globalRuleBoxLock : Bool) (kind : RuleBoxKind) : Bool :=
  hasRuleBox kind && !globalRuleBoxLock

theorem ruleBoxSuppressed_unlocked (kind : RuleBoxKind) :
    ruleBoxSuppressed false kind = false := by
  simp [ruleBoxSuppressed]

theorem ruleBoxSuppressed_noRuleBox (lock : Bool) :
    ruleBoxSuppressed lock .noRuleBox = false := by
  simp [ruleBoxSuppressed]

theorem ruleBoxSuppressed_locked_v : ruleBoxSuppressed true .pokemonV = true := by
  simp [ruleBoxSuppressed]

theorem ruleBoxEnabled_unlocked (kind : RuleBoxKind) :
    ruleBoxEnabled false kind = hasRuleBox kind := by
  simp [ruleBoxEnabled]

theorem ruleBoxEnabled_locked (kind : RuleBoxKind) :
    ruleBoxEnabled true kind = false := by
  simp [ruleBoxEnabled]

theorem ruleBoxEnabled_noRuleBox (lock : Bool) :
    ruleBoxEnabled lock .noRuleBox = false := by
  simp [ruleBoxEnabled]

theorem ruleBoxEnabled_v_unlocked : ruleBoxEnabled false .pokemonV = true := by
  simp [ruleBoxEnabled]

-- ============================================================================
-- VMAX FORMS (DYNAMAX / GIGANTAMAX)
-- ============================================================================

inductive VMAXForm
  | dynamax
  | gigantamax
  deriving Repr, BEq, DecidableEq

def isDynamax : VMAXForm → Bool
  | .dynamax => true
  | .gigantamax => false

def isGigantamax : VMAXForm → Bool
  | .dynamax => false
  | .gigantamax => true

@[simp] theorem isDynamax_dynamax : isDynamax .dynamax = true := rfl
@[simp] theorem isDynamax_gigantamax : isDynamax .gigantamax = false := rfl
@[simp] theorem isGigantamax_dynamax : isGigantamax .dynamax = false := rfl
@[simp] theorem isGigantamax_gigantamax : isGigantamax .gigantamax = true := rfl

theorem vmaxForm_partition (form : VMAXForm) :
    isDynamax form = true ∨ isGigantamax form = true := by
  cases form <;> simp [isDynamax, isGigantamax]

theorem vmaxForm_not_both (form : VMAXForm) :
    ¬(isDynamax form = true ∧ isGigantamax form = true) := by
  cases form <;> simp [isDynamax, isGigantamax]

theorem dynamax_excludes_gigantamax (form : VMAXForm)
    (h : isDynamax form = true) : isGigantamax form = false := by
  cases form <;> simp [isDynamax, isGigantamax] at h ⊢

theorem gigantamax_excludes_dynamax (form : VMAXForm)
    (h : isGigantamax form = true) : isDynamax form = false := by
  cases form <;> simp [isDynamax, isGigantamax] at h ⊢

-- ============================================================================
-- POWER BUDGET (ONCE PER GAME)
-- ============================================================================

structure PowerBudget where
  vstarPowerUsed : Bool := false
  gxAttackUsed : Bool := false
  deriving Repr, BEq, DecidableEq

def emptyPowerBudget : PowerBudget :=
  { vstarPowerUsed := false, gxAttackUsed := false }

def canUseVSTARPower (budget : PowerBudget) : Bool :=
  !budget.vstarPowerUsed

def canUseGXAttack (budget : PowerBudget) : Bool :=
  !budget.gxAttackUsed

def markVSTARPowerUsed (budget : PowerBudget) : PowerBudget :=
  { budget with vstarPowerUsed := true }

def markGXAttackUsed (budget : PowerBudget) : PowerBudget :=
  { budget with gxAttackUsed := true }

def useVSTARPower (budget : PowerBudget) : Option PowerBudget :=
  if budget.vstarPowerUsed then none else some (markVSTARPowerUsed budget)

def useGXAttack (budget : PowerBudget) : Option PowerBudget :=
  if budget.gxAttackUsed then none else some (markGXAttackUsed budget)

@[simp] theorem emptyPowerBudget_vstar : emptyPowerBudget.vstarPowerUsed = false := rfl
@[simp] theorem emptyPowerBudget_gx : emptyPowerBudget.gxAttackUsed = false := rfl
@[simp] theorem canUseVSTARPower_empty : canUseVSTARPower emptyPowerBudget = true := by
  simp [canUseVSTARPower, emptyPowerBudget]
@[simp] theorem canUseGXAttack_empty : canUseGXAttack emptyPowerBudget = true := by
  simp [canUseGXAttack, emptyPowerBudget]

@[simp] theorem markVSTARPowerUsed_sets_flag (budget : PowerBudget) :
    (markVSTARPowerUsed budget).vstarPowerUsed = true := by
  simp [markVSTARPowerUsed]

@[simp] theorem markVSTARPowerUsed_preserves_gx (budget : PowerBudget) :
    (markVSTARPowerUsed budget).gxAttackUsed = budget.gxAttackUsed := by
  simp [markVSTARPowerUsed]

@[simp] theorem markGXAttackUsed_sets_flag (budget : PowerBudget) :
    (markGXAttackUsed budget).gxAttackUsed = true := by
  simp [markGXAttackUsed]

@[simp] theorem markGXAttackUsed_preserves_vstar (budget : PowerBudget) :
    (markGXAttackUsed budget).vstarPowerUsed = budget.vstarPowerUsed := by
  simp [markGXAttackUsed]

theorem useVSTARPower_none_when_used (budget : PowerBudget)
    (h : budget.vstarPowerUsed = true) : useVSTARPower budget = none := by
  simp [useVSTARPower, h]

theorem useVSTARPower_some_when_unused (budget : PowerBudget)
    (h : budget.vstarPowerUsed = false) :
    useVSTARPower budget = some (markVSTARPowerUsed budget) := by
  simp [useVSTARPower, h]

theorem useVSTARPower_marks_used (budget next : PowerBudget)
    (h : useVSTARPower budget = some next) :
    next.vstarPowerUsed = true := by
  by_cases hUsed : budget.vstarPowerUsed
  · simp [useVSTARPower, hUsed] at h
  · simp [useVSTARPower, hUsed] at h
    cases h
    simp [markVSTARPowerUsed]

theorem useVSTARPower_preserves_gx_flag (budget next : PowerBudget)
    (h : useVSTARPower budget = some next) :
    next.gxAttackUsed = budget.gxAttackUsed := by
  by_cases hUsed : budget.vstarPowerUsed
  · simp [useVSTARPower, hUsed] at h
  · simp [useVSTARPower, hUsed] at h
    cases h
    simp [markVSTARPowerUsed]

theorem useVSTARPower_twice_none (budget next : PowerBudget)
    (h : useVSTARPower budget = some next) :
    useVSTARPower next = none := by
  have hUsed : next.vstarPowerUsed = true := useVSTARPower_marks_used budget next h
  simp [useVSTARPower, hUsed]

theorem useGXAttack_none_when_used (budget : PowerBudget)
    (h : budget.gxAttackUsed = true) : useGXAttack budget = none := by
  simp [useGXAttack, h]

theorem useGXAttack_some_when_unused (budget : PowerBudget)
    (h : budget.gxAttackUsed = false) :
    useGXAttack budget = some (markGXAttackUsed budget) := by
  simp [useGXAttack, h]

theorem useGXAttack_marks_used (budget next : PowerBudget)
    (h : useGXAttack budget = some next) :
    next.gxAttackUsed = true := by
  by_cases hUsed : budget.gxAttackUsed
  · simp [useGXAttack, hUsed] at h
  · simp [useGXAttack, hUsed] at h
    cases h
    simp [markGXAttackUsed]

theorem useGXAttack_preserves_vstar_flag (budget next : PowerBudget)
    (h : useGXAttack budget = some next) :
    next.vstarPowerUsed = budget.vstarPowerUsed := by
  by_cases hUsed : budget.gxAttackUsed
  · simp [useGXAttack, hUsed] at h
  · simp [useGXAttack, hUsed] at h
    cases h
    simp [markGXAttackUsed]

theorem useGXAttack_twice_none (budget next : PowerBudget)
    (h : useGXAttack budget = some next) :
    useGXAttack next = none := by
  have hUsed : next.gxAttackUsed = true := useGXAttack_marks_used budget next h
  simp [useGXAttack, hUsed]

theorem canUseGXAttack_after_vstar_use (budget next : PowerBudget)
    (h : useVSTARPower budget = some next) :
    canUseGXAttack next = canUseGXAttack budget := by
  simp [canUseGXAttack, useVSTARPower_preserves_gx_flag budget next h]

theorem canUseVSTARPower_after_gx_use (budget next : PowerBudget)
    (h : useGXAttack budget = some next) :
    canUseVSTARPower next = canUseVSTARPower budget := by
  simp [canUseVSTARPower, useGXAttack_preserves_vstar_flag budget next h]

-- ============================================================================
-- VUNION ASSEMBLY FROM DISCARD (4 PIECES)
-- ============================================================================

inductive VUnionSlot
  | upperLeft
  | upperRight
  | lowerLeft
  | lowerRight
  deriving Repr, BEq, DecidableEq

structure VUnionPiece where
  name : String
  slot : VUnionSlot
  deriving Repr, BEq, DecidableEq

def hasVUnionPiece (name : String) (slot : VUnionSlot) (discard : List VUnionPiece) : Bool :=
  discard.any (fun piece => piece.name == name && piece.slot == slot)

def canAssembleVUnion (name : String) (discard : List VUnionPiece) : Bool :=
  hasVUnionPiece name .upperLeft discard &&
  hasVUnionPiece name .upperRight discard &&
  hasVUnionPiece name .lowerLeft discard &&
  hasVUnionPiece name .lowerRight discard

structure AssembledVUnion where
  name : String
  deriving Repr, BEq, DecidableEq

def assembleVUnion (name : String) (discard : List VUnionPiece) : Option AssembledVUnion :=
  if canAssembleVUnion name discard then some { name := name } else none

@[simp] theorem hasVUnionPiece_nil (name : String) (slot : VUnionSlot) :
    hasVUnionPiece name slot [] = false := by
  simp [hasVUnionPiece]

theorem hasVUnionPiece_cons_hit (name : String) (slot : VUnionSlot) (rest : List VUnionPiece) :
    hasVUnionPiece name slot (({ name := name, slot := slot } : VUnionPiece) :: rest) = true := by
  unfold hasVUnionPiece
  simp [List.any_cons]
  left
  simp only [BEq.beq]
  cases slot <;> rfl

theorem canAssembleVUnion_nil (name : String) : canAssembleVUnion name [] = false := by
  simp [canAssembleVUnion, hasVUnionPiece]

theorem canAssembleVUnion_of_all_slots (name : String) (discard : List VUnionPiece)
    (hUL : hasVUnionPiece name .upperLeft discard = true)
    (hUR : hasVUnionPiece name .upperRight discard = true)
    (hLL : hasVUnionPiece name .lowerLeft discard = true)
    (hLR : hasVUnionPiece name .lowerRight discard = true) :
    canAssembleVUnion name discard = true := by
  simp [canAssembleVUnion, hUL, hUR, hLL, hLR]

theorem canAssembleVUnion_exact_four (name : String) (rest : List VUnionPiece) :
    canAssembleVUnion name
      (({ name := name, slot := .upperLeft } : VUnionPiece) ::
       ({ name := name, slot := .upperRight } : VUnionPiece) ::
       ({ name := name, slot := .lowerLeft } : VUnionPiece) ::
       ({ name := name, slot := .lowerRight } : VUnionPiece) ::
       rest) = true := by
  have h1 := hasVUnionPiece_cons_hit name .upperLeft
    (({ name := name, slot := .upperRight } : VUnionPiece) ::
     ({ name := name, slot := .lowerLeft } : VUnionPiece) ::
     ({ name := name, slot := .lowerRight } : VUnionPiece) :: rest)
  have h2 := hasVUnionPiece_cons_hit name .upperRight
    (({ name := name, slot := .lowerLeft } : VUnionPiece) ::
     ({ name := name, slot := .lowerRight } : VUnionPiece) :: rest)
  have h3 := hasVUnionPiece_cons_hit name .lowerLeft
    (({ name := name, slot := .lowerRight } : VUnionPiece) :: rest)
  have h4 := hasVUnionPiece_cons_hit name .lowerRight rest
  simp only [canAssembleVUnion, hasVUnionPiece, List.any_cons] at *
  simp_all

theorem assembleVUnion_some_of_can (name : String) (discard : List VUnionPiece)
    (h : canAssembleVUnion name discard = true) :
    assembleVUnion name discard = some { name := name } := by
  simp [assembleVUnion, h]

theorem assembleVUnion_none_of_not_can (name : String) (discard : List VUnionPiece)
    (h : canAssembleVUnion name discard = false) :
    assembleVUnion name discard = none := by
  simp [assembleVUnion, h]

theorem assembleVUnion_name (name : String) (discard : List VUnionPiece) (assembled : AssembledVUnion)
    (h : assembleVUnion name discard = some assembled) :
    assembled.name = name := by
  unfold assembleVUnion at h
  split at h
  · cases h
    rfl
  · simp at h

-- ============================================================================
-- KO PRIZE PAYOUT FOR RULE BOX CARDS
-- ============================================================================

def takePrizeCards : PlayerState → PlayerState → Nat → PlayerState × PlayerState
  | attacker, defender, 0 => (attacker, defender)
  | attacker, defender, n + 1 =>
      let (attacker', defender') := takePrize attacker defender
      takePrizeCards attacker' defender' n

def takeKOPayout (attacker defender : PlayerState) (kind : RuleBoxKind) : PlayerState × PlayerState :=
  takePrizeCards attacker defender (prizesForRuleBox kind)

@[simp] theorem takePrizeCards_zero (attacker defender : PlayerState) :
    takePrizeCards attacker defender 0 = (attacker, defender) := by
  rfl

@[simp] theorem takePrizeCards_succ (attacker defender : PlayerState) (n : Nat) :
    takePrizeCards attacker defender (n + 1) =
      let (attacker', defender') := takePrize attacker defender
      takePrizeCards attacker' defender' n := by
  rfl

theorem takePrizeCards_one (attacker defender : PlayerState) :
    takePrizeCards attacker defender 1 = takePrize attacker defender := by
  simp [takePrizeCards]

theorem takeKOPayout_noRuleBox (attacker defender : PlayerState) :
    takeKOPayout attacker defender .noRuleBox = takePrizeCards attacker defender 1 := by
  simp [takeKOPayout, prizesForRuleBox]

theorem takeKOPayout_pokemonV (attacker defender : PlayerState) :
    takeKOPayout attacker defender .pokemonV = takePrizeCards attacker defender 2 := by
  simp [takeKOPayout, prizesForRuleBox]

theorem takeKOPayout_pokemonVSTAR (attacker defender : PlayerState) :
    takeKOPayout attacker defender .pokemonVSTAR = takePrizeCards attacker defender 2 := by
  simp [takeKOPayout, prizesForRuleBox]

theorem takeKOPayout_pokemonVMAX (attacker defender : PlayerState) :
    takeKOPayout attacker defender .pokemonVMAX = takePrizeCards attacker defender 3 := by
  simp [takeKOPayout, prizesForRuleBox]

theorem takeKOPayout_pokemonVUNION (attacker defender : PlayerState) :
    takeKOPayout attacker defender .pokemonVUNION = takePrizeCards attacker defender 3 := by
  simp [takeKOPayout, prizesForRuleBox]

theorem takeKOPayout_pokemonGX (attacker defender : PlayerState) :
    takeKOPayout attacker defender .pokemonGX = takePrizeCards attacker defender 2 := by
  simp [takeKOPayout, prizesForRuleBox]

end PokemonLean.VSTAR
