/-
  PokemonLean / RuleBoxPokemon.lean

  Rule Box Pokémon mechanics:
  - EX, GX, V, VMAX, VSTAR, ex, and Tera all count as Rule Box targets
  - All grant extra prizes on knockout
  - Path to the Peak / Roxanne pressure points
  - Prize-race math comparisons
  - Rule Box evolution-line modeling

  Fully proved with direct computational paths.
-/

set_option linter.unusedVariables false

namespace RuleBoxPokemon

-- ============================================================================
-- §1  Computational path core
-- ============================================================================

inductive Step (α : Type) : α → α → Type where
  | refl : (a : α) → Step α a a
  | rule : (name : String) → (a b : α) → Step α a b

inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

def Path.trans : Path α a b → Path α b c → Path α a c
  | .nil _, q => q
  | .cons s p, q => .cons s (p.trans q)

def Path.length : Path α a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

def Path.single (s : Step α a b) : Path α a b :=
  .cons s (.nil _)

def Step.symm : Step α a b → Step α b a
  | .refl a => .refl a
  | .rule name a b => .rule (name ++ "⁻¹") b a

def Step.map (f : α → β) : Step α a b → Step β (f a) (f b)
  | .refl a => .refl (f a)
  | .rule name a b => .rule name (f a) (f b)

def Path.symm : Path α a b → Path α b a
  | .nil a => .nil a
  | .cons s p => (p.symm).trans (.single (s.symm))

def Path.congrArg (f : α → β) : Path α a b → Path β (f a) (f b)
  | .nil a => .nil (f a)
  | .cons s p => .cons (s.map f) (p.congrArg f)

theorem path_trans_assoc (p : Path α a b) (q : Path α b c) (r : Path α c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => rfl
  | cons s p ih => simp [Path.trans, ih]

theorem path_trans_nil_right (p : Path α a b) : p.trans (.nil b) = p := by
  induction p with
  | nil _ => rfl
  | cons s p ih => simp [Path.trans, ih]

theorem path_length_trans (p : Path α a b) (q : Path α b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [Path.trans, Path.length]
  | cons s p ih => simp [Path.trans, Path.length, ih, Nat.add_assoc]

theorem path_symm_single_length (s : Step α a b) :
    (Path.symm (Path.single s)).length = 1 := by
  simp [Path.symm, Path.single, Path.trans, Path.length]

theorem path_congrArg_length (f : α → β) (p : Path α a b) :
    (Path.congrArg f p).length = p.length := by
  induction p with
  | nil _ => rfl
  | cons s p ih => simp [Path.congrArg, Path.length, ih]

-- ============================================================================
-- §2  Rule Box universe and prize rules
-- ============================================================================

inductive RuleBoxKind where
  | EX | GX | V | VMAX | VSTAR | ex | tera
deriving DecidableEq, Repr, BEq

def kindName : RuleBoxKind → String
  | .EX => "EX"
  | .GX => "GX"
  | .V => "V"
  | .VMAX => "VMAX"
  | .VSTAR => "VSTAR"
  | .ex => "ex"
  | .tera => "Tera"

def prizePenalty : RuleBoxKind → Nat
  | .EX => 2
  | .GX => 2
  | .V => 2
  | .VMAX => 3
  | .VSTAR => 2
  | .ex => 2
  | .tera => 2

def isRuleBox : RuleBoxKind → Bool := fun _ => true

def givesExtraPrizes (k : RuleBoxKind) : Bool :=
  decide (prizePenalty k > 1)

theorem EX_extra_prize : givesExtraPrizes .EX = true := by native_decide
theorem GX_extra_prize : givesExtraPrizes .GX = true := by native_decide
theorem V_extra_prize : givesExtraPrizes .V = true := by native_decide
theorem VMAX_extra_prize : givesExtraPrizes .VMAX = true := by native_decide
theorem VSTAR_extra_prize : givesExtraPrizes .VSTAR = true := by native_decide
theorem ex_extra_prize : givesExtraPrizes .ex = true := by native_decide
theorem tera_extra_prize : givesExtraPrizes .tera = true := by native_decide

theorem all_rulebox_unified (k : RuleBoxKind) : isRuleBox k = true := rfl

theorem all_rulebox_extra_prizes (k : RuleBoxKind) : givesExtraPrizes k = true := by
  cases k <;> native_decide

theorem vmax_has_larger_prize_penalty_than_v :
    prizePenalty .VMAX > prizePenalty .V := by
  decide

-- ============================================================================
-- §3  Rule Box hate cards
-- ============================================================================

inductive HateCard where
  | pathToThePeak | roxanne
deriving DecidableEq, Repr, BEq

def pathToThePeakBlocksAbilities (k : RuleBoxKind) : Bool :=
  isRuleBox k

def roxanneLive (opponentPrizesRemaining : Nat) : Bool :=
  decide (opponentPrizesRemaining ≤ 3)

def roxanneHandSize (opponentPrizesRemaining : Nat) : Nat :=
  if roxanneLive opponentPrizesRemaining then 2 else 6

theorem path_to_the_peak_hits_all_rulebox (k : RuleBoxKind) :
    pathToThePeakBlocksAbilities k = true := by
  cases k <;> rfl

theorem roxanne_live_at_three : roxanneLive 3 = true := by
  native_decide

theorem roxanne_not_live_at_four : roxanneLive 4 = false := by
  native_decide

theorem roxanne_reduces_hand_when_live (n : Nat) (h : roxanneLive n = true) :
    roxanneHandSize n = 2 := by
  simp [roxanneHandSize, h]

theorem roxanne_leaves_full_hand_when_not_live (n : Nat) (h : roxanneLive n = false) :
    roxanneHandSize n = 6 := by
  simp [roxanneHandSize, h]

-- ============================================================================
-- §4  Prize-race math + paths
-- ============================================================================

def takeKO (remaining : Nat) (k : RuleBoxKind) : Nat :=
  remaining - prizePenalty k

def koStep (k : RuleBoxKind) (n : Nat) : Step Nat n (takeKO n k) :=
  .rule ("KO_" ++ kindName k) n (takeKO n k)

def twoVMaxKOPath : Path Nat 6 (takeKO (takeKO 6 .VMAX) .VMAX) :=
  let s1 := takeKO 6 .VMAX
  (Path.single (koStep .VMAX 6)).trans (Path.single (koStep .VMAX s1))

def threeTwoPrizeKOPath : Path Nat 6 (takeKO (takeKO (takeKO 6 .V) .GX) .ex) :=
  let s1 := takeKO 6 .V
  let s2 := takeKO s1 .GX
  Path.trans
    (Path.trans (Path.single (koStep .V 6)) (Path.single (koStep .GX s1)))
    (Path.single (koStep .ex s2))

theorem two_vmax_knockouts_take_all_prizes :
    takeKO (takeKO 6 .VMAX) .VMAX = 0 := rfl

theorem three_two_prize_knockouts_take_all_prizes :
    takeKO (takeKO (takeKO 6 .V) .GX) .ex = 0 := rfl

theorem two_vmax_path_length : twoVMaxKOPath.length = 2 := by
  simp [twoVMaxKOPath, Path.single, Path.trans, Path.length]

theorem three_two_prize_path_length : threeTwoPrizeKOPath.length = 3 := by
  simp [threeTwoPrizeKOPath, Path.single, Path.trans, Path.length]

theorem two_vmax_faster_than_three_two_prize :
    twoVMaxKOPath.length < threeTwoPrizeKOPath.length := by
  rw [two_vmax_path_length, three_two_prize_path_length]
  decide

theorem two_vmax_prize_math :
    prizePenalty .VMAX + prizePenalty .VMAX = 6 := by
  native_decide

theorem three_two_prize_math :
    prizePenalty .V + prizePenalty .GX + prizePenalty .ex = 6 := by
  native_decide

theorem roxanne_live_after_two_vmax_KOs :
    roxanneLive (takeKO (takeKO 6 .VMAX) .VMAX) = true := by
  native_decide

-- ============================================================================
-- §5  Rule Box evolution lines
-- ============================================================================

inductive EvolvesTo : RuleBoxKind → RuleBoxKind → Prop where
  | v_to_vmax : EvolvesTo .V .VMAX
  | v_to_vstar : EvolvesTo .V .VSTAR
  | ex_to_tera : EvolvesTo .ex .tera
  | ex_to_ex : EvolvesTo .ex .ex
  | EX_to_EX : EvolvesTo .EX .EX
  | GX_to_GX : EvolvesTo .GX .GX

def vToVMaxLine : Path RuleBoxKind .V .VMAX :=
  Path.single (Step.rule "V_to_VMAX" RuleBoxKind.V RuleBoxKind.VMAX)

def vToVStarLine : Path RuleBoxKind .V .VSTAR :=
  Path.single (Step.rule "V_to_VSTAR" RuleBoxKind.V RuleBoxKind.VSTAR)

def exToTeraLine : Path RuleBoxKind .ex .tera :=
  Path.single (Step.rule "ex_to_Tera" RuleBoxKind.ex RuleBoxKind.tera)

theorem v_evolves_to_vmax : EvolvesTo .V .VMAX := .v_to_vmax
theorem v_evolves_to_vstar : EvolvesTo .V .VSTAR := .v_to_vstar
theorem ex_evolves_to_tera : EvolvesTo .ex .tera := .ex_to_tera

theorem gx_does_not_evolve_to_vmax : ¬ EvolvesTo .GX .VMAX := by
  intro h
  cases h

theorem v_line_lengths :
    vToVMaxLine.length = 1 ∧ vToVStarLine.length = 1 := by
  constructor <;> simp [vToVMaxLine, vToVStarLine, Path.single, Path.length]

theorem ex_to_tera_line_length : exToTeraLine.length = 1 := by
  simp [exToTeraLine, Path.single, Path.length]

end RuleBoxPokemon
