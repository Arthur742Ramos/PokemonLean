/-
  PokemonLean / RuleBoxPokemon.lean

  Rule Box Pokémon mechanics:
  - EX, GX, V, VMAX, VSTAR, ex, and Tera all count as Rule Box targets
  - All grant extra prizes on knockout
  - Path to the Peak / Roxanne pressure points
  - Prize-race math comparisons
  - Rule Box evolution-line modeling

-/

set_option linter.unusedVariables false

namespace RuleBoxPokemon

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


def roxanneLive (opponentPrizesRemaining : Nat) : Bool :=
  decide (opponentPrizesRemaining ≤ 3)

def roxanneHandSize (opponentPrizesRemaining : Nat) : Nat :=
  if roxanneLive opponentPrizesRemaining then 2 else 6


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


theorem two_vmax_knockouts_take_all_prizes :
    takeKO (takeKO 6 .VMAX) .VMAX = 0 := rfl

theorem three_two_prize_knockouts_take_all_prizes :
    takeKO (takeKO (takeKO 6 .V) .GX) .ex = 0 := rfl


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

theorem v_evolves_to_vmax : EvolvesTo .V .VMAX := .v_to_vmax
theorem v_evolves_to_vstar : EvolvesTo .V .VSTAR := .v_to_vstar
theorem ex_evolves_to_tera : EvolvesTo .ex .tera := .ex_to_tera

theorem gx_does_not_evolve_to_vmax : ¬ EvolvesTo .GX .VMAX := by
  intro h
  cases h


end RuleBoxPokemon
