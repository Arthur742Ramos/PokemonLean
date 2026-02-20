import Lean.Elab.Tactic
/-
  PokemonLean/SharePerturbation.lean

  Formal share-perturbation theorems for the Trainer Hill top-14 metagame.
-/
import PokemonLean.RealMetagame

namespace PokemonLean.SharePerturbation

open PokemonLean.NashEquilibrium (Rat)
open PokemonLean.RealMetagame

elab "optimize_proof" : tactic => do
  try
    Lean.Elab.Tactic.evalTactic (← `(tactic| decide))
  catch _ =>
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact (decide_eq_true_eq.mp
      (by decide : decide (_ : Prop) = true))))

elab "optimize_proof_native" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact (decide_eq_true_eq.mp
    (by decide : decide (_ : Prop) = true))))


open PokemonLean.RealMetagame.Deck

abbrev Deck := PokemonLean.RealMetagame.Deck

def natToRat (n : Nat) : Rat := ((n : Int) : Rat)

def baseShare : Deck → Rat := fun d => natToRat (metaShare d)

def top14ShareTotal : Rat :=
  (Deck.all.map baseShare).foldl (· + ·) 0

def sharesWithProportionalShift (focus : Deck) (target : Rat) : Deck → Rat :=
  let old := baseShare focus
  let scale := (top14ShareTotal - target) / (top14ShareTotal - old)
  fun d => if d = focus then target else baseShare d * scale

def opponentShareMass (shares : Deck → Rat) (d : Deck) : Rat :=
  (Deck.all.map (fun opp => if opp = d then (0 : Rat) else shares opp)).foldl (· + ·) 0

def weightedMatchupSum (shares : Deck → Rat) (d : Deck) : Rat :=
  (Deck.all.map
    (fun opp => if opp = d then (0 : Rat) else shares opp * natToRat (matchupWR d opp))).foldl (· + ·) 0

/-- Expected WR vs the field with deck `d` removed from opponent normalization. -/
def expectedWRVsField (shares : Deck → Rat) (d : Deck) : Rat :=
  weightedMatchupSum shares d / (opponentShareMass shares d * 1000)

def expectedWRUnderShift (focus deck : Deck) (target : Rat) : Rat :=
  expectedWRVsField (sharesWithProportionalShift focus target) deck

def top6Decks : List Deck :=
  [.DragapultDusknoir, .GholdengoLunatone, .GrimssnarlFroslass,
   .MegaAbsolBox, .Gardevoir, .CharizardNoctowl]

def dragapultPercentGrid : List Nat :=
  (List.range 30).map (fun n => n + 1)

def minTop6TierBoundaryGap : Rat :=
  expectedWRVsField baseShare .GrimssnarlFroslass - expectedWRVsField baseShare .MegaAbsolBox

def maxTop6MatchupSpread : Rat := 323 / 1000

def conservativeTierFlipL1Bound : Rat :=
  minTop6TierBoundaryGap / maxTop6MatchupSpread

theorem top14_share_total : top14ShareTotal = 695 := by optimize_proof

theorem paradox_holds_drag_at_10pct :
    expectedWRUnderShift .DragapultDusknoir .DragapultDusknoir 100 < 1 / 2 := by
  optimize_proof_native

theorem paradox_holds_drag_at_5pct :
    expectedWRUnderShift .DragapultDusknoir .DragapultDusknoir 50 < 1 / 2 := by
  optimize_proof_native

theorem grimmsnarl_stays_best_at_10pct :
    expectedWRUnderShift .GrimssnarlFroslass .GrimssnarlFroslass 100 > 1 / 2 ∧
    (∀ d ∈ top6Decks,
      expectedWRUnderShift .GrimssnarlFroslass d 100 ≤
        expectedWRUnderShift .GrimssnarlFroslass .GrimssnarlFroslass 100) := by
  optimize_proof_native

theorem grimmsnarl_stays_best_at_15pct :
    expectedWRUnderShift .GrimssnarlFroslass .GrimssnarlFroslass 155 > 1 / 2 := by
  optimize_proof_native

theorem paradox_independent_of_popularity :
    ∀ pct ∈ dragapultPercentGrid,
      expectedWRUnderShift .DragapultDusknoir .DragapultDusknoir (natToRat (10 * pct)) < 1 / 2 := by
  optimize_proof_native

theorem share_sensitivity_bound :
    minTop6TierBoundaryGap = 770547 / 69230000 ∧
    conservativeTierFlipL1Bound = 770547 / 22361290 ∧
    conservativeTierFlipL1Bound > 3 / 100 := by
  optimize_proof

end PokemonLean.SharePerturbation
