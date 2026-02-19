/-
  PokemonLean/MatchupAnalysis.lean -- Real Trainer Hill Top-6 metagame analysis

  Data: Trainer Hill, 2026-01-29 to 2026-02-19, 50+ player tournaments.
  Win rates are stored as percentage * 10 (e.g. 627 = 62.7%).
-/
import PokemonLean.Core.Types

namespace PokemonLean.MatchupAnalysis

def dataSource : String :=
  "Data: Trainer Hill, 2026-01-29 to 2026-02-19, 50+ player tournaments"

/-! ## 1. Top-6 deck universe -/

inductive Archetype6 where
  | DragapultDusknoir
  | GholdengoLunatone
  | GrimmsnarlFroslass
  | MegaAbsolBox
  | Gardevoir
  | CharizardNoctowl
  deriving DecidableEq, BEq, Repr, Inhabited

open Archetype6

def Archetype6.all : List Archetype6 :=
  [DragapultDusknoir, GholdengoLunatone, GrimmsnarlFroslass,
   MegaAbsolBox, Gardevoir, CharizardNoctowl]

private def Archetype6.forAll (p : Archetype6 → Prop) [DecidablePred p] : Decidable (∀ a, p a) :=
  if h1 : p DragapultDusknoir then
    if h2 : p GholdengoLunatone then
      if h3 : p GrimmsnarlFroslass then
        if h4 : p MegaAbsolBox then
          if h5 : p Gardevoir then
            if h6 : p CharizardNoctowl then
              isTrue (fun a => by cases a <;> assumption)
            else isFalse (fun h => h6 (h CharizardNoctowl))
          else isFalse (fun h => h5 (h Gardevoir))
        else isFalse (fun h => h4 (h MegaAbsolBox))
      else isFalse (fun h => h3 (h GrimmsnarlFroslass))
    else isFalse (fun h => h2 (h GholdengoLunatone))
  else isFalse (fun h => h1 (h DragapultDusknoir))

instance (p : Archetype6 → Prop) [DecidablePred p] : Decidable (∀ a, p a) :=
  Archetype6.forAll p

/-! ## 2. Real top-6 shares and matchup matrix -/

/-- Meta share in tenths of a percent (15.5% -> 155). -/
def metaShareX10 : Archetype6 → Nat
  | DragapultDusknoir => 155
  | GholdengoLunatone => 99
  | GrimmsnarlFroslass => 51
  | MegaAbsolBox => 50
  | Gardevoir => 46
  | CharizardNoctowl => 43

theorem TOP6_SHARE_TOTAL : (Archetype6.all.map metaShareX10).foldl (· + ·) 0 = 444 := by
  native_decide

/-- Real Trainer Hill top-6 matrix, percentage * 10. -/
def matchupWRx10 (a b : Archetype6) : Nat :=
  match a, b with
  | DragapultDusknoir, DragapultDusknoir => 494
  | DragapultDusknoir, GholdengoLunatone => 436
  | DragapultDusknoir, GrimmsnarlFroslass => 386
  | DragapultDusknoir, MegaAbsolBox => 382
  | DragapultDusknoir, Gardevoir => 343
  | DragapultDusknoir, CharizardNoctowl => 641
  | GholdengoLunatone, DragapultDusknoir => 521
  | GholdengoLunatone, GholdengoLunatone => 488
  | GholdengoLunatone, GrimmsnarlFroslass => 476
  | GholdengoLunatone, MegaAbsolBox => 443
  | GholdengoLunatone, Gardevoir => 441
  | GholdengoLunatone, CharizardNoctowl => 483
  | GrimmsnarlFroslass, DragapultDusknoir => 572
  | GrimmsnarlFroslass, GholdengoLunatone => 467
  | GrimmsnarlFroslass, GrimmsnarlFroslass => 485
  | GrimmsnarlFroslass, MegaAbsolBox => 344
  | GrimmsnarlFroslass, Gardevoir => 566
  | GrimmsnarlFroslass, CharizardNoctowl => 558
  | MegaAbsolBox, DragapultDusknoir => 576
  | MegaAbsolBox, GholdengoLunatone => 512
  | MegaAbsolBox, GrimmsnarlFroslass => 621
  | MegaAbsolBox, MegaAbsolBox => 494
  | MegaAbsolBox, Gardevoir => 558
  | MegaAbsolBox, CharizardNoctowl => 475
  | Gardevoir, DragapultDusknoir => 627
  | Gardevoir, GholdengoLunatone => 493
  | Gardevoir, GrimmsnarlFroslass => 374
  | Gardevoir, MegaAbsolBox => 402
  | Gardevoir, Gardevoir => 480
  | Gardevoir, CharizardNoctowl => 394
  | CharizardNoctowl, DragapultDusknoir => 324
  | CharizardNoctowl, GholdengoLunatone => 480
  | CharizardNoctowl, GrimmsnarlFroslass => 397
  | CharizardNoctowl, MegaAbsolBox => 471
  | CharizardNoctowl, Gardevoir => 558
  | CharizardNoctowl, CharizardNoctowl => 487

def matchupAdvantage (a : Archetype6) : Nat :=
  (Archetype6.all.map (matchupWRx10 a)).foldl (· + ·) 0

def lossCountVsOthers (a : Archetype6) : Nat :=
  let opps := Archetype6.all.filter (· != a)
  opps.foldl (fun acc b => if matchupWRx10 a b < 500 then acc + 1 else acc) 0

/-! ## 3. Required insights from the real data -/

def beatsAllOthers (a : Archetype6) : Bool :=
  let opps := Archetype6.all.filter (· != a)
  opps.all (fun b => matchupWRx10 a b > 500)

/-- No deck is dominant; every deck has at least one sub-50 matchup. -/
theorem NO_DOMINANT_DECK : ∀ a : Archetype6, beatsAllOthers a = false := by
  native_decide

/-- Grimmsnarl is checked by Mega Absol in the head-to-head. -/
theorem GRIMMSNARL_LOSES_TO_MEGA_ABSOL :
    matchupWRx10 GrimmsnarlFroslass MegaAbsolBox = 344 := by
  native_decide

/-- Dragapult is the most played deck in this snapshot. -/
theorem DRAGAPULT_MOST_PLAYED :
    ∀ d : Archetype6, metaShareX10 d ≤ metaShareX10 DragapultDusknoir := by
  native_decide

/-- Dragapult loses to four of the other five top decks. -/
theorem DRAGAPULT_LOSES_TO_FOUR_OF_FIVE :
    lossCountVsOthers DragapultDusknoir = 4 := by
  native_decide

/-- Popularity and matchup strength diverge in the real metagame. -/
theorem POPULARITY_NEQ_OPTIMALITY :
    matchupAdvantage MegaAbsolBox > matchupAdvantage DragapultDusknoir := by
  native_decide

/-- Counter-deck value: Mega Absol checks Grimmsnarl despite lower play share. -/
theorem COUNTER_DECK_VALUE :
    matchupWRx10 MegaAbsolBox GrimmsnarlFroslass = 621 ∧
    metaShareX10 MegaAbsolBox < metaShareX10 GrimmsnarlFroslass := by
  native_decide

/-- Gardevoir is the strongest anti-Dragapult pick in the top-6 set. -/
theorem GARDEVOIR_HARD_COUNTERS_DRAGAPULT :
    matchupWRx10 Gardevoir DragapultDusknoir = 627 ∧
    ∀ d : Archetype6, matchupWRx10 d DragapultDusknoir ≤ matchupWRx10 Gardevoir DragapultDusknoir := by
  native_decide

/-- Precomputed Shannon entropy terms (micro-bits) for normalized top-6 shares. -/
def shannonTermMicroBits : Archetype6 → Nat
  | DragapultDusknoir => 530034
  | GholdengoLunatone => 482750
  | GrimmsnarlFroslass => 358607
  | MegaAbsolBox => 354793
  | Gardevoir => 338872
  | CharizardNoctowl => 326195

def observedEntropyTop6MicroBits : Nat :=
  (Archetype6.all.map shannonTermMicroBits).foldl (· + ·) 0

def uniformEntropyTop6MicroBits : Nat := 2584963

/-- The observed top-6 share distribution is less uniform than ideal 1/6. -/
theorem FORMAT_DIVERSITY_SHANNON :
    observedEntropyTop6MicroBits < uniformEntropyTop6MicroBits := by
  native_decide

/-- If Dragapult is banned, Gholdengo becomes the most-played remaining deck,
    and the best counter target shifts accordingly. -/
theorem BAN_DRAGAPULT_META_SHIFTS :
    (∀ d : Archetype6, d ≠ DragapultDusknoir → metaShareX10 d ≤ metaShareX10 GholdengoLunatone) ∧
    (∀ d : Archetype6, matchupWRx10 d DragapultDusknoir ≤ matchupWRx10 Gardevoir DragapultDusknoir) ∧
    (∀ d : Archetype6, d ≠ DragapultDusknoir →
      matchupWRx10 d GholdengoLunatone ≤ matchupWRx10 MegaAbsolBox GholdengoLunatone) := by
  native_decide

/-- From the full 14-deck Trainer Hill matrix: Raging Bolt -> Mega Absol is 67.3%. -/
def ragingBoltVsMegaAbsolX10 : Nat := 673

/-- Real metagame cycle from the full dataset:
    Grimmsnarl > Dragapult, Mega Absol > Grimmsnarl, Raging Bolt > Mega Absol. -/
theorem REAL_METAGAME_CYCLE :
    matchupWRx10 GrimmsnarlFroslass DragapultDusknoir > 500 ∧
    matchupWRx10 MegaAbsolBox GrimmsnarlFroslass > 500 ∧
    ragingBoltVsMegaAbsolX10 > 500 := by
  native_decide

end PokemonLean.MatchupAnalysis
