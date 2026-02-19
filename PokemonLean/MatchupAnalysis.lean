/-
  PokemonLean/MatchupAnalysis.lean -- Full 14-deck Trainer Hill matchup analysis

  Source: Data: Trainer Hill, 2026-01-29 to 2026-02-19, 50+ player tournaments
  Win rates are stored as percentage * 10 (e.g. 627 = 62.7%).
-/
import PokemonLean.RealMetagame

namespace PokemonLean.MatchupAnalysis

abbrev Deck := PokemonLean.RealMetagame.Deck
abbrev matchupWRx10 : Deck → Deck → Nat := PokemonLean.RealMetagame.matchupWR
abbrev metaShareX10 : Deck → Nat := PokemonLean.RealMetagame.metaShare

open PokemonLean.RealMetagame.Deck

def dataSource : String :=
  "Data: Trainer Hill, 2026-01-29 to 2026-02-19, 50+ player tournaments"

def allDecks : List Deck := PokemonLean.RealMetagame.Deck.all

def nonMirrorOpps (d : Deck) : List Deck :=
  allDecks.filter (fun opp => opp != d)

def losingMatchupCount (d : Deck) : Nat :=
  (nonMirrorOpps d).foldl (fun acc opp => if matchupWRx10 d opp < 500 then acc + 1 else acc) 0

def isDominant (d : Deck) : Bool :=
  (nonMirrorOpps d).all (fun opp => matchupWRx10 d opp > 500)

def totalMetaShareX10 : Nat :=
  (allDecks.map metaShareX10).foldl (· + ·) 0

def metaShareWithoutDragapult : Deck → Nat
  | .DragapultDusknoir => 0
  | d => metaShareX10 d

def totalMetaShareWithoutDragapultX10 : Nat :=
  (allDecks.map metaShareWithoutDragapult).foldl (· + ·) 0

def weightedWRNumerator (d : Deck) : Nat :=
  (allDecks.map (fun opp => matchupWRx10 d opp * metaShareX10 opp)).foldl (· + ·) 0

def weightedWRWithoutDragapultNumerator (d : Deck) : Nat :=
  (allDecks.map (fun opp => matchupWRx10 d opp * metaShareWithoutDragapult opp)).foldl (· + ·) 0

def weightedWRx10VsField (d : Deck) : Nat :=
  weightedWRNumerator d / totalMetaShareX10

def weightedWRx10VsFieldWithoutDragapult (d : Deck) : Nat :=
  weightedWRWithoutDragapultNumerator d / totalMetaShareWithoutDragapultX10

def nonMirrorWRSum (d : Deck) : Nat :=
  (nonMirrorOpps d).foldl (fun acc opp => acc + matchupWRx10 d opp) 0

def averageNonMirrorWRx10 (d : Deck) : Nat :=
  nonMirrorWRSum d / 13

inductive Tier where
  | S
  | A
  | B
  | C
  deriving DecidableEq, Repr, Inhabited

def tierOf (d : Deck) : Tier :=
  let wr := averageNonMirrorWRx10 d
  if wr >= 520 then Tier.S
  else if wr >= 490 then Tier.A
  else if wr >= 460 then Tier.B
  else Tier.C

def sTier : List Deck := allDecks.filter (fun d => tierOf d = Tier.S)
def aTier : List Deck := allDecks.filter (fun d => tierOf d = Tier.A)
def bTier : List Deck := allDecks.filter (fun d => tierOf d = Tier.B)
def cTier : List Deck := allDecks.filter (fun d => tierOf d = Tier.C)

/-- Precomputed Shannon entropy terms (micro-bits) for normalized top-14 shares. -/
def shannonTermMicroBits : Deck → Nat
  | .DragapultDusknoir    => 482785
  | .GholdengoLunatone    => 400489
  | .GrimssnarlFroslass   => 276533
  | .MegaAbsolBox         => 273166
  | .Gardevoir            => 259275
  | .CharizardNoctowl     => 248386
  | .GardevoirJellicent   => 244661
  | .CharizardPidgeot     => 217130
  | .DragapultCharizard   => 217130
  | .RagingBoltOgerpon    => 208753
  | .NsZoroark            => 195711
  | .AlakazamDudunsparce  => 186674
  | .KangaskhanBouffalant => 172554
  | .Ceruledge            => 162731

def observedEntropyTop14MicroBits : Nat :=
  (allDecks.map shannonTermMicroBits).foldl (· + ·) 0

def uniformEntropyTop14MicroBits : Nat := 3807355

/-- 14-deck universe is exactly the Trainer Hill full matrix from RealMetagame. -/
theorem FULL_14_DECK_UNIVERSE : allDecks.length = 14 := by
  native_decide

/-- 1) No dominant deck across all 14 (every deck has at least one losing matchup). -/
theorem NO_DOMINANT_DECK_ACROSS_14 :
    (allDecks.all (fun d => isDominant d = false)) = true := by
  native_decide

/-- 2) Dragapult popularity paradox: 15.5% share with 9 losing non-mirror matchups. -/
theorem DRAGAPULT_POPULARITY_PARADOX :
    metaShareX10 DragapultDusknoir = 155 ∧
    (nonMirrorOpps DragapultDusknoir).length = 13 ∧
    losingMatchupCount DragapultDusknoir = 9 ∧
    losingMatchupCount DragapultDusknoir >= 9 := by
  native_decide

/-- 3) Counter deck value: Raging Bolt is the best anti-Mega Absol counter at 67.3%. -/
theorem RAGING_BOLT_COUNTER_VALUE :
    matchupWRx10 RagingBoltOgerpon MegaAbsolBox = 673 ∧
    (allDecks.filter (fun d => d != MegaAbsolBox)).all
      (fun d => matchupWRx10 d MegaAbsolBox <= matchupWRx10 RagingBoltOgerpon MegaAbsolBox) = true := by
  native_decide

/-- 4) Mega Absol counters Grimssnarl at 62.1%. -/
theorem MEGA_ABSOL_COUNTERS_GRIMSSNARL :
    matchupWRx10 MegaAbsolBox GrimssnarlFroslass = 621 := by
  native_decide

/-- 5) Gardevoir counters Dragapult at 62.7%. -/
theorem GARDEVOIR_COUNTERS_DRAGAPULT :
    matchupWRx10 Gardevoir DragapultDusknoir = 627 := by
  native_decide

/-- 6) Alakazam is a Gholdengo tech (58.8%) against the #2 most played deck. -/
theorem ALAKAZAM_IS_GHOLDENGO_TECH :
    matchupWRx10 AlakazamDudunsparce GholdengoLunatone = 588 ∧
    metaShareX10 GholdengoLunatone = 99 ∧
    (allDecks.filter (fun d => d != DragapultDusknoir)).all
      (fun d => metaShareX10 d <= metaShareX10 GholdengoLunatone) = true := by
  native_decide

/-- 7) Kangaskhan rogue value against top decks. -/
theorem KANGASKHAN_ROGUE_VALUE :
    matchupWRx10 KangaskhanBouffalant CharizardNoctowl = 635 ∧
    matchupWRx10 KangaskhanBouffalant DragapultDusknoir = 582 := by
  native_decide

/-- 8) Format diversity: observed Shannon entropy is below uniform over 14 decks. -/
theorem FORMAT_DIVERSITY_SHANNON :
    observedEntropyTop14MicroBits < uniformEntropyTop14MicroBits := by
  native_decide

/-- 9) Ceruledge is worst-positioned by losing-count (tied highest at 10 losses). -/
theorem CERULEDGE_WORST_POSITIONED :
    losingMatchupCount Ceruledge = 10 ∧
    (allDecks.all (fun d => losingMatchupCount d <= losingMatchupCount Ceruledge)) = true := by
  native_decide

/-- 10) Full metagame cycle: Grimm > Drag > CharNoc > GardJell > Gard > DragDusk. -/
theorem FULL_METAGAME_CYCLE :
    matchupWRx10 GrimssnarlFroslass DragapultDusknoir > 500 ∧
    matchupWRx10 DragapultDusknoir CharizardNoctowl > 500 ∧
    matchupWRx10 CharizardNoctowl GardevoirJellicent > 500 ∧
    matchupWRx10 GardevoirJellicent Gardevoir > 500 ∧
    matchupWRx10 Gardevoir DragapultDusknoir > 500 := by
  native_decide

/-- 11) Ban analysis: removing Dragapult changes weighted field win rates. -/
theorem BAN_ANALYSIS_WEIGHTED_WR_SHIFT :
    totalMetaShareX10 = 695 ∧
    totalMetaShareWithoutDragapultX10 = 540 ∧
    weightedWRx10VsField CharizardNoctowl = 457 ∧
    weightedWRx10VsFieldWithoutDragapult CharizardNoctowl = 495 ∧
    weightedWRx10VsField Gardevoir = 498 ∧
    weightedWRx10VsFieldWithoutDragapult Gardevoir = 461 ∧
    weightedWRx10VsField MegaAbsolBox = 517 ∧
    weightedWRx10VsFieldWithoutDragapult MegaAbsolBox = 500 := by
  native_decide

theorem BAN_ANALYSIS_REORDERS_WEIGHTED_RANKS :
    weightedWRx10VsField Gardevoir > weightedWRx10VsField CharizardNoctowl ∧
    weightedWRx10VsFieldWithoutDragapult CharizardNoctowl >
      weightedWRx10VsFieldWithoutDragapult Gardevoir := by
  native_decide

/-- 12) Tier classification by average non-mirror WR (x10 scale). -/
theorem TIER_CLASSIFICATION :
    sTier = [GrimssnarlFroslass] ∧
    aTier = [MegaAbsolBox, DragapultCharizard] ∧
    bTier = [DragapultDusknoir, GholdengoLunatone, Gardevoir, CharizardNoctowl,
      GardevoirJellicent, CharizardPidgeot, RagingBoltOgerpon,
      AlakazamDudunsparce, KangaskhanBouffalant] ∧
    cTier = [NsZoroark, Ceruledge] := by
  native_decide

end PokemonLean.MatchupAnalysis
