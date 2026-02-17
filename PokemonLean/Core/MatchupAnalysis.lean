/-
  PokemonLean / Core / MatchupAnalysis.lean

  Deck matchup and win-rate analysis for competitive formats.
  Self-contained module with explicit matchup matrix semantics,
  favorable/unfavorable/even classification, RPS dynamics,
  counter-tech tradeoffs, and field-distribution EV calculations.

  All proofs are sorry-free.
-/

set_option linter.unusedVariables false

namespace PokemonLean.Core.MatchupAnalysis

-- ============================================================
-- §1  Core deck and win-rate types
-- ============================================================

abbrev WinRate := Nat

/-- Competitive deck families used in this module. -/
inductive Deck where
  | aggro
  | control
  | combo
  | midrange
  | toolbox
  | stall
  deriving DecidableEq, Repr, BEq, Inhabited

def allDecks : List Deck :=
  [.aggro, .control, .combo, .midrange, .toolbox, .stall]

def deckCount : Nat := 6

theorem allDecks_length : allDecks.length = deckCount := by native_decide
theorem aggro_in_allDecks : Deck.aggro ∈ allDecks := by simp [allDecks]
theorem control_in_allDecks : Deck.control ∈ allDecks := by simp [allDecks]
theorem combo_in_allDecks : Deck.combo ∈ allDecks := by simp [allDecks]
theorem midrange_in_allDecks : Deck.midrange ∈ allDecks := by simp [allDecks]
theorem toolbox_in_allDecks : Deck.toolbox ∈ allDecks := by simp [allDecks]
theorem stall_in_allDecks : Deck.stall ∈ allDecks := by simp [allDecks]

-- ============================================================
-- §2  Rate classification
-- ============================================================

def mirrorRate : WinRate := 50
def favorableThreshold : WinRate := 55
def unfavorableThreshold : WinRate := 45

/-- Favorable matchup: strictly above 55%. -/
def favorable (r : WinRate) : Bool := r > favorableThreshold

/-- Unfavorable matchup: strictly below 45%. -/
def unfavorable (r : WinRate) : Bool := r < unfavorableThreshold

/-- Even matchup: inclusive 45% to 55%. -/
def evenMatchup (r : WinRate) : Bool :=
  unfavorableThreshold ≤ r && r ≤ favorableThreshold

/-- Complementary rate in a zero-sum matchup. -/
def complement (p : WinRate) : WinRate := 100 - p

theorem mirrorRate_eq_50 : mirrorRate = 50 := rfl
theorem favorable_60 : favorable 60 = true := by native_decide
theorem favorable_55_false : favorable 55 = false := by native_decide
theorem unfavorable_40 : unfavorable 40 = true := by native_decide
theorem unfavorable_45_false : unfavorable 45 = false := by native_decide
theorem even_45 : evenMatchup 45 = true := by native_decide
theorem even_50 : evenMatchup 50 = true := by native_decide
theorem even_55 : evenMatchup 55 = true := by native_decide
theorem even_44_false : evenMatchup 44 = false := by native_decide
theorem even_56_false : evenMatchup 56 = false := by native_decide

theorem complement_sum_100 (p : Nat) (hp : p ≤ 100) :
    p + complement p = 100 := by
  simpa [complement] using Nat.add_sub_of_le hp

theorem complement_of_40 : complement 40 = 60 := by native_decide
theorem complement_of_50 : complement 50 = 50 := by native_decide
theorem complement_of_60 : complement 60 = 40 := by native_decide

-- ============================================================
-- §3  Rock-paper-scissors relations
-- ============================================================

/-- Directed matchup edge: `beats a b` means `a` is advantaged over `b`. -/
def beats : Deck → Deck → Bool
  | .aggro,   .control => true
  | .control, .combo   => true
  | .combo,   .aggro   => true
  | .midrange, .toolbox => true
  | .toolbox, .stall    => true
  | .stall,   .midrange => true
  | _, _ => false

theorem beats_aggro_control : beats .aggro .control = true := rfl
theorem beats_control_combo : beats .control .combo = true := rfl
theorem beats_combo_aggro : beats .combo .aggro = true := rfl
theorem beats_midrange_toolbox : beats .midrange .toolbox = true := rfl
theorem beats_toolbox_stall : beats .toolbox .stall = true := rfl
theorem beats_stall_midrange : beats .stall .midrange = true := rfl

theorem beats_not_reflexive (d : Deck) : beats d d = false := by
  cases d <;> rfl

theorem beats_aggro_combo_false : beats .aggro .combo = false := rfl
theorem beats_control_aggro_false : beats .control .aggro = false := rfl
theorem beats_combo_control_false : beats .combo .control = false := rfl

/-- A healthy format has at least one RPS cycle. -/
def hasRPSCycle : Prop :=
  ∃ a b c : Deck, beats a b = true ∧ beats b c = true ∧ beats c a = true

theorem rps_cycle_core_exists : hasRPSCycle := by
  refine ⟨.aggro, .control, .combo, ?_, ?_, ?_⟩ <;> rfl

theorem rps_cycle_secondary_exists : hasRPSCycle := by
  refine ⟨.midrange, .toolbox, .stall, ?_, ?_, ?_⟩ <;> rfl

-- ============================================================
-- §4  Matchup matrix and rates
-- ============================================================

/-- Standard matrix rate:
    - mirror = 50
    - advantaged edge = 60
    - disadvantaged edge = 40
    - unrelated pairing = 50
-/
def matchupRate (a b : Deck) : WinRate :=
  if a == b then 50
  else if beats a b then 60
  else if beats b a then 40
  else 50

structure MatchupMatrix where
  rate : Deck → Deck → WinRate

def standardMatrix : MatchupMatrix := ⟨matchupRate⟩

def MatchupMatrix.mirrorCorrect (m : MatchupMatrix) : Prop :=
  ∀ d : Deck, m.rate d d = mirrorRate

def MatchupMatrix.antisymmetric (m : MatchupMatrix) : Prop :=
  ∀ a b : Deck, m.rate a b + m.rate b a = 100

theorem matrix_uses_matchupRate (a b : Deck) :
    standardMatrix.rate a b = matchupRate a b := rfl

theorem matchup_mirror (d : Deck) : matchupRate d d = 50 := by
  cases d <;> rfl

theorem mirror_match_exactly_50 (d : Deck) : matchupRate d d = mirrorRate := by
  simpa [mirrorRate] using matchup_mirror d

theorem matchup_aggro_control : matchupRate .aggro .control = 60 := by rfl
theorem matchup_control_aggro : matchupRate .control .aggro = 40 := by rfl
theorem matchup_control_combo : matchupRate .control .combo = 60 := by rfl
theorem matchup_combo_control : matchupRate .combo .control = 40 := by rfl
theorem matchup_combo_aggro : matchupRate .combo .aggro = 60 := by rfl
theorem matchup_aggro_combo : matchupRate .aggro .combo = 40 := by rfl
theorem matchup_midrange_toolbox : matchupRate .midrange .toolbox = 60 := by rfl
theorem matchup_toolbox_midrange : matchupRate .toolbox .midrange = 40 := by rfl
theorem matchup_toolbox_stall : matchupRate .toolbox .stall = 60 := by rfl
theorem matchup_stall_toolbox : matchupRate .stall .toolbox = 40 := by rfl
theorem matchup_stall_midrange : matchupRate .stall .midrange = 60 := by rfl
theorem matchup_midrange_stall : matchupRate .midrange .stall = 40 := by rfl

theorem matchup_unrelated_is_even :
    matchupRate .aggro .toolbox = 50 := by rfl

theorem matchup_values_bounded (a b : Deck) :
    matchupRate a b ≤ 100 := by
  cases a <;> cases b <;> native_decide

theorem matchup_values_nonzero (a b : Deck) :
    matchupRate a b > 0 := by
  cases a <;> cases b <;> native_decide

theorem matchup_sum_100 (a b : Deck) :
    matchupRate a b + matchupRate b a = 100 := by
  cases a <;> cases b <;> native_decide

theorem standard_matrix_mirror_correct :
    standardMatrix.mirrorCorrect := by
  intro d
  simpa [MatchupMatrix.mirrorCorrect, standardMatrix, mirrorRate] using matchup_mirror d

theorem standard_matrix_antisymmetric :
    standardMatrix.antisymmetric := by
  intro a b
  simpa [MatchupMatrix.antisymmetric, standardMatrix] using matchup_sum_100 a b

theorem favorable_for_A_eq_unfavorable_for_B (a b : Deck) :
    favorable (matchupRate a b) = unfavorable (matchupRate b a) := by
  cases a <;> cases b <;> native_decide

theorem unfavorable_for_A_eq_favorable_for_B (a b : Deck) :
    unfavorable (matchupRate a b) = favorable (matchupRate b a) := by
  cases a <;> cases b <;> native_decide

theorem even_matchup_symmetric (a b : Deck) :
    evenMatchup (matchupRate a b) = evenMatchup (matchupRate b a) := by
  cases a <;> cases b <;> native_decide

theorem matchup_classification_complete (a b : Deck) :
    favorable (matchupRate a b) = true ∨
    unfavorable (matchupRate a b) = true ∨
    evenMatchup (matchupRate a b) = true := by
  cases a <;> cases b <;> native_decide

theorem favorable_implies_not_even_on_matrix (a b : Deck) :
    favorable (matchupRate a b) = true → evenMatchup (matchupRate a b) = false := by
  cases a <;> cases b <;> native_decide

theorem unfavorable_implies_not_even_on_matrix (a b : Deck) :
    unfavorable (matchupRate a b) = true → evenMatchup (matchupRate a b) = false := by
  cases a <;> cases b <;> native_decide

-- ============================================================
-- §5  RPS consequences
-- ============================================================

/-- No deck has advantage over itself. -/
theorem no_self_advantage (d : Deck) : beats d d = false := beats_not_reflexive d

/-- No deck can beat every deck in this relation (self-edge already fails). -/
theorem no_deck_beats_everything :
    ¬ ∃ d : Deck, ∀ x : Deck, beats d x = true := by
  intro h
  rcases h with ⟨d, hd⟩
  have hself : beats d d = true := hd d
  cases d <;> simp [beats] at hself

/-- If an RPS cycle exists, no single deck beats everything. -/
theorem no_deck_beats_everything_if_rps (_h : hasRPSCycle) :
    ¬ ∃ d : Deck, ∀ x : Deck, beats d x = true :=
  no_deck_beats_everything

theorem rps_cycle_gives_three_distinct_edges :
    ∃ a b c : Deck, beats a b = true ∧ beats b c = true ∧ beats c a = true :=
  rps_cycle_core_exists

theorem healthy_format_has_rps_cycle : hasRPSCycle := rps_cycle_core_exists

-- ============================================================
-- §6  Counter-teching model
-- ============================================================

structure CounterTech where
  name : String
  targetMatchup : Deck
  improvement : Nat
  collateralCost : Nat
  deriving Repr

/-- Improve one matchup, capped at 100. -/
def applyTech (base : WinRate) (tech : CounterTech) : WinRate :=
  min (base + tech.improvement) 100

/-- Collateral consistency cost can reduce other matchup rates. -/
def applyCollateral (base : WinRate) (tech : CounterTech) : WinRate :=
  base - tech.collateralCost

def antiComboPackage : CounterTech :=
  ⟨"Anti-Combo Package", .combo, 20, 8⟩

def antiControlPackage : CounterTech :=
  ⟨"Anti-Control Package", .control, 15, 5⟩

def aggroVsComboAfterTech : WinRate :=
  applyTech (matchupRate .aggro .combo) antiComboPackage

def aggroVsControlAfterTech : WinRate :=
  applyCollateral (matchupRate .aggro .control) antiComboPackage

theorem applyTech_le_100 (base : WinRate) (tech : CounterTech) :
    applyTech base tech ≤ 100 := by
  exact Nat.min_le_right (base + tech.improvement) 100

theorem applyTech_preserves_if_under_cap
    (base : WinRate) (tech : CounterTech) (h : base + tech.improvement ≤ 100) :
    applyTech base tech = base + tech.improvement := by
  simp [applyTech, Nat.min_eq_left h]

theorem applyTech_caps_if_overflow
    (base : WinRate) (tech : CounterTech) (h : 100 ≤ base + tech.improvement) :
    applyTech base tech = 100 := by
  simp [applyTech, Nat.min_eq_right h]

theorem anti_combo_improves_specific_matchup :
    aggroVsComboAfterTech > matchupRate .aggro .combo := by
  native_decide

theorem anti_combo_may_worsen_other_matchups :
    aggroVsControlAfterTech < matchupRate .aggro .control := by
  native_decide

theorem counter_tech_tradeoff_exists :
    aggroVsComboAfterTech > matchupRate .aggro .combo ∧
    aggroVsControlAfterTech < matchupRate .aggro .control := by
  constructor
  · exact anti_combo_improves_specific_matchup
  · exact anti_combo_may_worsen_other_matchups

theorem anti_control_package_improves_control_target :
    applyTech (matchupRate .combo .control) antiControlPackage >
    matchupRate .combo .control := by
  native_decide

-- ============================================================
-- §7  Tournament field distribution and expectation
-- ============================================================

structure FieldShare where
  deck : Deck
  pct  : Nat
  deriving Repr, DecidableEq

structure FieldDist where
  shares : List FieldShare
  deriving Repr

def FieldDist.total (f : FieldDist) : Nat :=
  f.shares.foldl (fun acc e => acc + e.pct) 0

def FieldDist.valid (f : FieldDist) : Prop :=
  f.total = 100

def weightedContribution (myDeck : Deck) (entry : FieldShare) : Nat :=
  matchupRate myDeck entry.deck * entry.pct

def expectedRaw (myDeck : Deck) (f : FieldDist) : Nat :=
  f.shares.foldl (fun acc e => acc + weightedContribution myDeck e) 0

/-- Integer expected win rate percentage. -/
def expectedWinRate (myDeck : Deck) (f : FieldDist) : Nat :=
  expectedRaw myDeck f / 100

def controlHeavyField : FieldDist :=
  ⟨[⟨.control, 70⟩, ⟨.combo, 30⟩]⟩

def comboHeavyField : FieldDist :=
  ⟨[⟨.control, 30⟩, ⟨.combo, 70⟩]⟩

def mirrorOnlyAggroField : FieldDist :=
  ⟨[⟨.aggro, 100⟩]⟩

theorem controlHeavy_total : controlHeavyField.total = 100 := by native_decide
theorem comboHeavy_total : comboHeavyField.total = 100 := by native_decide
theorem mirrorOnly_total : mirrorOnlyAggroField.total = 100 := by native_decide

theorem weightedContribution_zero_share (d : Deck) :
    weightedContribution d ⟨.combo, 0⟩ = 0 := by
  simp [weightedContribution]

theorem expected_empty_field_zero (d : Deck) :
    expectedRaw d ⟨[]⟩ = 0 := by
  simp [expectedRaw]

theorem expected_single_full_share (a b : Deck) :
    expectedWinRate a ⟨[⟨b, 100⟩]⟩ = matchupRate a b := by
  simp [expectedWinRate, expectedRaw, weightedContribution]

theorem mirror_field_expected_is_50 :
    expectedWinRate .aggro mirrorOnlyAggroField = 50 := by
  native_decide

theorem aggro_expected_controlHeavy :
    expectedWinRate .aggro controlHeavyField = 54 := by
  native_decide

theorem aggro_expected_comboHeavy :
    expectedWinRate .aggro comboHeavyField = 46 := by
  native_decide

theorem expected_depends_on_field_distribution :
    expectedWinRate .aggro controlHeavyField ≠ expectedWinRate .aggro comboHeavyField := by
  native_decide

theorem expected_control_in_controlHeavy :
    expectedWinRate .control controlHeavyField = 53 := by
  native_decide

theorem expected_combo_in_controlHeavy :
    expectedWinRate .combo controlHeavyField = 43 := by
  native_decide

theorem expected_control_vs_combo_relation :
    expectedWinRate .control controlHeavyField >
    expectedWinRate .combo controlHeavyField := by
  native_decide

-- ============================================================
-- §8  Additional symmetry and utility theorems
-- ============================================================

theorem favorable_control_vs_combo :
    favorable (matchupRate .control .combo) = true := by native_decide

theorem unfavorable_combo_vs_control :
    unfavorable (matchupRate .combo .control) = true := by native_decide

theorem even_aggro_vs_toolbox :
    evenMatchup (matchupRate .aggro .toolbox) = true := by native_decide

theorem zero_sum_determines_opponent (a b : Deck) :
    matchupRate a b = 100 - matchupRate b a := by
  cases a <;> cases b <;> native_decide

theorem complement_of_matchup_is_opponent (a b : Deck) :
    complement (matchupRate a b) = matchupRate b a := by
  cases a <;> cases b <;> native_decide

theorem favorable_threshold_strict :
    favorableThreshold = 55 := rfl

theorem unfavorable_threshold_strict :
    unfavorableThreshold = 45 := rfl

theorem mirror_is_even :
    evenMatchup mirrorRate = true := by native_decide

theorem favorable_not_unfavorable_on_matrix (a b : Deck) :
    favorable (matchupRate a b) = true →
    unfavorable (matchupRate a b) = false := by
  cases a <;> cases b <;> native_decide

theorem unfavorable_not_favorable_on_matrix (a b : Deck) :
    unfavorable (matchupRate a b) = true →
    favorable (matchupRate a b) = false := by
  cases a <;> cases b <;> native_decide

theorem matchup_rate_is_40_50_or_60 (a b : Deck) :
    matchupRate a b = 40 ∨ matchupRate a b = 50 ∨ matchupRate a b = 60 := by
  cases a <;> cases b <;> native_decide

theorem expected_mirror_equals_mirrorRate (d : Deck) :
    expectedWinRate d ⟨[⟨d, 100⟩]⟩ = mirrorRate := by
  cases d <;> native_decide

theorem healthy_format_statement :
    hasRPSCycle ∧ ¬ (∃ d : Deck, ∀ x : Deck, beats d x = true) := by
  constructor
  · exact healthy_format_has_rps_cycle
  · exact no_deck_beats_everything

end PokemonLean.Core.MatchupAnalysis
