/-
  PokemonLean / Core / ResourceManagement.lean

  Formalization of in-game resource management in the Pokémon TCG.
  Tracks hand, deck, bench, energy, prizes, card economy, tempo,
  denial effects, depletion bounds, and mirror-resource parity.

  All proofs are sorry-free.
-/

set_option linter.unusedVariables false

namespace PokemonLean.Core.ResourceManagement

-- ============================================================
-- §1  Core resource state
-- ============================================================

structure Resources where
  handSize        : Nat
  deckSize        : Nat
  benchCount      : Nat
  energyInPlay    : Nat
  prizesRemaining : Nat
  deriving DecidableEq, Repr

def maxDeckSize : Nat := 60
def maxBenchSize : Nat := 5
def startingPrizes : Nat := 6

def initialResources : Resources :=
  { handSize := 7
    deckSize := maxDeckSize
    benchCount := 0
    energyInPlay := 0
    prizesRemaining := startingPrizes }

def validResources (r : Resources) : Prop :=
  r.deckSize ≤ maxDeckSize ∧
  r.benchCount ≤ maxBenchSize ∧
  r.prizesRemaining ≤ startingPrizes

theorem initial_hand_is_7 : initialResources.handSize = 7 := rfl
theorem initial_deck_is_60 : initialResources.deckSize = 60 := rfl
theorem initial_bench_is_0 : initialResources.benchCount = 0 := rfl
theorem initial_energy_is_0 : initialResources.energyInPlay = 0 := rfl
theorem initial_prizes_is_6 : initialResources.prizesRemaining = 6 := rfl

theorem initial_resources_valid : validResources initialResources := by
  constructor
  · decide
  constructor
  · decide
  · decide

-- ============================================================
-- §2  Primitive actions
-- ============================================================

/-- Draw one card if possible; if deck is empty, nothing changes. -/
def drawCard (r : Resources) : Resources :=
  if r.deckSize = 0 then r
  else
    { r with
      handSize := r.handSize + 1
      deckSize := r.deckSize - 1 }

/-- Play one card from hand. -/
def playCard (r : Resources) : Resources :=
  { r with handSize := r.handSize - 1 }

/-- Play a Basic to bench if room exists; costs one hand card. -/
def benchBasic (r : Resources) : Resources :=
  if r.benchCount < maxBenchSize then
    { r with handSize := r.handSize - 1, benchCount := r.benchCount + 1 }
  else r

/-- Attach one energy from hand to board. -/
def attachEnergy (r : Resources) : Resources :=
  { r with handSize := r.handSize - 1, energyInPlay := r.energyInPlay + 1 }

/-- Take one prize card (adds one card to hand). -/
def takePrize (r : Resources) : Resources :=
  { r with prizesRemaining := r.prizesRemaining - 1, handSize := r.handSize + 1 }

/-- Knock out can remove attached energy from board. -/
def applyKO (r : Resources) (energyLost : Nat) : Resources :=
  { r with energyInPlay := r.energyInPlay - energyLost }

theorem draw_from_empty_unchanged (r : Resources) (h : r.deckSize = 0) :
    drawCard r = r := by simp [drawCard, h]

theorem draw_increases_hand (r : Resources) (h : r.deckSize > 0) :
    (drawCard r).handSize = r.handSize + 1 := by
  simp [drawCard, Nat.ne_of_gt h]

theorem draw_decreases_deck (r : Resources) (h : r.deckSize > 0) :
    (drawCard r).deckSize = r.deckSize - 1 := by
  simp [drawCard, Nat.ne_of_gt h]

theorem draw_keeps_bench (r : Resources) : (drawCard r).benchCount = r.benchCount := by
  by_cases h : r.deckSize = 0
  · simp [drawCard, h]
  · simp [drawCard, h]

theorem play_decreases_hand_by_one (r : Resources) :
    (playCard r).handSize = r.handSize - 1 := rfl

theorem play_decreases_hand_strict (r : Resources) (h : r.handSize > 0) :
    (playCard r).handSize < r.handSize := by
  have hsub : r.handSize - 1 < r.handSize := Nat.sub_lt h (by decide)
  simpa [playCard] using hsub

theorem attach_increases_energy (r : Resources) :
    (attachEnergy r).energyInPlay = r.energyInPlay + 1 := rfl

theorem attach_uses_hand (r : Resources) :
    (attachEnergy r).handSize = r.handSize - 1 := rfl

theorem prize_reduces_prizes (r : Resources) :
    (takePrize r).prizesRemaining = r.prizesRemaining - 1 := rfl

theorem prize_increases_hand (r : Resources) :
    (takePrize r).handSize = r.handSize + 1 := rfl

theorem ko_can_reduce_energy (r : Resources) (n : Nat) :
    (applyKO r n).energyInPlay = r.energyInPlay - n := rfl

theorem ko_never_increases_energy (r : Resources) (n : Nat) :
    (applyKO r n).energyInPlay ≤ r.energyInPlay := by
  simp [applyKO]

-- ============================================================
-- §3  Card advantage and options
-- ============================================================

def cardAdvantage (mine opp : Resources) : Int :=
  Int.ofNat mine.handSize - Int.ofNat opp.handSize

def optionCount (r : Resources) : Nat :=
  r.handSize + (maxBenchSize - r.benchCount) + r.energyInPlay

def hasMoreOptions (mine opp : Resources) : Bool :=
  optionCount mine > optionCount opp

def netCardAdvantage (draws plays : Nat) : Int :=
  Int.ofNat draws - Int.ofNat plays

def handAfterSequence (start draws plays : Nat) : Nat :=
  start + draws - plays

theorem net_card_advantage_formula (draws plays : Nat) :
    netCardAdvantage draws plays = Int.ofNat draws - Int.ofNat plays := rfl

theorem hand_after_sequence_formula (start draws plays : Nat) :
    handAfterSequence start draws plays = start + draws - plays := rfl

theorem draw_adds_one_option (r : Resources) (h : r.deckSize > 0) :
    optionCount (drawCard r) = optionCount r + 1 := by
  simp [optionCount, drawCard, Nat.ne_of_gt h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem play_reduces_options_when_hand_positive (r : Resources) (h : r.handSize > 0) :
    optionCount (playCard r) < optionCount r := by
  have hsub : r.handSize - 1 < r.handSize := Nat.sub_lt h (by decide)
  have hmono :
      (r.handSize - 1) + (maxBenchSize - r.benchCount) + r.energyInPlay <
      r.handSize + (maxBenchSize - r.benchCount) + r.energyInPlay := by
    exact Nat.add_lt_add_right (Nat.add_lt_add_right hsub (maxBenchSize - r.benchCount)) r.energyInPlay
  simpa [optionCount, playCard, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmono

theorem equal_hands_zero_card_advantage (a b : Resources) (h : a.handSize = b.handSize) :
    cardAdvantage a b = 0 := by
  simp [cardAdvantage, h]

theorem card_advantage_reflexive_zero (r : Resources) :
    cardAdvantage r r = 0 := by
  simp [cardAdvantage]

theorem net_card_advantage_draw3_play1 :
    netCardAdvantage 3 1 = 2 := by native_decide

theorem net_card_advantage_draw2_play2 :
    netCardAdvantage 2 2 = 0 := by native_decide

theorem net_card_advantage_draw1_play3 :
    netCardAdvantage 1 3 = -2 := by native_decide

-- ============================================================
-- §4  Tempo and board development
-- ============================================================

structure TempoState where
  boardDevelopment : Nat
  turnsElapsed     : Nat
  deriving DecidableEq, Repr

/-- Development rate in integer points per turn (0 if no turns elapsed). -/
def developmentRate (t : TempoState) : Nat :=
  if t.turnsElapsed = 0 then 0 else t.boardDevelopment / t.turnsElapsed

def hasTempoAdvantage (mine opp : TempoState) : Bool :=
  decide (developmentRate mine > developmentRate opp)

theorem development_rate_zero_turns (n : Nat) :
    developmentRate ⟨n, 0⟩ = 0 := by simp [developmentRate]

theorem development_rate_exact_div (n : Nat) :
    developmentRate ⟨2 * n, 2⟩ = n := by
  simp [developmentRate]

theorem tempo_advantage_is_rate_comparison (a b : TempoState) :
    hasTempoAdvantage a b = decide (developmentRate a > developmentRate b) := rfl

theorem tempo_advantage_sample_true :
    hasTempoAdvantage ⟨12, 3⟩ ⟨8, 3⟩ = true := by native_decide

theorem tempo_advantage_sample_false :
    hasTempoAdvantage ⟨6, 3⟩ ⟨12, 3⟩ = false := by native_decide

theorem equal_rate_no_tempo_advantage (a b : TempoState)
    (h : developmentRate a = developmentRate b) :
    hasTempoAdvantage a b = false := by
  simp [hasTempoAdvantage, h]

-- ============================================================
-- §5  Card economy (draw supporters and abilities)
-- ============================================================

def playDrawSupporter (r : Resources) (drawAmount : Nat) : Resources :=
  { r with handSize := r.handSize - 1 + drawAmount, deckSize := r.deckSize - drawAmount }

def useDrawAbility (r : Resources) (drawAmount : Nat) : Resources :=
  { r with handSize := r.handSize + drawAmount, deckSize := r.deckSize - drawAmount }

theorem supporter_net_cards (r : Resources) (n : Nat) :
    (playDrawSupporter r n).handSize = r.handSize - 1 + n := rfl

theorem ability_net_cards (r : Resources) (n : Nat) :
    (useDrawAbility r n).handSize = r.handSize + n := rfl

theorem draw_supporter_increases_hand_if_two_plus (r : Resources) (h : r.handSize > 0) :
    (playDrawSupporter r 2).handSize > r.handSize - 1 := by
  simp [playDrawSupporter]

theorem draw_ability_increases_hand (r : Resources) :
    (useDrawAbility r 1).handSize = r.handSize + 1 := by
  simp [useDrawAbility]

theorem economy_draw3_vs_draw1 :
    (useDrawAbility initialResources 3).handSize >
    (useDrawAbility initialResources 1).handSize := by
  native_decide

theorem supporter_draw3_example :
    (playDrawSupporter initialResources 3).handSize = 9 := by
  native_decide

-- ============================================================
-- §6  Resource denial (N / Iono / Judge)
-- ============================================================

inductive DenialCard where
  | n
  | iono
  | judge
  deriving DecidableEq, Repr

def applyN (oppHand oppPrizes : Nat) : Nat :=
  min oppHand oppPrizes

def applyIono (oppHand oppPrizes : Nat) : Nat :=
  min oppHand oppPrizes

def applyJudge (oppHand : Nat) : Nat :=
  min oppHand 4

def denialEffective (before after : Nat) : Bool :=
  after < before

theorem judge_caps_at_four (h : Nat) : applyJudge h ≤ 4 := by
  exact Nat.min_le_right h 4

theorem judge_large_hand_hits_four (h : Nat) (hh : h > 4) :
    applyJudge h = 4 := by
  exact Nat.min_eq_right (Nat.le_of_lt hh)

theorem judge_effective_when_hand_large (h : Nat) (hh : h > 4) :
    denialEffective h (applyJudge h) = true := by
  have hfour : applyJudge h = 4 := judge_large_hand_hits_four h hh
  simp [denialEffective, hfour, hh]

theorem judge_not_effective_at_four :
    denialEffective 4 (applyJudge 4) = false := by
  native_decide

theorem n_reduces_large_hand (hand prizes : Nat) (hhand : hand > prizes) :
    applyN hand prizes = prizes := by
  exact Nat.min_eq_right (Nat.le_of_lt hhand)

theorem iono_reduces_large_hand (hand prizes : Nat) (hhand : hand > prizes) :
    applyIono hand prizes = prizes := by
  exact Nat.min_eq_right (Nat.le_of_lt hhand)

theorem n_effective_when_hand_large (hand prizes : Nat) (hpr : prizes > 0) (hhand : hand > prizes) :
    denialEffective hand (applyN hand prizes) = true := by
  have hN : applyN hand prizes = prizes := n_reduces_large_hand hand prizes hhand
  simp [denialEffective, hN, hhand]

theorem iono_effective_when_hand_large (hand prizes : Nat) (hpr : prizes > 0) (hhand : hand > prizes) :
    denialEffective hand (applyIono hand prizes) = true := by
  have hI : applyIono hand prizes = prizes := iono_reduces_large_hand hand prizes hhand
  simp [denialEffective, hI, hhand]

theorem judge_example_8_to_4 : applyJudge 8 = 4 := by native_decide
theorem n_example_8_to_2 : applyN 8 2 = 2 := by native_decide
theorem iono_example_9_to_3 : applyIono 9 3 = 3 := by native_decide

-- ============================================================
-- §7  Deck depletion bounds
-- ============================================================

theorem deck_size_bounded_by_60_in_initial :
    initialResources.deckSize ≤ maxDeckSize := by decide

theorem draw_preserves_deck_upper_bound (r : Resources)
    (hvalid : r.deckSize ≤ maxDeckSize) :
    (drawCard r).deckSize ≤ maxDeckSize := by
  by_cases h0 : r.deckSize = 0
  · simp [drawCard, h0]
  · have hsub : r.deckSize - 1 ≤ r.deckSize := Nat.sub_le _ _
    have hdraw : (drawCard r).deckSize ≤ r.deckSize := by
      simp [drawCard, h0, hsub]
    exact Nat.le_trans hdraw hvalid

theorem repeated_depletion_bounded :
    (drawCard (drawCard initialResources)).deckSize ≤ maxDeckSize := by
  have h1 : (drawCard initialResources).deckSize ≤ maxDeckSize :=
    draw_preserves_deck_upper_bound initialResources (by decide)
  exact draw_preserves_deck_upper_bound (drawCard initialResources) h1

theorem deck_never_negative (r : Resources) :
    (drawCard r).deckSize ≥ 0 := Nat.zero_le _

theorem max_deck_constant : maxDeckSize = 60 := rfl

-- ============================================================
-- §8  Energy monotonicity until KO
-- ============================================================

def nonKOTurn (r : Resources) (energyAttachments : Nat) : Resources :=
  { r with energyInPlay := r.energyInPlay + energyAttachments }

theorem nonko_turn_energy_monotone (r : Resources) (n : Nat) :
    (nonKOTurn r n).energyInPlay ≥ r.energyInPlay := by
  simp [nonKOTurn]

theorem nonko_turn_energy_with_zero (r : Resources) :
    (nonKOTurn r 0).energyInPlay = r.energyInPlay := by
  simp [nonKOTurn]

theorem nonko_turn_energy_with_one (r : Resources) :
    (nonKOTurn r 1).energyInPlay = r.energyInPlay + 1 := by
  simp [nonKOTurn]

theorem ko_breaks_monotonicity_example :
    (applyKO (nonKOTurn initialResources 3) 2).energyInPlay <
    (nonKOTurn initialResources 3).energyInPlay := by
  native_decide

theorem energy_monotone_until_ko_statement (r : Resources) (n : Nat) :
    (nonKOTurn r n).energyInPlay ≥ r.energyInPlay :=
  nonko_turn_energy_monotone r n

-- ============================================================
-- §9  Mirror match resource parity
-- ============================================================

def resourceParity (a b : Resources) : Prop :=
  a.handSize = b.handSize ∧
  a.deckSize = b.deckSize ∧
  a.benchCount = b.benchCount ∧
  a.energyInPlay = b.energyInPlay ∧
  a.prizesRemaining = b.prizesRemaining

theorem resource_parity_refl (r : Resources) : resourceParity r r := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem mirror_initial_parity :
    resourceParity initialResources initialResources :=
  resource_parity_refl _

theorem mirror_draw_preserves_parity (r : Resources) :
    resourceParity (drawCard r) (drawCard r) :=
  resource_parity_refl _

theorem mirror_play_preserves_parity (r : Resources) :
    resourceParity (playCard r) (playCard r) :=
  resource_parity_refl _

theorem mirror_attach_preserves_parity (r : Resources) :
    resourceParity (attachEnergy r) (attachEnergy r) :=
  resource_parity_refl _

theorem mirror_prize_preserves_parity (r : Resources) :
    resourceParity (takePrize r) (takePrize r) :=
  resource_parity_refl _

theorem mirror_resource_parity_statement :
    resourceParity initialResources initialResources :=
  mirror_initial_parity

-- ============================================================
-- §10  Additional utility theorems
-- ============================================================

theorem bench_basic_increases_bench_when_room (r : Resources)
    (h : r.benchCount < maxBenchSize) :
    (benchBasic r).benchCount = r.benchCount + 1 := by
  simp [benchBasic, h]

theorem bench_basic_reduces_hand_when_room (r : Resources)
    (h : r.benchCount < maxBenchSize) :
    (benchBasic r).handSize = r.handSize - 1 := by
  simp [benchBasic, h]

theorem bench_basic_no_change_when_full (r : Resources)
    (h : ¬ r.benchCount < maxBenchSize) :
    benchBasic r = r := by
  simp [benchBasic, h]

theorem one_draw_one_play_net_zero_hand (h : Nat) :
    handAfterSequence h 1 1 = h := by
  simp [handAfterSequence]

theorem two_draws_one_play_net_plus_one (h : Nat) :
    handAfterSequence h 2 1 = h + 1 := by
  simp [handAfterSequence]

theorem three_plays_zero_draws_nonincrease (h : Nat) :
    handAfterSequence h 0 3 ≤ h := by
  simp [handAfterSequence]

end PokemonLean.Core.ResourceManagement
