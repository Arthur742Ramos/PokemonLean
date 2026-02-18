/-
  PokemonLean / Core / LostZoneDeck.lean

  Lost Zone Box archetype formalization.
  Self-contained, sorry-free, with 35+ theorems.
-/

set_option linter.unusedVariables false

namespace PokemonLean.Core.LostZoneDeck

-- ============================================================
-- §1  Core cards and thresholds
-- ============================================================

inductive EnergyType where
  | grass
  | fire
  | water
  | lightning
  | psychic
  | fighting
  deriving DecidableEq, Repr

inductive CardKind where
  | pokemon
  | trainer
  deriving DecidableEq, Repr

structure Card where
  name : String
  kind : CardKind
  deriving DecidableEq, Repr

/-- Key Lost Zone Box cards. -/
def comfey : Card := ⟨"Comfey", .pokemon⟩
def cramorant : Card := ⟨"Cramorant", .pokemon⟩
def sableye : Card := ⟨"Sableye", .pokemon⟩
def mirageGate : Card := ⟨"Mirage Gate", .trainer⟩
def colressExperimentCard : Card := ⟨"Colress's Experiment", .trainer⟩

/-- Lost Zone thresholds for important unlocks. -/
def cramorantThreshold : Nat := 4
def mirageGateThreshold : Nat := 7
def sableyeThreshold : Nat := 10

/-- Colress's Experiment: look 5, keep 2, Lost Zone 3. -/
def colressCardsSeen : Nat := 5
def colressToHand : Nat := 2
def colressToLostZone : Nat := 3

/-- [T1] Threshold value for Cramorant. -/
theorem cramorant_threshold_value : cramorantThreshold = 4 := rfl

/-- [T2] Threshold value for Mirage Gate. -/
theorem mirage_gate_threshold_value : mirageGateThreshold = 7 := rfl

/-- [T3] Threshold value for Sableye. -/
theorem sableye_threshold_value : sableyeThreshold = 10 := rfl

/-- [T4] Thresholds are strictly ordered: 4 < 7. -/
theorem threshold_4_lt_7 : cramorantThreshold < mirageGateThreshold := by
  native_decide

/-- [T5] Thresholds are strictly ordered: 7 < 10. -/
theorem threshold_7_lt_10 : mirageGateThreshold < sableyeThreshold := by
  native_decide

/-- [T6] Thresholds are strictly ordered: 4 < 10. -/
theorem threshold_4_lt_10 : cramorantThreshold < sableyeThreshold := by
  native_decide

/-- [T7] Colress split is 3 to Lost Zone + 2 to hand. -/
theorem colress_split_total : colressToLostZone + colressToHand = colressCardsSeen := by
  native_decide

/-- [T8] Colress gives net +2 hand cards from 5 seen. -/
theorem colress_net_hand_gain_constant : colressToHand = 2 := rfl

/-- [T9] Colress gives net +3 Lost Zone cards. -/
theorem colress_net_lost_zone_constant : colressToLostZone = 3 := rfl

-- ============================================================
-- §2  State transitions
-- ============================================================

structure LZState where
  lostZone : Nat
  hand : Nat
  deck : Nat
  attachedEnergy : Nat
  turn : Nat
  deriving DecidableEq, Repr

/-- Comfey Flower Selecting: look top 2, choose 1 to Lost Zone. -/
def flowerSelecting (s : LZState) : LZState :=
  { s with
    lostZone := s.lostZone + 1
    hand := s.hand + 1
    deck := s.deck - 2 }

/-- Two Comfey uses in a turn cycle. -/
def doubleFlower (s : LZState) : LZState :=
  flowerSelecting (flowerSelecting s)

/-- Colress's Experiment: +3 Lost Zone, +2 hand, consumes 5 deck cards seen. -/
def colressExperiment (s : LZState) : LZState :=
  { s with
    lostZone := s.lostZone + colressToLostZone
    hand := s.hand + colressToHand
    deck := s.deck - colressCardsSeen }

/-- Advance to next turn (simplified). -/
def nextTurn (s : LZState) : LZState :=
  { s with turn := s.turn + 1 }

/-- Unlock predicates. -/
def cramorantOnline (s : LZState) : Prop := s.lostZone ≥ cramorantThreshold
def mirageGateOnline (s : LZState) : Prop := s.lostZone ≥ mirageGateThreshold
def sableyeOnline (s : LZState) : Prop := s.lostZone ≥ sableyeThreshold

instance decidableCramorantOnline (s : LZState) : Decidable (cramorantOnline s) := by
  unfold cramorantOnline cramorantThreshold
  infer_instance

/-- [T10] Flower Selecting adds exactly 1 Lost Zone card. -/
theorem flower_adds_exactly_one (s : LZState) :
    (flowerSelecting s).lostZone = s.lostZone + 1 := rfl

/-- [T11] Flower Selecting adds exactly 1 hand card. -/
theorem flower_hand_plus_one (s : LZState) :
    (flowerSelecting s).hand = s.hand + 1 := rfl

/-- [T12] Flower Selecting looks at 2 deck cards. -/
theorem flower_deck_minus_two (s : LZState) :
    (flowerSelecting s).deck = s.deck - 2 := rfl

/-- [T13] Double Flower Selecting adds exactly 2 Lost Zone cards. -/
theorem double_flower_adds_two (s : LZState) :
    (doubleFlower s).lostZone = s.lostZone + 2 := by
  simp [doubleFlower, flowerSelecting, Nat.add_assoc]

/-- [T14] Colress adds exactly 3 to Lost Zone. -/
theorem colress_adds_three (s : LZState) :
    (colressExperiment s).lostZone = s.lostZone + 3 := by
  simp [colressExperiment, colressToLostZone]

/-- [T15] Colress adds exactly 2 to hand. -/
theorem colress_hand_plus_two (s : LZState) :
    (colressExperiment s).hand = s.hand + 2 := by
  simp [colressExperiment, colressToHand]

/-- [T16] Colress sees 5 cards from deck. -/
theorem colress_deck_minus_five (s : LZState) :
    (colressExperiment s).deck = s.deck - 5 := by
  simp [colressExperiment, colressCardsSeen]

/-- [T17] nextTurn increments turn count by 1. -/
theorem next_turn_increments (s : LZState) :
    (nextTurn s).turn = s.turn + 1 := rfl

/-- [T18] nextTurn does not change Lost Zone size. -/
theorem next_turn_preserves_lost_zone (s : LZState) :
    (nextTurn s).lostZone = s.lostZone := rfl

-- ============================================================
-- §3  Monotonicity of Lost Zone growth
-- ============================================================

/-- [T19] Flower Selecting is Lost Zone monotone. -/
theorem flower_monotone (s : LZState) :
    s.lostZone ≤ (flowerSelecting s).lostZone := by
  simp [flowerSelecting]

/-- [T20] Double Flower is Lost Zone monotone. -/
theorem double_flower_monotone (s : LZState) :
    s.lostZone ≤ (doubleFlower s).lostZone := by
  simp [doubleFlower, flowerSelecting]
  omega

/-- [T21] Colress is Lost Zone monotone. -/
theorem colress_monotone (s : LZState) :
    s.lostZone ≤ (colressExperiment s).lostZone := by
  simp [colressExperiment, colressToLostZone]

inductive LZAction where
  | flower
  | colress
  | pass
  deriving DecidableEq, Repr

def actionGain : LZAction → Nat
  | .flower => 1
  | .colress => 3
  | .pass => 0

def applyAction (s : LZState) (a : LZAction) : LZState :=
  { s with
    lostZone := s.lostZone + actionGain a
    turn := s.turn + 1 }

/-- Apply a list of actions in order. -/
def applyActions : LZState → List LZAction → LZState
  | s, [] => s
  | s, a :: rest => applyActions (applyAction s a) rest

def totalGain : List LZAction → Nat
  | [] => 0
  | a :: rest => actionGain a + totalGain rest

/-- [T22] Single action never decreases Lost Zone. -/
theorem apply_action_monotone (s : LZState) (a : LZAction) :
    s.lostZone ≤ (applyAction s a).lostZone := by
  simp [applyAction, actionGain]

/-- [T23] Applying actions gives exact Lost Zone increase by totalGain. -/
theorem apply_actions_exact_gain (s : LZState) (acts : List LZAction) :
    (applyActions s acts).lostZone = s.lostZone + totalGain acts := by
  induction acts generalizing s with
  | nil =>
      simp [applyActions, totalGain]
  | cons a rest ih =>
      simp [applyActions, totalGain, ih, applyAction, Nat.add_assoc]

/-- [T24] Action sequences are monotone in Lost Zone. -/
theorem apply_actions_monotone (s : LZState) (acts : List LZAction) :
    s.lostZone ≤ (applyActions s acts).lostZone := by
  rw [apply_actions_exact_gain]
  exact Nat.le_add_right _ _

/-- [T25] totalGain is nonnegative. -/
theorem total_gain_nonneg (acts : List LZAction) :
    0 ≤ totalGain acts := Nat.zero_le _

/-- [T26] totalGain for one Flower is 1. -/
theorem total_gain_single_flower : totalGain [.flower] = 1 := rfl

/-- [T27] totalGain for one Colress is 3. -/
theorem total_gain_single_colress : totalGain [.colress] = 3 := rfl

/-- [T28] totalGain for pass is 0. -/
theorem total_gain_single_pass : totalGain [.pass] = 0 := rfl

-- ============================================================
-- §4  Threshold unlock implications
-- ============================================================

/-- [T29] If Sableye is online, Mirage Gate is online. -/
theorem sableye_implies_mirage (s : LZState) (h : sableyeOnline s) :
    mirageGateOnline s := by
  unfold sableyeOnline mirageGateOnline mirageGateThreshold sableyeThreshold at *
  omega

/-- [T30] If Mirage Gate is online, Cramorant is online. -/
theorem mirage_implies_cramorant (s : LZState) (h : mirageGateOnline s) :
    cramorantOnline s := by
  unfold cramorantOnline mirageGateOnline cramorantThreshold mirageGateThreshold at *
  omega

/-- [T31] If Sableye is online, Cramorant is online. -/
theorem sableye_implies_cramorant (s : LZState) (h : sableyeOnline s) :
    cramorantOnline s := by
  exact mirage_implies_cramorant s (sableye_implies_mirage s h)

/-- [T32] Reaching 10 Lost Zone enables all key Lost Zone payoffs. -/
theorem reaching_ten_enables_all (s : LZState) (h : s.lostZone ≥ 10) :
    cramorantOnline s ∧ mirageGateOnline s ∧ sableyeOnline s := by
  constructor
  · unfold cramorantOnline cramorantThreshold
    omega
  constructor
  · unfold mirageGateOnline mirageGateThreshold
    omega
  · unfold sableyeOnline sableyeThreshold
    omega

/-- [T33] Reaching 7 enables Mirage Gate. -/
theorem reaching_seven_enables_mirage (s : LZState) (h : s.lostZone ≥ 7) :
    mirageGateOnline s := by
  exact h

/-- [T34] Reaching 4 enables Cramorant. -/
theorem reaching_four_enables_cramorant (s : LZState) (h : s.lostZone ≥ 4) :
    cramorantOnline s := by
  exact h

/-- [T35] At exactly 10 Lost Zone, all thresholds hold. -/
theorem exactly_ten_enables_all (s : LZState) (h : s.lostZone = 10) :
    cramorantOnline s ∧ mirageGateOnline s ∧ sableyeOnline s := by
  apply reaching_ten_enables_all
  omega

-- ============================================================
-- §5  Cramorant free attack and Mirage Gate condition
-- ============================================================

/-- Cramorant's nominal attack cost (two Colorless). -/
def cramorantPrintedCost : Nat := 2

/-- Lost Provisions reduces attack cost to zero at 4+ Lost Zone. -/
def cramorantEffectiveCost (s : LZState) : Nat :=
  if h : cramorantOnline s then 0 else cramorantPrintedCost

/-- Mirage Gate condition: 7+ in Lost Zone and two different Energy types. -/
def mirageGateCanAttach (s : LZState) (e1 e2 : EnergyType) : Prop :=
  mirageGateOnline s ∧ e1 ≠ e2

/-- [T36] Printed Cramorant cost is 2. -/
theorem cramorant_printed_cost_value : cramorantPrintedCost = 2 := rfl

/-- [T37] Cramorant is free when online. -/
theorem cramorant_free_when_online (s : LZState) (h : cramorantOnline s) :
    cramorantEffectiveCost s = 0 := by
  simp [cramorantEffectiveCost, h]

/-- [T38] Cramorant costs 2 when below threshold. -/
theorem cramorant_cost_when_offline (s : LZState) (h : ¬ cramorantOnline s) :
    cramorantEffectiveCost s = 2 := by
  simp [cramorantEffectiveCost, h, cramorantPrintedCost]

/-- [T39] Cramorant is a free attacker at 4+ Lost Zone. -/
theorem cramorant_is_free_attacker (s : LZState) (h : s.lostZone ≥ 4) :
    cramorantEffectiveCost s = 0 := by
  exact cramorant_free_when_online s h

/-- [T40] Mirage Gate can attach when threshold and energy inequality hold. -/
theorem mirage_gate_attach_possible (s : LZState) (e1 e2 : EnergyType)
    (hZone : s.lostZone ≥ 7) (hDiff : e1 ≠ e2) :
    mirageGateCanAttach s e1 e2 := by
  exact ⟨hZone, hDiff⟩

/-- [T41] Mirage Gate cannot attach two identical energies. -/
theorem mirage_gate_no_same_energy (s : LZState) (e : EnergyType) :
    ¬ mirageGateCanAttach s e e := by
  intro h
  exact h.2 rfl

-- ============================================================
-- §6  Optimal sequencing: early Comfey, mid Cramorant, late Sableye
-- ============================================================

/-- A practical high-tempo opening:
    Turn 1: two Comfey uses, Turn 2: two Comfey uses, Turn 3: Colress. -/
def optimalTurn1to3 : List LZAction :=
  [.flower, .flower, .flower, .flower, .colress]

/-- Turn 4 extension: a second Colress to hit 10 exactly from zero. -/
def optimalTurn1to4 : List LZAction :=
  [.flower, .flower, .flower, .flower, .colress, .colress]

/-- [T42] totalGain for optimal Turn 1-3 line is exactly 7. -/
theorem optimal_turn1to3_gain : totalGain optimalTurn1to3 = 7 := by
  native_decide

/-- [T43] totalGain for optimal Turn 1-4 line is exactly 10. -/
theorem optimal_turn1to4_gain : totalGain optimalTurn1to4 = 10 := by
  native_decide

/-- [T44] Optimal line reaches 7 by turn 3 from Lost Zone 0. -/
theorem optimal_line_reaches_7_by_turn3 (s : LZState) (h0 : s.lostZone = 0) :
    (applyActions s optimalTurn1to3).lostZone = 7 := by
  rw [apply_actions_exact_gain]
  rw [h0]
  rw [optimal_turn1to3_gain]

/-- [T45] The same line enables Mirage Gate on turn 3. -/
theorem optimal_line_turn3_mirage_online (s : LZState) (h0 : s.lostZone = 0) :
    mirageGateOnline (applyActions s optimalTurn1to3) := by
  have hz : (applyActions s optimalTurn1to3).lostZone = 7 :=
    optimal_line_reaches_7_by_turn3 s h0
  unfold mirageGateOnline mirageGateThreshold
  rw [hz]
  omega

/-- [T46] The same line also enables Cramorant by turn 3. -/
theorem optimal_line_turn3_cramorant_online (s : LZState) (h0 : s.lostZone = 0) :
    cramorantOnline (applyActions s optimalTurn1to3) := by
  exact mirage_implies_cramorant _ (optimal_line_turn3_mirage_online s h0)

/-- [T47] Extended line reaches 10 by turn 4 from Lost Zone 0. -/
theorem optimal_line_reaches_10_by_turn4 (s : LZState) (h0 : s.lostZone = 0) :
    (applyActions s optimalTurn1to4).lostZone = 10 := by
  rw [apply_actions_exact_gain]
  rw [h0]
  rw [optimal_turn1to4_gain]

/-- [T48] Extended line enables Sableye by turn 4. -/
theorem optimal_line_turn4_sableye_online (s : LZState) (h0 : s.lostZone = 0) :
    sableyeOnline (applyActions s optimalTurn1to4) := by
  have hz : (applyActions s optimalTurn1to4).lostZone = 10 :=
    optimal_line_reaches_10_by_turn4 s h0
  unfold sableyeOnline sableyeThreshold
  rw [hz]
  omega

-- ============================================================
-- §7  Sableye Lost Mine damage-counter math
-- ============================================================

/-- One damage counter is ten damage. -/
def damagePerCounter : Nat := 10

/-- Lost Mine places 12 damage counters. -/
def sableyeCounters : Nat := 12

/-- Total raw damage represented by Lost Mine counters. -/
def sableyeDamage : Nat := sableyeCounters * damagePerCounter

/-- Counters needed to KO a target with hp. -/
def countersNeededForHP (hp : Nat) : Nat :=
  (hp + damagePerCounter - 1) / damagePerCounter

/-- Is a target KOable by Lost Mine alone? -/
def sableyeCanKO (hp : Nat) : Prop :=
  countersNeededForHP hp ≤ sableyeCounters

/-- [T49] Sableye Lost Mine equals 120 damage in counters. -/
theorem sableye_damage_value : sableyeDamage = 120 := by
  native_decide

/-- [T50] 60 HP requires 6 counters. -/
theorem counters_needed_60 : countersNeededForHP 60 = 6 := by
  native_decide

/-- [T51] 70 HP requires 7 counters. -/
theorem counters_needed_70 : countersNeededForHP 70 = 7 := by
  native_decide

/-- [T52] 120 HP requires 12 counters. -/
theorem counters_needed_120 : countersNeededForHP 120 = 12 := by
  native_decide

/-- [T53] 130 HP requires 13 counters. -/
theorem counters_needed_130 : countersNeededForHP 130 = 13 := by
  native_decide

/-- [T54] Lost Mine can KO a 60 HP bench Pokémon. -/
theorem sableye_kos_60 : sableyeCanKO 60 := by
  unfold sableyeCanKO
  rw [counters_needed_60]
  native_decide

/-- [T55] Lost Mine can KO a 70 HP bench Pokémon. -/
theorem sableye_kos_70 : sableyeCanKO 70 := by
  unfold sableyeCanKO
  rw [counters_needed_70]
  native_decide

/-- [T56] Lost Mine can KO a 120 HP bench Pokémon exactly. -/
theorem sableye_kos_120 : sableyeCanKO 120 := by
  unfold sableyeCanKO
  rw [counters_needed_120]
  native_decide

/-- [T57] Lost Mine cannot KO a 130 HP bench Pokémon by itself. -/
theorem sableye_not_ko_130 : ¬ sableyeCanKO 130 := by
  unfold sableyeCanKO
  rw [counters_needed_130]
  native_decide

/-- [T58] 12 counters can produce up to two 60 HP KOs (6 + 6). -/
theorem sableye_two_60hp_kos_possible : 2 * countersNeededForHP 60 ≤ sableyeCounters := by
  rw [counters_needed_60]
  native_decide

/-- [T59] 12 counters cannot produce three 60 HP KOs (6 + 6 + 6). -/
theorem sableye_three_60hp_kos_impossible :
    ¬ (3 * countersNeededForHP 60 ≤ sableyeCounters) := by
  rw [counters_needed_60]
  native_decide

/-- [T60] Lost Mine corresponds to practical 1-2 bench KOs on low-HP targets. -/
theorem sableye_one_to_two_kos_low_hp :
    countersNeededForHP 60 ≤ sableyeCounters ∧
    2 * countersNeededForHP 60 ≤ sableyeCounters ∧
    ¬ (3 * countersNeededForHP 60 ≤ sableyeCounters) := by
  constructor
  · rw [counters_needed_60]
    native_decide
  constructor
  · exact sableye_two_60hp_kos_possible
  · exact sableye_three_60hp_kos_impossible

-- ============================================================
-- §8  Colress arithmetic guarantees
-- ============================================================

/-- [T61] Colress gives exact Lost Zone gain of 3. -/
theorem colress_exact_lost_zone_gain (s : LZState) :
    (colressExperiment s).lostZone - s.lostZone = 3 := by
  simp [colressExperiment, colressToLostZone]

/-- [T62] Colress gives exact hand gain of 2. -/
theorem colress_exact_hand_gain (s : LZState) :
    (colressExperiment s).hand - s.hand = 2 := by
  simp [colressExperiment, colressToHand]

/-- [T63] Colress keeps all seen cards accounted for. -/
theorem colress_accounting : colressToHand + colressToLostZone = 5 := by
  native_decide

/-- [T64] Any Colress use strictly increases Lost Zone. -/
theorem colress_strictly_increases_lost_zone (s : LZState) :
    (colressExperiment s).lostZone > s.lostZone := by
  simp [colressExperiment, colressToLostZone]

/-- [T65] Any Flower Selecting use strictly increases Lost Zone. -/
theorem flower_strictly_increases_lost_zone (s : LZState) :
    (flowerSelecting s).lostZone > s.lostZone := by
  simp [flowerSelecting]

end PokemonLean.Core.LostZoneDeck
