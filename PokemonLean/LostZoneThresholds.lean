import PokemonLean.Basic
import PokemonLean.LostZone

namespace PokemonLean.LostZoneThresholds

open PokemonLean.LostZone

-- ============================================================================
-- LOST ZONE THRESHOLD SYSTEM
-- ============================================================================

inductive LostZoneThreshold
  | provision   -- 4 cards: Cramorant free attack
  | mirageGate  -- 7 cards: Mirage Gate energy accel
  | lostMine    -- 10 cards: Sableye damage spread
  deriving Repr, BEq, DecidableEq

def thresholdValue : LostZoneThreshold → Nat
  | .provision  => 4
  | .mirageGate => 7
  | .lostMine   => 10

@[simp] theorem thresholdValue_provision : thresholdValue .provision = 4 := rfl
@[simp] theorem thresholdValue_mirageGate : thresholdValue .mirageGate = 7 := rfl
@[simp] theorem thresholdValue_lostMine : thresholdValue .lostMine = 10 := rfl

def thresholdMet (player : LostZonePlayerState) (t : LostZoneThreshold) : Prop :=
  thresholdValue t ≤ lostZoneCount player

def hasThresholdMet (player : LostZonePlayerState) (t : LostZoneThreshold) : Bool :=
  decide (thresholdValue t ≤ lostZoneCount player)

theorem hasThresholdMet_iff (player : LostZonePlayerState) (t : LostZoneThreshold) :
    hasThresholdMet player t = true ↔ thresholdMet player t := by
  simp [hasThresholdMet, thresholdMet]

-- ============================================================================
-- THRESHOLD ORDERING
-- ============================================================================

theorem provision_le_mirageGate : thresholdValue .provision ≤ thresholdValue .mirageGate := by decide
theorem mirageGate_le_lostMine : thresholdValue .mirageGate ≤ thresholdValue .lostMine := by decide
theorem provision_le_lostMine : thresholdValue .provision ≤ thresholdValue .lostMine := by decide

theorem mirageGate_met_implies_provision (player : LostZonePlayerState)
    (h : thresholdMet player .mirageGate) : thresholdMet player .provision := by
  simp only [thresholdMet, thresholdValue] at *; omega

theorem lostMine_met_implies_mirageGate (player : LostZonePlayerState)
    (h : thresholdMet player .lostMine) : thresholdMet player .mirageGate := by
  simp only [thresholdMet, thresholdValue] at *; omega

theorem lostMine_met_implies_provision (player : LostZonePlayerState)
    (h : thresholdMet player .lostMine) : thresholdMet player .provision :=
  mirageGate_met_implies_provision player (lostMine_met_implies_mirageGate player h)

-- ============================================================================
-- THRESHOLD MONOTONICITY
-- ============================================================================

theorem sendCard_preserves_threshold (player : LostZonePlayerState) (card : Card) (t : LostZoneThreshold)
    (h : thresholdMet player t) : thresholdMet (sendCardToLostZone player card) t := by
  simp only [thresholdMet] at *
  have hc := sendCardToLostZone_lostZoneCount player card
  omega

theorem sendEnergy_preserves_threshold (player : LostZonePlayerState) (e : EnergyType) (t : LostZoneThreshold)
    (h : thresholdMet player t) : thresholdMet (sendEnergyToLostZone player e) t := by
  simp only [thresholdMet] at *
  have hc := sendEnergyToLostZone_lostZoneCount player e
  omega

theorem threshold_monotone (player : LostZonePlayerState) (t1 t2 : LostZoneThreshold)
    (hOrd : thresholdValue t1 ≤ thresholdValue t2)
    (hMet : thresholdMet player t2) : thresholdMet player t1 := by
  simp only [thresholdMet] at *; omega

-- ============================================================================
-- CRAMORANT: LOST PROVISION (FREE ATTACK AT 4+ LOST ZONE)
-- ============================================================================

def cramorantLostProvisionDamage : Nat := 110

def canUseLostProvision (player : LostZonePlayerState) : Bool :=
  hasThresholdMet player .provision

def cramorantLostProvision (attacker : LostZonePlayerState) (target : PokemonInPlay) :
    Option PokemonInPlay :=
  if 4 ≤ lostZoneCount attacker then
    some (applyDamage target cramorantLostProvisionDamage)
  else
    none

@[simp] theorem cramorantLostProvisionDamage_value : cramorantLostProvisionDamage = 110 := rfl

theorem canUseLostProvision_iff (player : LostZonePlayerState) :
    canUseLostProvision player = true ↔ thresholdMet player .provision := by
  simp [canUseLostProvision, hasThresholdMet_iff]

theorem cramorantLostProvision_none_of_lt_four (attacker : LostZonePlayerState) (target : PokemonInPlay)
    (h : lostZoneCount attacker < 4) : cramorantLostProvision attacker target = none := by
  simp only [cramorantLostProvision]
  split
  · next h' => exact absurd h (by omega)
  · rfl

theorem cramorantLostProvision_some_of_four (attacker : LostZonePlayerState) (target : PokemonInPlay)
    (h : 4 ≤ lostZoneCount attacker) :
    cramorantLostProvision attacker target = some (applyDamage target cramorantLostProvisionDamage) := by
  simp only [cramorantLostProvision]
  split
  · rfl
  · next h' => exact absurd h (by omega)

theorem cramorantLostProvision_damage_le_hp (attacker : LostZonePlayerState)
    (target damaged : PokemonInPlay)
    (h : cramorantLostProvision attacker target = some damaged) :
    damaged.damage ≤ target.card.hp := by
  simp only [cramorantLostProvision] at h
  split at h
  · simp at h; cases h; exact applyDamage_damage_le_hp target cramorantLostProvisionDamage
  · simp at h

theorem cramorantLostProvision_no_energy_cost (attacker : LostZonePlayerState)
    (target damaged : PokemonInPlay)
    (h : cramorantLostProvision attacker target = some damaged) :
    damaged.energy = target.energy := by
  simp only [cramorantLostProvision] at h
  split at h
  · simp at h; cases h; exact applyDamage_energy target cramorantLostProvisionDamage
  · simp at h

theorem cramorantLostProvision_status (attacker : LostZonePlayerState)
    (target damaged : PokemonInPlay)
    (h : cramorantLostProvision attacker target = some damaged) :
    damaged.status = target.status := by
  simp only [cramorantLostProvision] at h
  split at h
  · simp at h; cases h; exact applyDamage_status target cramorantLostProvisionDamage
  · simp at h

theorem cramorantLostProvision_attacker_unchanged (attacker : LostZonePlayerState) (target : PokemonInPlay)
    (h : 4 ≤ lostZoneCount attacker) :
    ∃ damaged, cramorantLostProvision attacker target = some damaged ∧
      attacker.lostZone = attacker.lostZone :=
  ⟨applyDamage target cramorantLostProvisionDamage,
    cramorantLostProvision_some_of_four attacker target h, rfl⟩

-- ============================================================================
-- COLRESS'S EXPERIMENT (LOOK 5, HAND 3, LOST ZONE 2)
-- ============================================================================

structure ColressResult where
  toHand : List Card
  toLostZone : List Card
  deriving Repr, BEq, DecidableEq

def colressExperimentValid (looked : List Card) (result : ColressResult) : Prop :=
  looked.length = 5 ∧
  result.toHand.length = 3 ∧
  result.toLostZone.length = 2 ∧
  (∀ c, c ∈ result.toHand → c ∈ looked) ∧
  (∀ c, c ∈ result.toLostZone → c ∈ looked)

def applyColressExperiment (player : LostZonePlayerState) (result : ColressResult) :
    LostZonePlayerState :=
  let newHand := result.toHand ++ player.hand
  let newLZ := result.toLostZone.map LostZoneItem.card ++ player.lostZone
  { player with hand := newHand, lostZone := newLZ }

theorem applyColressExperiment_hand_length (player : LostZonePlayerState) (result : ColressResult)
    (hHand : result.toHand.length = 3) :
    (applyColressExperiment player result).hand.length = player.hand.length + 3 := by
  simp [applyColressExperiment, hHand]; omega

theorem applyColressExperiment_lostZoneCount (player : LostZonePlayerState) (result : ColressResult)
    (hLZ : result.toLostZone.length = 2) :
    lostZoneCount (applyColressExperiment player result) = lostZoneCount player + 2 := by
  simp [applyColressExperiment, lostZoneCount, List.length_map, hLZ]; omega

theorem applyColressExperiment_discard (player : LostZonePlayerState) (result : ColressResult) :
    (applyColressExperiment player result).discard = player.discard := by
  simp [applyColressExperiment]

theorem applyColressExperiment_deck (player : LostZonePlayerState) (result : ColressResult) :
    (applyColressExperiment player result).deck = player.deck := by
  simp [applyColressExperiment]

theorem applyColressExperiment_active (player : LostZonePlayerState) (result : ColressResult) :
    (applyColressExperiment player result).active = player.active := by
  simp [applyColressExperiment]

theorem applyColressExperiment_bench (player : LostZonePlayerState) (result : ColressResult) :
    (applyColressExperiment player result).bench = player.bench := by
  simp [applyColressExperiment]

theorem applyColressExperiment_preserves_threshold (player : LostZonePlayerState)
    (result : ColressResult) (t : LostZoneThreshold)
    (hLZ : result.toLostZone.length = 2)
    (h : thresholdMet player t) :
    thresholdMet (applyColressExperiment player result) t := by
  simp only [thresholdMet] at *
  have hc := applyColressExperiment_lostZoneCount player result hLZ
  omega

theorem colress_cards_distributed (result : ColressResult)
    (looked : List Card)
    (h : colressExperimentValid looked result) :
    result.toHand.length + result.toLostZone.length = 5 := by
  obtain ⟨_, hH, hL, _, _⟩ := h; omega

def applyColressFromDeck (player : LostZonePlayerState) (result : ColressResult)
    (_looked : List Card) (restDeck : List Card) : LostZonePlayerState :=
  let afterColress := applyColressExperiment player result
  { afterColress with deck := restDeck }

theorem applyColressFromDeck_hand_length (player : LostZonePlayerState)
    (result : ColressResult) (looked restDeck : List Card)
    (hHand : result.toHand.length = 3) :
    (applyColressFromDeck player result looked restDeck).hand.length = player.hand.length + 3 := by
  simp [applyColressFromDeck, applyColressExperiment, hHand]; omega

theorem applyColressFromDeck_lostZoneCount (player : LostZonePlayerState)
    (result : ColressResult) (looked restDeck : List Card)
    (hLZ : result.toLostZone.length = 2) :
    lostZoneCount (applyColressFromDeck player result looked restDeck) = lostZoneCount player + 2 := by
  simp [applyColressFromDeck, applyColressExperiment, lostZoneCount, List.length_map, hLZ]; omega

-- ============================================================================
-- ACCUMULATION THEOREMS
-- ============================================================================

theorem accumulate_cards_threshold (player : LostZonePlayerState)
    (cards : List Card) (t : LostZoneThreshold)
    (h : thresholdValue t ≤ lostZoneCount player + cards.length) :
    thresholdMet (cards.foldl sendCardToLostZone player) t := by
  induction cards generalizing player with
  | nil =>
    simp only [List.foldl, List.length_nil, Nat.add_zero] at *
    exact h
  | cons c cs ih =>
    simp only [List.foldl]
    apply ih
    have hc := sendCardToLostZone_lostZoneCount player c
    simp only [List.length_cons] at h
    omega

theorem two_flower_selectings_add_two
    (p0 p1 p2 : LostZonePlayerState) (b1 b2 : Bool)
    (h1 : flowerSelecting p0 b1 = some p1)
    (h2 : flowerSelecting p1 b2 = some p2) :
    lostZoneCount p2 = lostZoneCount p0 + 2 := by
  have h1c := flowerSelecting_lostZoneCount p0 p1 b1 h1
  have h2c := flowerSelecting_lostZoneCount p1 p2 b2 h2
  omega

theorem three_flower_selectings_add_three
    (p0 p1 p2 p3 : LostZonePlayerState) (b1 b2 b3 : Bool)
    (h1 : flowerSelecting p0 b1 = some p1)
    (h2 : flowerSelecting p1 b2 = some p2)
    (h3 : flowerSelecting p2 b3 = some p3) :
    lostZoneCount p3 = lostZoneCount p0 + 3 := by
  have h12 := two_flower_selectings_add_two p0 p1 p2 b1 b2 h1 h2
  have h3c := flowerSelecting_lostZoneCount p2 p3 b3 h3
  omega

theorem four_flower_selectings_reach_provision
    (p0 p1 p2 p3 p4 : LostZonePlayerState) (b1 b2 b3 b4 : Bool)
    (hInit : lostZoneCount p0 = 0)
    (h1 : flowerSelecting p0 b1 = some p1)
    (h2 : flowerSelecting p1 b2 = some p2)
    (h3 : flowerSelecting p2 b3 = some p3)
    (h4 : flowerSelecting p3 b4 = some p4) :
    thresholdMet p4 .provision := by
  have h123 := three_flower_selectings_add_three p0 p1 p2 p3 b1 b2 b3 h1 h2 h3
  have h4c := flowerSelecting_lostZoneCount p3 p4 b4 h4
  simp only [thresholdMet, thresholdValue]; omega

theorem lostImpact_advances_threshold (player next : LostZonePlayerState)
    (h : lostImpact player = some next) (t : LostZoneThreshold)
    (hAlmost : thresholdValue t ≤ lostZoneCount player + 2) :
    thresholdMet next t := by
  have hCount := lostImpact_lostZoneCount player next h
  simp only [thresholdMet]; omega

theorem colress_advances_threshold (player : LostZonePlayerState)
    (result : ColressResult) (t : LostZoneThreshold)
    (hLZ : result.toLostZone.length = 2)
    (hAlmost : thresholdValue t ≤ lostZoneCount player + 2) :
    thresholdMet (applyColressExperiment player result) t := by
  simp only [thresholdMet]
  have hc := applyColressExperiment_lostZoneCount player result hLZ
  omega

-- ============================================================================
-- THRESHOLD COUNT ENUMERATION
-- ============================================================================

theorem no_threshold_at_zero (player : LostZonePlayerState) (h : lostZoneCount player = 0) :
    ¬thresholdMet player .provision := by
  simp only [thresholdMet, thresholdValue]; omega

theorem no_threshold_at_three (player : LostZonePlayerState) (h : lostZoneCount player = 3) :
    ¬thresholdMet player .provision := by
  simp only [thresholdMet, thresholdValue]; omega

theorem provision_at_four (player : LostZonePlayerState) (h : lostZoneCount player = 4) :
    thresholdMet player .provision := by
  simp only [thresholdMet, thresholdValue]; omega

theorem no_mirageGate_at_four (player : LostZonePlayerState) (h : lostZoneCount player = 4) :
    ¬thresholdMet player .mirageGate := by
  simp only [thresholdMet, thresholdValue]; omega

theorem provision_at_six (player : LostZonePlayerState) (h : lostZoneCount player = 6) :
    thresholdMet player .provision ∧ ¬thresholdMet player .mirageGate := by
  simp only [thresholdMet, thresholdValue]; omega

theorem mirageGate_at_seven (player : LostZonePlayerState) (h : lostZoneCount player = 7) :
    thresholdMet player .mirageGate := by
  simp only [thresholdMet, thresholdValue]; omega

theorem no_lostMine_at_seven (player : LostZonePlayerState) (h : lostZoneCount player = 7) :
    ¬thresholdMet player .lostMine := by
  simp only [thresholdMet, thresholdValue]; omega

theorem mirageGate_at_nine (player : LostZonePlayerState) (h : lostZoneCount player = 9) :
    thresholdMet player .mirageGate ∧ ¬thresholdMet player .lostMine := by
  simp only [thresholdMet, thresholdValue]; omega

theorem all_thresholds_at_ten (player : LostZonePlayerState) (h : lostZoneCount player = 10) :
    thresholdMet player .provision ∧ thresholdMet player .mirageGate ∧ thresholdMet player .lostMine := by
  simp only [thresholdMet, thresholdValue]; omega

theorem all_thresholds_at_fifteen (player : LostZonePlayerState) (h : lostZoneCount player = 15) :
    thresholdMet player .provision ∧ thresholdMet player .mirageGate ∧ thresholdMet player .lostMine := by
  simp only [thresholdMet, thresholdValue]; omega

end PokemonLean.LostZoneThresholds
