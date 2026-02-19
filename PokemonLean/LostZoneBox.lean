import PokemonLean.Basic
import PokemonLean.LostZone
import PokemonLean.LostZoneThresholds

namespace PokemonLean.LostZoneBox

open PokemonLean.LostZone
open PokemonLean.LostZoneThresholds

-- ============================================================================
-- LOST ZONE BOX DECK ARCHETYPE
-- ============================================================================

structure LostZoneBoxDeck where
  comfeyCount : Nat
  cramorantCount : Nat
  sableyeCount : Nat
  giratinaVSTARCount : Nat
  colressCount : Nat
  mirageGateCount : Nat
  lostVacuumCount : Nat
  otherCards : Nat
  deriving Repr, BEq, DecidableEq

def deckTotalCount (d : LostZoneBoxDeck) : Nat :=
  d.comfeyCount + d.cramorantCount + d.sableyeCount + d.giratinaVSTARCount +
  d.colressCount + d.mirageGateCount + d.lostVacuumCount + d.otherCards

def isValidLostZoneBoxDeck (d : LostZoneBoxDeck) : Prop :=
  deckTotalCount d = 60 ∧
  d.comfeyCount ≤ 4 ∧ d.cramorantCount ≤ 4 ∧ d.sableyeCount ≤ 4 ∧
  d.giratinaVSTARCount ≤ 4 ∧ d.colressCount ≤ 4 ∧ d.mirageGateCount ≤ 4 ∧
  d.lostVacuumCount ≤ 4

def standardLostBoxDeck : LostZoneBoxDeck :=
  { comfeyCount := 4, cramorantCount := 1, sableyeCount := 2, giratinaVSTARCount := 2,
    colressCount := 4, mirageGateCount := 4, lostVacuumCount := 2, otherCards := 41 }

theorem standardLostBoxDeck_valid : isValidLostZoneBoxDeck standardLostBoxDeck := by
  unfold isValidLostZoneBoxDeck standardLostBoxDeck deckTotalCount; decide

theorem standardLostBoxDeck_total : deckTotalCount standardLostBoxDeck = 60 := by native_decide

-- ============================================================================
-- GAME PLAN PHASES
-- ============================================================================

inductive GamePhase
  | earlySetup | provisionReady | mirageReady | fullPower
  deriving Repr, BEq, DecidableEq

def currentPhase (player : LostZonePlayerState) : GamePhase :=
  let n := lostZoneCount player
  if n < 4 then .earlySetup
  else if n < 7 then .provisionReady
  else if n < 10 then .mirageReady
  else .fullPower

theorem currentPhase_earlySetup (player : LostZonePlayerState)
    (h : lostZoneCount player < 4) : currentPhase player = .earlySetup := by
  show (if lostZoneCount player < 4 then _ else _) = _
  rw [if_pos h]

theorem currentPhase_provision (player : LostZonePlayerState)
    (h1 : 4 ≤ lostZoneCount player) (h2 : lostZoneCount player < 7) :
    currentPhase player = .provisionReady := by
  show (if lostZoneCount player < 4 then _ else _) = _
  rw [if_neg (by omega), if_pos h2]

theorem currentPhase_mirage (player : LostZonePlayerState)
    (h1 : 7 ≤ lostZoneCount player) (h2 : lostZoneCount player < 10) :
    currentPhase player = .mirageReady := by
  show (if lostZoneCount player < 4 then _ else _) = _
  rw [if_neg (by omega), if_neg (by omega), if_pos h2]

theorem currentPhase_fullPower (player : LostZonePlayerState)
    (h : 10 ≤ lostZoneCount player) : currentPhase player = .fullPower := by
  show (if lostZoneCount player < 4 then _ else _) = _
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

-- ============================================================================
-- PHASE PROGRESSION (simplified — no push_neg)
-- ============================================================================

theorem flowerSelecting_phase_nondecreasing (p0 p1 : LostZonePlayerState) (b : Bool)
    (h : flowerSelecting p0 b = some p1) :
    lostZoneCount p1 = lostZoneCount p0 + 1 :=
  flowerSelecting_lostZoneCount p0 p1 b h

theorem colress_grows_lz (player : LostZonePlayerState) (result : ColressResult)
    (hLZ : result.toLostZone.length = 2) :
    lostZoneCount (applyColressExperiment player result) = lostZoneCount player + 2 :=
  applyColressExperiment_lostZoneCount player result hLZ

theorem lostImpact_grows_lz (player next : LostZonePlayerState)
    (h : lostImpact player = some next) :
    lostZoneCount next = lostZoneCount player + 2 :=
  lostImpact_lostZoneCount player next h

-- ============================================================================
-- LOST ZONE PERMANENCE
-- ============================================================================

theorem lostZone_permanent_sendCard (player : LostZonePlayerState) (card : Card)
    (item : LostZoneItem) (h : item ∈ player.lostZone) :
    item ∈ (sendCardToLostZone player card).lostZone := by
  simp [sendCardToLostZone]; right; exact h

theorem lostZone_permanent_sendEnergy (player : LostZonePlayerState) (e : EnergyType)
    (item : LostZoneItem) (h : item ∈ player.lostZone) :
    item ∈ (sendEnergyToLostZone player e).lostZone := by
  simp [sendEnergyToLostZone]; right; exact h

theorem lostZone_permanent_colress (player : LostZonePlayerState) (result : ColressResult)
    (item : LostZoneItem) (h : item ∈ player.lostZone) :
    item ∈ (applyColressExperiment player result).lostZone := by
  simp [applyColressExperiment]; right; exact h

theorem lostZoneCount_nondecreasing_sendCard (player : LostZonePlayerState) (card : Card) :
    lostZoneCount player ≤ lostZoneCount (sendCardToLostZone player card) := by
  have hc := sendCardToLostZone_lostZoneCount player card; omega

theorem lostZoneCount_nondecreasing_colress (player : LostZonePlayerState) (result : ColressResult)
    (hLZ : result.toLostZone.length = 2) :
    lostZoneCount player ≤ lostZoneCount (applyColressExperiment player result) := by
  have hc := applyColressExperiment_lostZoneCount player result hLZ; omega

theorem threshold_permanent_sendCard (player : LostZonePlayerState) (card : Card)
    (t : LostZoneThreshold) (h : thresholdMet player t) :
    thresholdMet (sendCardToLostZone player card) t :=
  sendCard_preserves_threshold player card t h

theorem threshold_permanent_colress (player : LostZonePlayerState) (result : ColressResult)
    (t : LostZoneThreshold) (hLZ : result.toLostZone.length = 2)
    (h : thresholdMet player t) :
    thresholdMet (applyColressExperiment player result) t :=
  applyColressExperiment_preserves_threshold player result t hLZ h

-- ============================================================================
-- LOST ZONE VS DISCARD
-- ============================================================================

theorem discard_does_not_increase_lostZone (player : LostZonePlayerState) (card : Card) :
    lostZoneCount (sendCardToDiscard player card) = lostZoneCount player := by
  simp [sendCardToDiscard, lostZoneCount]

theorem lostZone_strictly_increases (player : LostZonePlayerState) (card : Card) :
    lostZoneCount (sendCardToLostZone player card) > lostZoneCount player := by
  have hc := sendCardToLostZone_lostZoneCount player card; omega

theorem lostZone_tradeoff (player : LostZonePlayerState) (card : Card) :
    lostZoneCount (sendCardToLostZone player card) = lostZoneCount player + 1 ∧
    lostZoneCount (sendCardToDiscard player card) = lostZoneCount player :=
  ⟨sendCardToLostZone_lostZoneCount player card, by simp [sendCardToDiscard, lostZoneCount]⟩

-- ============================================================================
-- TURN SEQUENCE
-- ============================================================================

inductive LostZoneAction
  | flowerSelect (chooseFirst : Bool)
  | colress (result : ColressResult)
  | lostImpactAction
  | lostVacuum (costCard : Card)
  | pass
  deriving Repr, BEq, DecidableEq

def lzGainFromAction : LostZoneAction → Nat
  | .flowerSelect _ => 1 | .colress _ => 2 | .lostImpactAction => 2
  | .lostVacuum _ => 1 | .pass => 0

-- ============================================================================
-- OPTIMAL PLAY SEQUENCES
-- ============================================================================


theorem lostImpact_eq_colress_lz_gain (result : ColressResult) :
    lzGainFromAction .lostImpactAction = lzGainFromAction (.colress result) := by
  simp [lzGainFromAction]

-- ============================================================================
-- MIRAGE GATE INTERACTION
-- ============================================================================

theorem mirageGate_preserves_lostZoneCount (player next : LostZonePlayerState)
    (h : mirageGate player = some next) :
    lostZoneCount next = lostZoneCount player := by
  have hLZ := mirageGate_lostZone player next h
  simp [lostZoneCount, hLZ]

theorem mirageGate_preserves_threshold (player next : LostZonePlayerState)
    (h : mirageGate player = some next) (t : LostZoneThreshold)
    (hMet : thresholdMet player t) : thresholdMet next t := by
  simp only [thresholdMet] at *
  have hc := mirageGate_preserves_lostZoneCount player next h; omega

theorem mirageGate_preserves_phase (player next : LostZonePlayerState)
    (h : mirageGate player = some next) :
    currentPhase next = currentPhase player := by
  have hLZ := mirageGate_preserves_lostZoneCount player next h
  simp only [currentPhase, hLZ]

end PokemonLean.LostZoneBox
