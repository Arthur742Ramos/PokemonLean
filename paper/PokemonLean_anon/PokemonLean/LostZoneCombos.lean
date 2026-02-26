import PokemonLean.Basic
import PokemonLean.LostZone
import PokemonLean.LostZoneThresholds

namespace PokemonLean.LostZoneCombos

open PokemonLean.LostZone
open PokemonLean.LostZoneThresholds

-- ============================================================================
-- MULTI-CARD COMBO SEQUENCES
-- ============================================================================

-- ============================================================================
-- FLOWER SELECTING + COLRESS CHAINS
-- ============================================================================

theorem flower_then_colress_lz
    (p0 p1 : LostZonePlayerState) (b : Bool) (result : ColressResult)
    (hFlower : flowerSelecting p0 b = some p1)
    (hLZ : result.toLostZone.length = 2) :
    lostZoneCount (applyColressExperiment p1 result) = lostZoneCount p0 + 3 := by
  have h1 := flowerSelecting_lostZoneCount p0 p1 b hFlower
  have h2 := applyColressExperiment_lostZoneCount p1 result hLZ
  omega

theorem colress_then_flower_lz
    (p0 p1 : LostZonePlayerState) (result : ColressResult) (b : Bool)
    (hLZ : result.toLostZone.length = 2)
    (hFlower : flowerSelecting (applyColressExperiment p0 result) b = some p1) :
    lostZoneCount p1 = lostZoneCount p0 + 3 := by
  have h1 := applyColressExperiment_lostZoneCount p0 result hLZ
  have h2 := flowerSelecting_lostZoneCount (applyColressExperiment p0 result) p1 b hFlower
  omega

theorem double_colress_lz (p0 : LostZonePlayerState) (r1 r2 : ColressResult)
    (hLZ1 : r1.toLostZone.length = 2) (hLZ2 : r2.toLostZone.length = 2) :
    lostZoneCount (applyColressExperiment (applyColressExperiment p0 r1) r2) =
      lostZoneCount p0 + 4 := by
  have h1 := applyColressExperiment_lostZoneCount p0 r1 hLZ1
  have h2 := applyColressExperiment_lostZoneCount (applyColressExperiment p0 r1) r2 hLZ2
  omega

-- ============================================================================
-- GIRATINA VSTAR LOST IMPACT COMBOS
-- ============================================================================

def giratinaLostImpactDamage : Nat := 280
@[simp] theorem giratinaLostImpactDamage_value : giratinaLostImpactDamage = 280 := rfl

theorem lostImpact_kos_if_hp_le_280 (target : PokemonInPlay)
    (hHP : target.card.hp ≤ 280) (hNoDmg : target.damage = 0) :
    (applyDamage target giratinaLostImpactDamage).damage = target.card.hp := by
  exact applyDamage_damage_eq_hp target 280 (by omega)

theorem lostImpact_kos_with_prior_damage (target : PokemonInPlay)
    (hHP : target.card.hp ≤ target.damage + 280) :
    (applyDamage target giratinaLostImpactDamage).damage = target.card.hp := by
  exact applyDamage_damage_eq_hp target 280 hHP

theorem lostImpact_enables_sableye (player next : LostZonePlayerState)
    (h : lostImpact player = some next) (hCount : lostZoneCount player = 8) :
    thresholdMet next .lostMine := by
  have hLZ := lostImpact_lostZoneCount player next h
  simp only [thresholdMet, thresholdValue]; omega

theorem lostImpact_reaches_mirage (player next : LostZonePlayerState)
    (h : lostImpact player = some next) (hCount : 5 ≤ lostZoneCount player) :
    thresholdMet next .mirageGate := by
  have hLZ := lostImpact_lostZoneCount player next h
  simp only [thresholdMet, thresholdValue]; omega

-- ============================================================================
-- SABLEYE LOST MINE SPREAD DAMAGE
-- ============================================================================

theorem sableye_kos_low_hp (attacker : LostZonePlayerState) (target : PokemonInPlay)
    (hCount : 10 ≤ lostZoneCount attacker)
    (hHP : target.card.hp ≤ 120) (hNoDmg : target.damage = 0) :
    ∃ damaged, sableyeLostMine attacker target = some damaged ∧
      damaged.damage = target.card.hp := by
  refine ⟨applyDamage target lostMineDamage, sableyeLostMine_some_of_ten attacker target hCount, ?_⟩
  simp [lostMineDamage, lostMineDamageCounters]
  exact applyDamage_damage_eq_hp target 120 (by omega)

theorem sableye_no_ko_high_hp (attacker : LostZonePlayerState) (target : PokemonInPlay)
    (hCount : 10 ≤ lostZoneCount attacker)
    (hHP : 120 < target.card.hp) (hNoDmg : target.damage = 0) :
    ∃ damaged, sableyeLostMine attacker target = some damaged ∧
      damaged.damage = 120 ∧ damaged.damage < target.card.hp := by
  refine ⟨applyDamage target lostMineDamage, sableyeLostMine_some_of_ten attacker target hCount, ?_, ?_⟩
  · simp [lostMineDamage, lostMineDamageCounters]
    have := applyDamage_damage_eq_add target 120 (by omega)
    simp [hNoDmg] at this; exact this
  · simp [lostMineDamage, lostMineDamageCounters]
    have := applyDamage_damage_eq_add target 120 (by omega)
    simp [hNoDmg] at this; rw [this]; omega

-- ============================================================================
-- CRAMORANT + MIRAGE GATE COMBO
-- ============================================================================

theorem provision_and_mirage_at_seven (player : LostZonePlayerState)
    (h : 7 ≤ lostZoneCount player) :
    thresholdMet player .provision ∧ thresholdMet player .mirageGate := by
  constructor
  · exact mirageGate_met_implies_provision player h
  · exact h

theorem cramorant_then_mirageGate_valid
    (attacker : LostZonePlayerState) (target : PokemonInPlay)
    (h7 : 7 ≤ lostZoneCount attacker) :
    ∃ damaged, cramorantLostProvision attacker target = some damaged := by
  exact ⟨applyDamage target cramorantLostProvisionDamage,
    cramorantLostProvision_some_of_four attacker target (by omega)⟩

-- ============================================================================
-- LOST VACUUM DISRUPTION COMBOS
-- ============================================================================

theorem lostVacuum_cost_advances_threshold
    (player next : LostZonePlayerState) (costCard : Card) (t : LostZoneThreshold)
    (hPay : payLostVacuumCost player costCard = some next)
    (hAlmost : thresholdValue t ≤ lostZoneCount player + 1) :
    thresholdMet next t := by
  have hCount := payLostVacuumCost_lostZoneCount player next costCard hPay
  simp only [thresholdMet]; omega

theorem lostVacuum_then_flower_lz
    (p0 p1 p2 : LostZonePlayerState) (costCard : Card) (b : Bool)
    (hPay : payLostVacuumCost p0 costCard = some p1)
    (hFlower : flowerSelecting p1 b = some p2) :
    lostZoneCount p2 = lostZoneCount p0 + 2 := by
  have h1 := payLostVacuumCost_lostZoneCount p0 p1 costCard hPay
  have h2 := flowerSelecting_lostZoneCount p1 p2 b hFlower; omega

-- ============================================================================
-- LOST CITY STADIUM COMBOS
-- ============================================================================

theorem lostCity_ko_advances_threshold
    (player : LostZonePlayerState) (active : PokemonInPlay) (t : LostZoneThreshold)
    (hActive : player.active = some active)
    (hAlmost : thresholdValue t ≤ lostZoneCount player + 1) :
    thresholdMet (lostCityKO true player) t := by
  have hCount := lostCityKO_true_lostZoneCount player active hActive
  simp only [thresholdMet]; omega

theorem normal_ko_no_lz_advance (player : LostZonePlayerState) :
    lostZoneCount (knockOutActiveToDiscard player) = lostZoneCount player := by
  cases hActive : player.active with
  | none => simp [knockOutActiveToDiscard, hActive, lostZoneCount]
  | some active => simp [knockOutActiveToDiscard, hActive, lostZoneCount]

-- ============================================================================
-- ENERGY MANAGEMENT WITH LOST ZONE
-- ============================================================================

theorem lostImpact_energy_loss (player next : LostZonePlayerState)
    (h : lostImpact player = some next) :
    ∃ active nextActive e1 e2 rest,
      player.active = some active ∧ next.active = some nextActive ∧
      active.energy = e1 :: e2 :: rest ∧ nextActive.energy = rest := by
  cases hActive : player.active with
  | none => simp [lostImpact, hActive] at h
  | some active =>
    cases hEnergy : active.energy with
    | nil => simp [lostImpact, hActive, hEnergy] at h
    | cons e1 tail =>
      cases tail with
      | nil => simp [lostImpact, hActive, hEnergy] at h
      | cons e2 rest =>
        simp only [lostImpact, hActive, hEnergy] at h
        cases h
        exact ⟨active, _, e1, e2, rest, rfl, rfl, hEnergy, rfl⟩

theorem mirageGate_restores_energy (player next : LostZonePlayerState)
    (h : mirageGate player = some next) :
    ∃ active nextActive e1 e2,
      player.active = some active ∧ next.active = some nextActive ∧
      nextActive.energy = e1 :: e2 :: active.energy := by
  unfold mirageGate at h
  split at h
  · cases hActive : player.active with
    | none => simp [hActive] at h
    | some active =>
      cases hDeck : player.energyDeck with
      | nil => simp [hActive, hDeck] at h
      | cons e1 tail =>
        cases tail with
        | nil => simp [hActive, hDeck] at h
        | cons e2 rest =>
          simp only [hActive, hDeck] at h
          cases h
          exact ⟨active, _, e1, e2, rfl, rfl, rfl⟩
  · simp at h

theorem lostImpact_mirageGate_energy_cycle
    (p0 p1 p2 : LostZonePlayerState)
    (hImpact : lostImpact p0 = some p1)
    (hMirage : mirageGate p1 = some p2) :
    ∃ active0 active2,
      p0.active = some active0 ∧ p2.active = some active2 ∧
      active2.energy.length = active0.energy.length := by
  obtain ⟨a0, a1, e1, e2, rest, hA0, hA1, hE0, hE1⟩ := lostImpact_energy_loss p0 p1 hImpact
  obtain ⟨a1', a2, f1, f2, hA1', hA2, hE2⟩ := mirageGate_restores_energy p1 p2 hMirage
  rw [hA1] at hA1'; simp at hA1'; subst hA1'
  exact ⟨a0, a2, hA0, hA2, by rw [hE2, hE1, hE0]; simp⟩

-- ============================================================================
-- FULL COMBO: REACH FULL POWER FROM ZERO
-- ============================================================================


-- ============================================================================
-- DAMAGE CALCULATION COMBOS
-- ============================================================================

theorem cramorant_sableye_total_damage :
    cramorantLostProvisionDamage + lostMineDamage = 230 := by
  simp [cramorantLostProvisionDamage, lostMineDamage, lostMineDamageCounters]

theorem double_cramorant_damage :
    cramorantLostProvisionDamage + cramorantLostProvisionDamage = 220 := by
  simp [cramorantLostProvisionDamage]

theorem giratina_oneshots_vstar (hp : Nat) (h : hp ≤ 280) :
    hp ≤ giratinaLostImpactDamage := by
  simp [giratinaLostImpactDamage]; exact h

theorem cramorant_giratina_total :
    cramorantLostProvisionDamage + giratinaLostImpactDamage = 390 := by
  simp [cramorantLostProvisionDamage, giratinaLostImpactDamage]

-- ============================================================================
-- HAND SIZE MANAGEMENT
-- ============================================================================

theorem colress_hand_economy (player : LostZonePlayerState) (result : ColressResult)
    (hHand : result.toHand.length = 3) (hLZ : result.toLostZone.length = 2) :
    (applyColressExperiment player result).hand.length = player.hand.length + 3 ∧
    lostZoneCount (applyColressExperiment player result) = lostZoneCount player + 2 :=
  ⟨applyColressExperiment_hand_length player result hHand,
   applyColressExperiment_lostZoneCount player result hLZ⟩

theorem flower_hand_economy (p0 p1 : LostZonePlayerState) (b : Bool)
    (h : flowerSelecting p0 b = some p1) :
    p1.hand.length = p0.hand.length + 1 ∧
    lostZoneCount p1 = lostZoneCount p0 + 1 :=
  ⟨flowerSelecting_hand_length p0 p1 b h, flowerSelecting_lostZoneCount p0 p1 b h⟩

theorem lostVacuum_hand_economy (player next : LostZonePlayerState) (costCard : Card)
    (h : payLostVacuumCost player costCard = some next) :
    next.hand.length + 1 = player.hand.length ∧
    lostZoneCount next = lostZoneCount player + 1 :=
  ⟨payLostVacuumCost_hand_length player next costCard h,
   payLostVacuumCost_lostZoneCount player next costCard h⟩

end PokemonLean.LostZoneCombos
