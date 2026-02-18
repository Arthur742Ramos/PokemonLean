/-
  PokemonLean / Core / ControlDeck.lean

  Control / stall archetype formalization.
  Self-contained, sorry-free, with 30+ theorems.
-/

set_option linter.unusedVariables false

namespace PokemonLean.Core.ControlDeck

-- ============================================================
-- §1  Deck-out win condition and mill-rate model
-- ============================================================

/-- A player loses by deck-out when required to draw from an empty deck. -/
def deckOutLoss (deckCount : Nat) : Prop := deckCount = 0

/-- Natural turn draw. -/
def naturalDrawPerTurn : Nat := 1

/-- Miss Fortune Sisters discard count (simplified per turn model). -/
def missFortuneDiscardPerTurn : Nat := 2

/-- Total deck destruction per turn in this control model. -/
def deckDestructionPerTurn (drawPerTurn discardPerTurn : Nat) : Nat :=
  drawPerTurn + discardPerTurn

/-- Cards removed after a fixed number of turns. -/
def destroyedCardsAfterTurns (drawPerTurn discardPerTurn turns : Nat) : Nat :=
  deckDestructionPerTurn drawPerTurn discardPerTurn * turns

/-- Remaining deck with saturating subtraction. -/
def remainingDeck (initialDeck drawPerTurn discardPerTurn turns : Nat) : Nat :=
  initialDeck - destroyedCardsAfterTurns drawPerTurn discardPerTurn turns

/-- Ceiling-division estimate for deck-out turns. -/
def turnsToDeckOut (initialDeck drawPerTurn discardPerTurn : Nat) : Nat :=
  let rate := deckDestructionPerTurn drawPerTurn discardPerTurn
  if h : rate = 0 then 0
  else (initialDeck + rate - 1) / rate

/-- [T1] Natural draw per turn is 1. -/
theorem natural_draw_value : naturalDrawPerTurn = 1 := rfl

/-- [T2] Miss Fortune Sisters discards 2 in this model. -/
theorem miss_fortune_discard_value : missFortuneDiscardPerTurn = 2 := rfl

/-- [T3] Control mill rate with draw+MFS is 3 cards/turn. -/
theorem control_mill_rate_value :
    deckDestructionPerTurn naturalDrawPerTurn missFortuneDiscardPerTurn = 3 := by
  native_decide

/-- [T4] Destroyed cards after 0 turns is 0. -/
theorem destroyed_zero_turns (d m : Nat) :
    destroyedCardsAfterTurns d m 0 = 0 := by
  simp [destroyedCardsAfterTurns]

/-- [T5] Remaining deck never exceeds initial deck. -/
theorem remaining_le_initial (initial d m t : Nat) :
    remainingDeck initial d m t ≤ initial := by
  unfold remainingDeck
  exact Nat.sub_le _ _

/-- [T6] Deck destruction is monotone in turns. -/
theorem destroyed_monotone_turns (d m t1 t2 : Nat) (h : t1 ≤ t2) :
    destroyedCardsAfterTurns d m t1 ≤ destroyedCardsAfterTurns d m t2 := by
  unfold destroyedCardsAfterTurns
  exact Nat.mul_le_mul_left _ h

/-- [T7] Remaining deck is nonincreasing in turns. -/
theorem remaining_nonincreasing (initial d m t1 t2 : Nat) (h : t1 ≤ t2) :
    remainingDeck initial d m t2 ≤ remainingDeck initial d m t1 := by
  unfold remainingDeck destroyedCardsAfterTurns
  have hm : deckDestructionPerTurn d m * t1 ≤ deckDestructionPerTurn d m * t2 :=
    Nat.mul_le_mul_left _ h
  exact Nat.sub_le_sub_left hm initial

/-- [T8] 60-card deck with rate 3 decks out in 20 turns. -/
theorem turns_to_deckout_60_at_rate3 : turnsToDeckOut 60 1 2 = 20 := by
  native_decide

/-- [T9] Remaining deck after 20 turns at rate 3 is exactly 0. -/
theorem remaining_after_20_turns_rate3 :
    remainingDeck 60 1 2 20 = 0 := by
  native_decide

/-- [T10] Remaining deck after 19 turns at rate 3 is 3 cards. -/
theorem remaining_after_19_turns_rate3 :
    remainingDeck 60 1 2 19 = 3 := by
  native_decide

/-- [T11] Deck-out loss condition is true at zero deck. -/
theorem deckout_at_zero : deckOutLoss 0 := rfl

/-- [T12] Nonzero deck is not deck-out. -/
theorem nonzero_not_deckout (n : Nat) : ¬ deckOutLoss (n + 1) := by
  unfold deckOutLoss
  omega

-- ============================================================
-- §2  Snorlax stall (Block ability)
-- ============================================================

/-- Snorlax wall HP benchmark in this control shell. -/
def snorlaxWallHP : Nat := 150

/-- Block: if active and opponent has no Switch effect, retreat is denied. -/
def retreatDeniedByBlock (blockActive hasSwitchOut : Bool) : Bool :=
  blockActive && !hasSwitchOut

/-- Opponent is stuck active under Block lock. -/
def opponentStuck (blockActive hasSwitchOut : Bool) : Prop :=
  retreatDeniedByBlock blockActive hasSwitchOut = true

/-- [T13] Snorlax wall HP is 150. -/
theorem snorlax_hp_value : snorlaxWallHP = 150 := rfl

/-- [T14] Block + no Switch means opponent is stuck. -/
theorem block_no_switch_stuck : opponentStuck true false := by
  unfold opponentStuck retreatDeniedByBlock
  native_decide

/-- [T15] Block + Switch available means opponent is not stuck. -/
theorem block_with_switch_not_stuck : ¬ opponentStuck true true := by
  unfold opponentStuck retreatDeniedByBlock
  native_decide

/-- [T16] No Block means opponent is never stuck by Block. -/
theorem no_block_not_stuck (hasSwitchOut : Bool) : ¬ opponentStuck false hasSwitchOut := by
  unfold opponentStuck retreatDeniedByBlock
  cases hasSwitchOut <;> native_decide

/-- [T17] If opponent is stuck, retreatDeniedByBlock evaluates true. -/
theorem stuck_implies_retreat_denied (b s : Bool) (h : opponentStuck b s) :
    retreatDeniedByBlock b s = true := h

/-- [T18] Retreat denied implies opponent is stuck. -/
theorem retreat_denied_implies_stuck (b s : Bool)
    (h : retreatDeniedByBlock b s = true) : opponentStuck b s := h

-- ============================================================
-- §3  Miss Fortune Sisters and Chip-Chip Ice Axe pressure
-- ============================================================

/-- Miss Fortune Sisters effect in this simplified model. -/
def missFortuneSisters (deckCount : Nat) : Nat := deckCount - 2

/-- Chip-Chip: inspect top five, choose one card index to place on top. -/
def chipChipLookCount : Nat := 5

def chipChipChoose (topCards : List Nat) (idx : Nat) : Option Nat :=
  topCards[idx]?

/-- [T19] Miss Fortune Sisters from 10 leaves 8. -/
theorem miss_fortune_from_10 : missFortuneSisters 10 = 8 := by
  native_decide

/-- [T20] Miss Fortune Sisters is nonincreasing on deck count. -/
theorem miss_fortune_nonincreasing (n : Nat) :
    missFortuneSisters n ≤ n := by
  unfold missFortuneSisters
  exact Nat.sub_le _ _

/-- [T21] Chip-Chip looks at five cards. -/
theorem chip_chip_look_count_value : chipChipLookCount = 5 := rfl

def chipChipExampleTop5 : List Nat := [9, 1, 7, 3, 5]

/-- [T22] Example Chip-Chip stack has length 5. -/
theorem chip_chip_example_length : chipChipExampleTop5.length = 5 := by
  native_decide

/-- [T23] Choosing index 0 returns the first viewed card. -/
theorem chip_chip_choose_zero : chipChipChoose chipChipExampleTop5 0 = some 9 := by
  native_decide

/-- [T24] Choosing index 3 returns the fourth viewed card. -/
theorem chip_chip_choose_three : chipChipChoose chipChipExampleTop5 3 = some 3 := by
  native_decide

/-- [T25] Choosing out-of-range index returns none. -/
theorem chip_chip_choose_out_of_range : chipChipChoose chipChipExampleTop5 9 = none := by
  native_decide

/-- [T26] Chip-Chip can force a specific top card from visible options. -/
theorem chip_chip_can_force_seen_card :
    ∃ c, chipChipChoose chipChipExampleTop5 1 = some c := by
  refine ⟨1, ?_⟩
  native_decide

-- ============================================================
-- §4  Healing, survival, and stall clock
-- ============================================================

/-- Effective damage after healing. -/
def effectiveDamagePerTurn (incomingDamage healPerTurn : Nat) : Nat :=
  incomingDamage - healPerTurn

/-- Turns to KO under repeated incoming damage and healing. -/
def turnsToKOWithHealing (hp incomingDamage healPerTurn : Nat) : Nat :=
  let net := effectiveDamagePerTurn incomingDamage healPerTurn
  if h : net = 0 then 0 else (hp + net - 1) / net

/-- Stall win precondition: survive at least required deck-out turns. -/
def stallSurvivesLongEnough (survivalTurns requiredTurns : Nat) : Prop :=
  survivalTurns ≥ requiredTurns

/-- [T27] Effective damage is never above incoming damage. -/
theorem effective_damage_le_incoming (d h : Nat) :
    effectiveDamagePerTurn d h ≤ d := by
  unfold effectiveDamagePerTurn
  exact Nat.sub_le _ _

/-- [T28] More healing means less or equal effective damage. -/
theorem more_heal_less_damage (d h1 h2 : Nat) (hh : h1 ≤ h2) :
    effectiveDamagePerTurn d h2 ≤ effectiveDamagePerTurn d h1 := by
  unfold effectiveDamagePerTurn
  exact Nat.sub_le_sub_left hh d

/-- [T29] 150 HP under 80 damage, no heal: KO in 2 turns. -/
theorem ko_clock_no_heal : turnsToKOWithHealing 150 80 0 = 2 := by
  native_decide

/-- [T30] 150 HP under 80 damage, 20 heal/turn: KO in 3 turns. -/
theorem ko_clock_with_heal : turnsToKOWithHealing 150 80 20 = 3 := by
  native_decide

/-- [T31] Healing extends survival in this benchmark. -/
theorem healing_extends_game_length :
    turnsToKOWithHealing 150 80 20 > turnsToKOWithHealing 150 80 0 := by
  rw [ko_clock_with_heal, ko_clock_no_heal]
  omega

/-- [T32] If net damage is zero, model reports no finite KO clock (0 sentinel). -/
theorem zero_net_damage_sentinel (hp d h : Nat)
    (hz : effectiveDamagePerTurn d h = 0) :
    turnsToKOWithHealing hp d h = 0 := by
  unfold turnsToKOWithHealing
  simp [hz]

/-- [T33] Surviving enough turns satisfies stall prerequisite. -/
theorem survive_enough_for_stall (s req : Nat) (h : s ≥ req) :
    stallSurvivesLongEnough s req := h

/-- [T34] Failing to survive enough turns violates stall prerequisite. -/
theorem not_survive_enough_for_stall (s req : Nat) (h : s < req) :
    ¬ stallSurvivesLongEnough s req := by
  unfold stallSurvivesLongEnough
  omega

-- ============================================================
-- §5  Matchup pacing: control vs slow and fast decks
-- ============================================================

/-- Control wins resource race if deck-out clock is at most opponent's win clock. -/
def controlWinsRace (controlDeckOutTurns opponentWinTurns : Nat) : Prop :=
  controlDeckOutTurns ≤ opponentWinTurns

/-- [T35] Control race relation is reflexive. -/
theorem control_race_reflexive (t : Nat) : controlWinsRace t t := by
  unfold controlWinsRace
  omega

/-- [T36] Slow deck example: opponent wins in 24 turns, control decks out in 20. -/
theorem control_beats_slow_deck_example : controlWinsRace 20 24 := by
  unfold controlWinsRace
  omega

/-- [T37] Fast aggro example: opponent wins in 4 turns, control at 20 loses race. -/
theorem control_loses_fast_aggro_example : ¬ controlWinsRace 20 4 := by
  unfold controlWinsRace
  omega

/-- [T38] Deck-out clock from canonical 60-card model is 20 turns. -/
theorem canonical_control_clock : turnsToDeckOut 60 1 2 = 20 :=
  turns_to_deckout_60_at_rate3

/-- [T39] If control survives 20 turns in canonical line, stall win is reachable. -/
theorem canonical_stall_reachable (surviveTurns : Nat) (h : surviveTurns ≥ 20) :
    stallSurvivesLongEnough surviveTurns (turnsToDeckOut 60 1 2) := by
  rw [turns_to_deckout_60_at_rate3]
  exact h

/-- [T40] Canonical model satisfies draw+discard = 3 cards per turn. -/
theorem canonical_rate_formula :
    deckDestructionPerTurn 1 2 = 3 := by
  native_decide

-- ============================================================
-- §6  Control-specific monotonicity and sanity checks
-- ============================================================

/-- [T41] Deck destruction after one more turn adds exactly one rate chunk. -/
theorem destroyed_next_turn (d m t : Nat) :
    destroyedCardsAfterTurns d m (t + 1) = destroyedCardsAfterTurns d m t + deckDestructionPerTurn d m := by
  unfold destroyedCardsAfterTurns
  rw [Nat.mul_add, Nat.mul_one]

/-- [T42] Remaining deck at turn 0 is initial deck. -/
theorem remaining_turn_zero (initial d m : Nat) :
    remainingDeck initial d m 0 = initial := by
  unfold remainingDeck destroyedCardsAfterTurns
  simp

/-- [T43] Deck-out from 0-card deck is immediate. -/
theorem turns_to_deckout_zero_deck : turnsToDeckOut 0 1 2 = 0 := by
  native_decide

/-- [T44] Positive destruction rate removes the zero-rate branch. -/
theorem positive_rate_unfolds_formula (deck d m : Nat)
    (h : deckDestructionPerTurn d m > 0) :
    turnsToDeckOut deck d m =
      (deck + deckDestructionPerTurn d m - 1) / deckDestructionPerTurn d m := by
  unfold turnsToDeckOut
  simp [Nat.ne_of_gt h]

/-- [T45] Control gameplan: deck destruction is monotone and non-recovering. -/
theorem control_plan_monotone_statement (d m t1 t2 : Nat) (h : t1 ≤ t2) :
    destroyedCardsAfterTurns d m t1 ≤ destroyedCardsAfterTurns d m t2 ∧
    remainingDeck 60 d m t2 ≤ remainingDeck 60 d m t1 := by
  constructor
  · exact destroyed_monotone_turns d m t1 t2 h
  · exact remaining_nonincreasing 60 d m t1 t2 h

end PokemonLean.Core.ControlDeck
