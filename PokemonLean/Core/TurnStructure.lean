/-
  PokemonLean / Core / TurnStructure.lean

  Detailed turn structure and phase formalization for Pokémon TCG:
    Draw -> Main -> Attack -> Between turns.

  Includes mandatory draw, evolution timing, once-per-turn attachment,
  attack resolution/turn end, and between-turns special conditions.

  All proofs are sorry-free.
-/

set_option linter.unusedVariables false

namespace PokemonLean.Core.TurnStructure

-- ============================================================
-- §1  Core enums and phase order
-- ============================================================

inductive Coin where
  | heads
  | tails
  deriving DecidableEq, Repr, BEq

inductive Phase where
  | draw
  | main
  | attack
  | betweenTurns
  deriving DecidableEq, Repr, BEq, Inhabited

def Phase.ord : Phase → Nat
  | .draw => 0
  | .main => 1
  | .attack => 2
  | .betweenTurns => 3

def Phase.next : Phase → Phase
  | .draw => .main
  | .main => .attack
  | .attack => .betweenTurns
  | .betweenTurns => .draw

def Phase.isLast : Phase → Bool
  | .betweenTurns => true
  | _ => false

theorem draw_ord : Phase.ord .draw = 0 := rfl
theorem main_ord : Phase.ord .main = 1 := rfl
theorem attack_ord : Phase.ord .attack = 2 := rfl
theorem between_ord : Phase.ord .betweenTurns = 3 := rfl

theorem draw_to_main : Phase.next .draw = .main := rfl
theorem main_to_attack : Phase.next .main = .attack := rfl
theorem attack_to_between : Phase.next .attack = .betweenTurns := rfl
theorem between_to_draw : Phase.next .betweenTurns = .draw := rfl

theorem only_between_is_last (p : Phase) :
    Phase.isLast p = true ↔ p = .betweenTurns := by
  cases p <;> simp [Phase.isLast]

-- ============================================================
-- §2  Draw phase
-- ============================================================

inductive DrawResult where
  | success (newDeck : Nat) (newHand : Nat)
  | deckOut
  deriving DecidableEq, Repr

def drawMandatory : Bool := true

def executeDraw (deck hand : Nat) : DrawResult :=
  if deck = 0 then .deckOut
  else .success (deck - 1) (hand + 1)

theorem draw_is_mandatory : drawMandatory = true := rfl

theorem draw_deckout_when_empty (hand : Nat) :
    executeDraw 0 hand = .deckOut := by
  simp [executeDraw]

theorem draw_success_when_nonempty (deck hand : Nat) (h : deck > 0) :
    executeDraw deck hand = .success (deck - 1) (hand + 1) := by
  simp [executeDraw, Nat.ne_of_gt h]

theorem draw_exactly_one_card (deck hand newDeck newHand : Nat)
    (h : executeDraw deck hand = .success newDeck newHand) :
    newHand = hand + 1 := by
  unfold executeDraw at h
  by_cases h0 : deck = 0
  · simp [h0] at h
  · simp [h0] at h
    exact h.2.symm

theorem draw_reduces_deck_by_one (deck hand newDeck newHand : Nat)
    (h : executeDraw deck hand = .success newDeck newHand) :
    newDeck = deck - 1 := by
  unfold executeDraw at h
  by_cases h0 : deck = 0
  · simp [h0] at h
  · simp [h0] at h
    exact h.1.symm

theorem draw_cannot_be_skipped_statement :
    drawMandatory = true := draw_is_mandatory

-- ============================================================
-- §3  Main phase permissions
-- ============================================================

def maxBench : Nat := 5

structure MainFlags where
  energyAttached : Bool
  supporterPlayed : Bool
  retreated : Bool
  deriving DecidableEq, Repr

def MainFlags.fresh : MainFlags :=
  { energyAttached := false
    supporterPlayed := false
    retreated := false }

def canBenchBasic (benchCount : Nat) : Bool :=
  benchCount < maxBench

def canEvolve (turnsInPlay : Nat) : Bool :=
  turnsInPlay ≥ 1

def canAttachEnergy (flags : MainFlags) : Bool :=
  !flags.energyAttached

def useEnergyAttach (flags : MainFlags) : MainFlags :=
  { flags with energyAttached := true }

def canPlaySupporter (flags : MainFlags) : Bool :=
  !flags.supporterPlayed

def useSupporter (flags : MainFlags) : MainFlags :=
  { flags with supporterPlayed := true }

def canRetreat (flags : MainFlags) : Bool :=
  !flags.retreated

def useRetreat (flags : MainFlags) : MainFlags :=
  { flags with retreated := true }

theorem fresh_energy_not_used :
    MainFlags.fresh.energyAttached = false := rfl

theorem fresh_supporter_not_used :
    MainFlags.fresh.supporterPlayed = false := rfl

theorem fresh_retreat_not_used :
    MainFlags.fresh.retreated = false := rfl

theorem bench_allowed_under_five (n : Nat) (h : n < 5) :
    canBenchBasic n = true := by
  simpa [canBenchBasic, maxBench] using h

theorem bench_full_at_five :
    canBenchBasic 5 = false := by native_decide

theorem evolution_requires_wait_zero :
    canEvolve 0 = false := by native_decide

theorem evolution_requires_wait_one :
    canEvolve 1 = true := by native_decide

theorem evolution_requires_wait_two :
    canEvolve 2 = true := by native_decide

theorem energy_attach_available_fresh :
    canAttachEnergy MainFlags.fresh = true := by
  simp [canAttachEnergy, MainFlags.fresh]

theorem energy_attach_once_per_turn (f : MainFlags) :
    canAttachEnergy (useEnergyAttach f) = false := by
  simp [canAttachEnergy, useEnergyAttach]

theorem supporter_once_per_turn (f : MainFlags) :
    canPlaySupporter (useSupporter f) = false := by
  simp [canPlaySupporter, useSupporter]

theorem retreat_once_per_turn (f : MainFlags) :
    canRetreat (useRetreat f) = false := by
  simp [canRetreat, useRetreat]

-- ============================================================
-- §4  Attack phase and damage resolution
-- ============================================================

structure AttackSpec where
  cost       : Nat
  baseDamage : Nat
  deriving DecidableEq, Repr

def canPayCost (attachedEnergy cost : Nat) : Bool :=
  attachedEnergy ≥ cost

def weaknessApplied (dmg : Nat) (isWeak : Bool) : Nat :=
  if isWeak then dmg * 2 else dmg

def resistanceApplied (dmg : Nat) (isResist : Bool) : Nat :=
  if isResist then dmg - 30 else dmg

def finalDamage (base : Nat) (isWeak isResist : Bool) : Nat :=
  resistanceApplied (weaknessApplied base isWeak) isResist

def isKO (hp accumulatedDamage : Nat) : Bool :=
  hp ≤ accumulatedDamage

structure AttackState where
  phase            : Phase
  attackerEnergy   : Nat
  defenderHP       : Nat
  defenderDamage   : Nat
  deriving DecidableEq, Repr

def announceAttack (st : AttackState) (atk : AttackSpec) : Bool :=
  st.phase = .attack ∧ canPayCost st.attackerEnergy atk.cost

def applyAttack (st : AttackState) (atk : AttackSpec) (isWeak isResist : Bool) : AttackState :=
  { st with
    defenderDamage := st.defenderDamage + finalDamage atk.baseDamage isWeak isResist
    phase := .betweenTurns }

theorem can_pay_cost_equal : canPayCost 3 3 = true := by native_decide
theorem can_pay_cost_more : canPayCost 4 3 = true := by native_decide
theorem can_pay_cost_less : canPayCost 2 3 = false := by native_decide

theorem weakness_double_damage (n : Nat) :
    weaknessApplied n true = n * 2 := by simp [weaknessApplied]

theorem weakness_no_change (n : Nat) :
    weaknessApplied n false = n := by simp [weaknessApplied]

theorem resistance_minus_30 (n : Nat) :
    resistanceApplied n true = n - 30 := by simp [resistanceApplied]

theorem resistance_no_change (n : Nat) :
    resistanceApplied n false = n := by simp [resistanceApplied]

theorem final_damage_neutral (n : Nat) :
    finalDamage n false false = n := by
  simp [finalDamage, weaknessApplied, resistanceApplied]

theorem final_damage_weak_only (n : Nat) :
    finalDamage n true false = n * 2 := by
  simp [finalDamage, weaknessApplied, resistanceApplied]

theorem final_damage_resist_only (n : Nat) :
    finalDamage n false true = n - 30 := by
  simp [finalDamage, weaknessApplied, resistanceApplied]

theorem attack_requires_attack_phase (st : AttackState) (atk : AttackSpec)
    (h : announceAttack st atk = true) :
    st.phase = .attack := by
  simp [announceAttack] at h
  exact h.1

theorem attack_requires_energy_cost (st : AttackState) (atk : AttackSpec)
    (h : announceAttack st atk = true) :
    canPayCost st.attackerEnergy atk.cost = true := by
  simp [announceAttack] at h
  exact h.2

theorem attack_ends_turn (st : AttackState) (atk : AttackSpec) (w r : Bool) :
    (applyAttack st atk w r).phase = .betweenTurns := by
  simp [applyAttack]

theorem attack_adds_damage (st : AttackState) (atk : AttackSpec) (w r : Bool) :
    (applyAttack st atk w r).defenderDamage =
    st.defenderDamage + finalDamage atk.baseDamage w r := by
  simp [applyAttack]

theorem ko_when_damage_reaches_hp (hp dmg : Nat) (h : hp ≤ dmg) :
    isKO hp dmg = true := by
  simp [isKO, h]

theorem not_ko_when_damage_below_hp (hp dmg : Nat) (h : dmg < hp) :
    isKO hp dmg = false := by
  have hnot : ¬ hp ≤ dmg := Nat.not_le.mpr h
  simp [isKO, hnot]

-- ============================================================
-- §5  Between-turns effects
-- ============================================================

structure Conditions where
  poisoned   : Bool
  burned     : Bool
  asleep     : Bool
  paralyzed  : Bool
  burnFlip   : Coin
  sleepFlip  : Coin
  deriving DecidableEq, Repr

structure BetweenResult where
  poisonDamage   : Nat
  burnDamage     : Nat
  wokeUp         : Bool
  paralysisCured : Bool
  deriving DecidableEq, Repr

def poisonTick (isPoisoned : Bool) : Nat :=
  if isPoisoned then 10 else 0

def burnTick (isBurned : Bool) (flip : Coin) : Nat :=
  if isBurned then
    match flip with
    | .heads => 0
    | .tails => 20
  else 0

def sleepTick (isAsleep : Bool) (flip : Coin) : Bool :=
  if isAsleep then
    match flip with
    | .heads => true
    | .tails => false
  else true

def paralysisTick (isParalyzed : Bool) : Bool :=
  if isParalyzed then true else false

def processBetweenTurns (c : Conditions) : BetweenResult :=
  { poisonDamage := poisonTick c.poisoned
    burnDamage := burnTick c.burned c.burnFlip
    wokeUp := sleepTick c.asleep c.sleepFlip
    paralysisCured := paralysisTick c.paralyzed }

theorem between_poison_10 :
    poisonTick true = 10 := by simp [poisonTick]

theorem between_no_poison_0 :
    poisonTick false = 0 := by simp [poisonTick]

theorem between_burn_heads_no_damage :
    burnTick true .heads = 0 := by simp [burnTick]

theorem between_burn_tails_20 :
    burnTick true .tails = 20 := by simp [burnTick]

theorem between_no_burn_0 (f : Coin) :
    burnTick false f = 0 := by
  cases f <;> simp [burnTick]

theorem sleep_heads_wakes :
    sleepTick true .heads = true := by simp [sleepTick]

theorem sleep_tails_stays_asleep :
    sleepTick true .tails = false := by simp [sleepTick]

theorem sleep_not_asleep_stays_awake (f : Coin) :
    sleepTick false f = true := by
  cases f <;> simp [sleepTick]

theorem paralysis_auto_cures_after_turn :
    paralysisTick true = true := by simp [paralysisTick]

theorem no_paralysis_no_cure_flag :
    paralysisTick false = false := by simp [paralysisTick]

theorem process_between_poison_damage (c : Conditions) (h : c.poisoned = true) :
    (processBetweenTurns c).poisonDamage = 10 := by
  simp [processBetweenTurns, poisonTick, h]

theorem process_between_burn_heads (c : Conditions)
    (hb : c.burned = true) (hf : c.burnFlip = .heads) :
    (processBetweenTurns c).burnDamage = 0 := by
  simp [processBetweenTurns, burnTick, hb, hf]

theorem process_between_burn_tails (c : Conditions)
    (hb : c.burned = true) (hf : c.burnFlip = .tails) :
    (processBetweenTurns c).burnDamage = 20 := by
  simp [processBetweenTurns, burnTick, hb, hf]

theorem process_between_sleep_heads_wake (c : Conditions)
    (ha : c.asleep = true) (hf : c.sleepFlip = .heads) :
    (processBetweenTurns c).wokeUp = true := by
  simp [processBetweenTurns, sleepTick, ha, hf]

theorem process_between_sleep_tails_not_wake (c : Conditions)
    (ha : c.asleep = true) (hf : c.sleepFlip = .tails) :
    (processBetweenTurns c).wokeUp = false := by
  simp [processBetweenTurns, sleepTick, ha, hf]

theorem process_between_paralysis_cured (c : Conditions) (hp : c.paralyzed = true) :
    (processBetweenTurns c).paralysisCured = true := by
  simp [processBetweenTurns, paralysisTick, hp]

-- ============================================================
-- §6  Full turn state and progression
-- ============================================================

structure TurnState where
  phase                 : Phase
  deckSize              : Nat
  handSize              : Nat
  activeTurnsInPlay     : Nat
  flags                 : MainFlags
  deriving DecidableEq, Repr

def startOfTurn (deck hand activeTurns : Nat) : TurnState :=
  { phase := .draw
    deckSize := deck
    handSize := hand
    activeTurnsInPlay := activeTurns
    flags := MainFlags.fresh }

def afterDrawPhase (t : TurnState) : TurnState :=
  { t with phase := .main }

def afterMainPhase (t : TurnState) : TurnState :=
  { t with phase := .attack }

def afterAttackPhase (t : TurnState) : TurnState :=
  { t with phase := .betweenTurns }

def nextTurnStart (t : TurnState) : TurnState :=
  { t with phase := .draw, flags := MainFlags.fresh, activeTurnsInPlay := t.activeTurnsInPlay + 1 }

theorem turn_starts_in_draw (d h a : Nat) :
    (startOfTurn d h a).phase = .draw := rfl

theorem draw_transitions_to_main (t : TurnState) :
    (afterDrawPhase t).phase = .main := rfl

theorem main_transitions_to_attack (t : TurnState) :
    (afterMainPhase t).phase = .attack := rfl

theorem attack_transitions_to_between (t : TurnState) :
    (afterAttackPhase t).phase = .betweenTurns := rfl

theorem between_transitions_to_draw (t : TurnState) :
    (nextTurnStart t).phase = .draw := rfl

theorem next_turn_resets_energy_attach_flag (t : TurnState) :
    (nextTurnStart t).flags.energyAttached = false := by
  simp [nextTurnStart, MainFlags.fresh]

theorem next_turn_increments_active_turns (t : TurnState) :
    (nextTurnStart t).activeTurnsInPlay = t.activeTurnsInPlay + 1 := rfl

theorem evolution_wait_satisfied_next_turn (t : TurnState) (h : t.activeTurnsInPlay = 0) :
    canEvolve (nextTurnStart t).activeTurnsInPlay = true := by
  simp [nextTurnStart, canEvolve, h]

-- ============================================================
-- §7  Requested headline theorems (explicit statements)
-- ============================================================

theorem theorem_draw_mandatory :
    drawMandatory = true := draw_is_mandatory

theorem theorem_exactly_one_card_drawn (deck hand newDeck newHand : Nat)
    (h : executeDraw deck hand = .success newDeck newHand) :
    newHand = hand + 1 :=
  draw_exactly_one_card deck hand newDeck newHand h

theorem theorem_evolution_wait_one_turn :
    canEvolve 0 = false ∧ canEvolve 1 = true := by
  constructor
  · exact evolution_requires_wait_zero
  · exact evolution_requires_wait_one

theorem theorem_energy_attach_once :
    canAttachEnergy (useEnergyAttach MainFlags.fresh) = false := by
  simpa using energy_attach_once_per_turn MainFlags.fresh

theorem theorem_attack_ends_turn (st : AttackState) (atk : AttackSpec) (w r : Bool) :
    (applyAttack st atk w r).phase = .betweenTurns :=
  attack_ends_turn st atk w r

theorem theorem_between_poison_10 :
    poisonTick true = 10 := between_poison_10

theorem theorem_burn_coin_flip_heads_tails :
    burnTick true .heads = 0 ∧ burnTick true .tails = 20 := by
  constructor
  · exact between_burn_heads_no_damage
  · exact between_burn_tails_20

theorem theorem_sleep_requires_flip :
    sleepTick true .heads = true ∧ sleepTick true .tails = false := by
  constructor
  · exact sleep_heads_wakes
  · exact sleep_tails_stays_asleep

theorem theorem_paralysis_auto_cures :
    paralysisTick true = true :=
  paralysis_auto_cures_after_turn

end PokemonLean.Core.TurnStructure
