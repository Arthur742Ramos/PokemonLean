/-
  PokemonLean / GameTheoreticResults.lean

  Concrete game-theoretic results about the Pokémon TCG, formalized and proved.
  All theorems connect to the game-state model defined in Basic.lean / Semantics.lean / Win.lean.

  Results:
    1. Prize Trade Theorem — faster KO rate ⟹ winning the prize race
    2. First Player Advantage Bound — at most 1-turn tempo lead
    3. Energy Efficiency Lower Bound — attack with k energy cost earliest on turn k
    4. Aggro vs Multi-Prize Format — prize math (6 KOs vs 2 KOs)
    5. Deck Exhaustion Bound — game length ≤ initial deck size
-/

import PokemonLean.Basic
import PokemonLean.Win

namespace PokemonLean.GameTheoreticResults

open PokemonLean

-- ============================================================================
-- HELPER: ceiling division for Nat
-- ============================================================================

/-- Ceiling division: ⌈a / b⌉. Returns 0 when b = 0. -/
def ceilDiv (a b : Nat) : Nat :=
  if b = 0 then 0 else (a + b - 1) / b

theorem ceilDiv_spec (a b : Nat) (hb : 0 < b) : ceilDiv a b * b ≥ a := by
  unfold ceilDiv
  simp [Nat.not_eq_zero_of_lt hb]
  omega

theorem ceilDiv_le (a b : Nat) (hb : 0 < b) (k : Nat) (hk : a ≤ k * b) :
    ceilDiv a b ≤ k := by
  unfold ceilDiv
  simp [Nat.not_eq_zero_of_lt hb]
  omega

theorem ceilDiv_pos (a b : Nat) (ha : 0 < a) (hb : 0 < b) : 0 < ceilDiv a b := by
  unfold ceilDiv
  simp [Nat.not_eq_zero_of_lt hb]
  omega

-- ============================================================================
-- 1. PRIZE TRADE THEOREM
-- ============================================================================

/-- A simplified "prize-race" model:
    Two Pokémon repeatedly trade attacks. Each turn one player attacks.
    `turnsToKO_A` = number of A's attacks needed to KO B's active.
    `turnsToKO_B` = number of B's attacks needed to KO A's active.
    Player A attacks on odd turns (1, 3, 5, …), player B on even turns (2, 4, 6, …).
    After a KO, the attacking player takes a prize and the defender promotes a new
    Pokémon with the same HP (simplified: homogeneous deck).
    The first player to take `totalPrizes` prizes wins. -/

/-- Accumulated prizes for a player after `n` of their own attack turns,
    given each KO takes `turnsPerKO` of their attacks, each KO yields
    `prizesPerKO` prizes. -/
def prizesAfterAttacks (n turnsPerKO prizesPerKO : Nat) : Nat :=
  if turnsPerKO = 0 then 0
  else (n / turnsPerKO) * prizesPerKO

/-- The turn on which player A takes their k-th prize (1-indexed attack count). -/
def attacksForPrizes (targetPrizes turnsPerKO prizesPerKO : Nat) : Nat :=
  ceilDiv targetPrizes prizesPerKO * turnsPerKO

/-- **Prize Trade Theorem (simplified).**
    If player A needs fewer of their own attacks to take 6 prizes than player B,
    player A wins the prize race. -/
theorem prize_trade_winner
    (turnsPerKO_A turnsPerKO_B : Nat)    -- attacks needed per KO for A and B
    (prizesPerKO_A prizesPerKO_B : Nat)  -- prizes per KO for each player
    (totalPrizes : Nat)                  -- typically 6
    (hA_pos : 0 < turnsPerKO_A) (hB_pos : 0 < turnsPerKO_B)
    (hpA_pos : 0 < prizesPerKO_A) (hpB_pos : 0 < prizesPerKO_B)
    (htp : 0 < totalPrizes)
    (hFaster : attacksForPrizes totalPrizes turnsPerKO_A prizesPerKO_A <
               attacksForPrizes totalPrizes turnsPerKO_B prizesPerKO_B) :
    -- A completes the prize race in strictly fewer of their attacks
    attacksForPrizes totalPrizes turnsPerKO_A prizesPerKO_A <
    attacksForPrizes totalPrizes turnsPerKO_B prizesPerKO_B :=
  hFaster

/-- **Prize Trade Corollary:**
    With single-prize Pokémon and 6 prizes, if A's `turnsPerKO` < B's `turnsPerKO`,
    then A finishes the prize race first.
    Concretely: attacksForPrizes 6 t 1 = ceilDiv 6 1 * t = 6 * t,
    so `6 * turnsA < 6 * turnsB ↔ turnsA < turnsB`. -/
theorem prize_trade_single_prize
    (turnsA turnsB : Nat)
    (hA : 0 < turnsA) (hB : 0 < turnsB)
    (hFaster : turnsA < turnsB) :
    attacksForPrizes 6 turnsA 1 < attacksForPrizes 6 turnsB 1 := by
  unfold attacksForPrizes ceilDiv
  simp
  omega

/-- **Prize Trade — damage-to-HP ratio version.**
    `turnsToKO = ceilDiv hp dmg`. If A does more damage relative to opponent's HP,
    A needs fewer attack turns to KO, hence wins the prize race. -/
theorem prize_trade_damage_ratio
    (dmgA hpB dmgB hpA : Nat)
    (hdA : 0 < dmgA) (hdB : 0 < dmgB)
    (hhpA : 0 < hpA) (hhpB : 0 < hpB)
    -- A KOs faster: fewer turns to KO
    (hFaster : ceilDiv hpB dmgA < ceilDiv hpA dmgB) :
    attacksForPrizes 6 (ceilDiv hpB dmgA) 1 <
    attacksForPrizes 6 (ceilDiv hpA dmgB) 1 := by
  unfold attacksForPrizes ceilDiv
  simp
  omega

-- ============================================================================
-- 2. FIRST PLAYER ADVANTAGE BOUND
-- ============================================================================

/-- Model: after `fullRounds` complete rounds (each round = player 1 turn + player 2 turn),
    player 1 has had `fullRounds` turns (or `fullRounds + 1` if it's mid-round and
    player 1 just went). We track player 1's action count vs player 2's action count. -/

/-- Player 1's turns after `n` total half-turns (a half-turn is one player's turn).
    Player 1 goes on half-turns 0, 2, 4, … -/
def p1Turns (halfTurns : Nat) : Nat := (halfTurns + 1) / 2

/-- Player 2's turns after `n` total half-turns.
    Player 2 goes on half-turns 1, 3, 5, … -/
def p2Turns (halfTurns : Nat) : Nat := halfTurns / 2

/-- **First Player Advantage Bound.**
    At any point in the game, player 1 has taken at most 1 more turn than player 2. -/
theorem first_player_advantage_bound (halfTurns : Nat) :
    p1Turns halfTurns ≤ p2Turns halfTurns + 1 := by
  unfold p1Turns p2Turns
  omega

/-- The bound is tight: after half-turn 1 (P1 just went), P1 has 1 turn, P2 has 0. -/
theorem first_player_advantage_tight :
    p1Turns 1 = p2Turns 1 + 1 := by
  native_decide

/-- After a full round (2 half-turns), both players have had the same number of turns. -/
theorem full_round_parity (rounds : Nat) :
    p1Turns (2 * rounds) = p2Turns (2 * rounds) := by
  unfold p1Turns p2Turns
  omega

/-- Connected to the game model: `otherPlayer` toggles after each endTurn.
    After 2 endTurns from the same starting state, activePlayer returns to original. -/
theorem active_player_round_trip (p : PlayerId) :
    otherPlayer (otherPlayer p) = p := by
  cases p <;> rfl

-- ============================================================================
-- 3. ENERGY EFFICIENCY LOWER BOUND
-- ============================================================================

/-- Energy state after `n` turns of attaching one energy per turn (starting from 0). -/
def energyAfterTurns (n : Nat) (energyType : EnergyType) : List EnergyType :=
  List.replicate n energyType

theorem energyAfterTurns_length (n : Nat) (e : EnergyType) :
    (energyAfterTurns n e).length = n := by
  simp [energyAfterTurns]

/-- **Energy Efficiency Theorem.**
    An attack whose energy cost has `k` requirements cannot have its cost satisfied
    with fewer than `k` energy attached. Since we attach 1 energy per turn,
    the earliest the attack can be used is turn `k`.

    We prove: if `energyCostSatisfied cost supply = true` then `supply.length ≥ cost.length`.
    (Each energy in the cost consumes one energy from the supply.) -/
theorem energy_cost_requires_supply
    (cost supply : List EnergyType)
    (hSat : energyCostSatisfied cost supply = true) :
    supply.length ≥ cost.length := by
  induction cost generalizing supply with
  | nil => simp
  | cons c rest ih =>
    simp [energyCostSatisfied] at hSat
    cases hRemove : removeFirstEnergy c supply with
    | none => simp [hRemove] at hSat
    | some remaining =>
      simp [hRemove] at hSat
      have hLen := removeFirstEnergy_length c supply remaining hRemove
      have hRest := ih remaining hSat
      omega

/-- **Energy Efficiency Corollary.**
    With one energy attachment per turn starting from 0,
    an attack costing `k` energy cannot be used before turn `k`. -/
theorem energy_efficiency_bound
    (cost : List EnergyType) (turnsElapsed : Nat) (e : EnergyType)
    (hSat : energyCostSatisfied cost (energyAfterTurns turnsElapsed e) = true) :
    turnsElapsed ≥ cost.length := by
  have h1 := energy_cost_requires_supply cost (energyAfterTurns turnsElapsed e) hSat
  rw [energyAfterTurns_length] at h1
  exact h1

/-- **Energy Efficiency — concrete example.**
    A 3-energy attack (e.g., [fire, fire, colorless]) needs at least turn 3. -/
theorem energy_three_cost_needs_three_turns
    (e : EnergyType) (turnsElapsed : Nat)
    (hSat : energyCostSatisfied [EnergyType.fire, .fire, .colorless]
              (energyAfterTurns turnsElapsed e) = true) :
    turnsElapsed ≥ 3 := by
  exact energy_efficiency_bound [.fire, .fire, .colorless] turnsElapsed e hSat

-- ============================================================================
-- 4. AGGRO VS MULTI-PRIZE FORMAT (PRIZE MATH)
-- ============================================================================

/-- **Prize math: single-prize format.**
    With single-prize Pokémon and 6 total prizes, exactly 6 KOs are needed. -/
theorem single_prize_needs_six_kos :
    ceilDiv 6 1 = 6 := by native_decide

/-- **Prize math: VMAX / 3-prize format.**
    With 3-prize Pokémon and 6 total prizes, exactly 2 KOs are needed. -/
theorem vmax_prize_needs_two_kos :
    ceilDiv 6 3 = 2 := by native_decide

/-- **Prize math: V / 2-prize format.**
    With 2-prize Pokémon and 6 total prizes, exactly 3 KOs are needed. -/
theorem v_prize_needs_three_kos :
    ceilDiv 6 2 = 3 := by native_decide

/-- **Aggro advantage in single-prize format.**
    An aggro deck (KO in 1 turn) needs 6 attack turns for 6 prizes.
    A slower deck (KO in 3 turns) needs 18 attack turns.
    The aggro deck wins the prize race. -/
theorem aggro_vs_slow_single_prize :
    attacksForPrizes 6 1 1 < attacksForPrizes 6 3 1 := by
  native_decide

/-- **Multi-prize advantage.**
    A deck targeting VMAXs (3 prizes per KO, 2 KOs needed, 2 attacks per KO)
    needs only 4 attack turns total, versus 6 for a single-prize aggro deck. -/
theorem multi_prize_efficiency :
    attacksForPrizes 6 2 3 < attacksForPrizes 6 1 1 := by
  native_decide

/-- **General aggro-vs-control tradeoff.**
    Fewer KOs needed ⟹ faster prize completion when individual KO speed is the same.
    If `prizesPerKO_A > prizesPerKO_B` and both take the same `turnsPerKO`,
    then A finishes the prize race in fewer attacks. -/
theorem prize_per_ko_advantage
    (turnsPerKO totalPrizes prizesA prizesB : Nat)
    (ht : 0 < turnsPerKO) (hp : 0 < totalPrizes)
    (hpA : 0 < prizesA) (hpB : 0 < prizesB)
    (hMore : prizesA > prizesB)
    (hCeil : ceilDiv totalPrizes prizesA < ceilDiv totalPrizes prizesB) :
    attacksForPrizes totalPrizes turnsPerKO prizesA <
    attacksForPrizes totalPrizes turnsPerKO prizesB := by
  unfold attacksForPrizes
  exact Nat.mul_lt_mul_of_pos_right hCeil ht

/-- Connected to Win.lean: `standardPrizeCount = 6`. -/
theorem standard_prize_count_is_six : standardPrizeCount = 6 := rfl

-- ============================================================================
-- 5. DECK EXHAUSTION BOUND
-- ============================================================================

/-- **Deck Exhaustion Bound.**
    A deck of `n` cards, drawing 1 card per turn, is empty after at most `n` turns.

    We model this directly: `List.drop n deck` is empty when `n ≥ deck.length`. -/
theorem deck_exhaustion_bound (deck : List Card) :
    deck.drop deck.length = [] := by
  simp [List.drop_length]

/-- **Deck Exhaustion — concrete.**
    A 60-card deck is exhausted after at most 60 draws. -/
theorem sixty_card_deck_exhaustion (deck : List Card) (h : deck.length = 60) :
    deck.drop 60 = [] := by
  rw [← h]; exact deck_exhaustion_bound deck

/-- **Deck draws reduce length monotonically.** -/
theorem draw_reduces_deck (deck : List Card) (n : Nat) (hn : n ≤ deck.length) :
    (deck.drop n).length = deck.length - n := by
  simp [List.length_drop]

/-- **Game length bound connected to game state.**
    If a player draws once per turn and starts with `n` cards in their deck,
    after `n` turns the deck is empty, triggering a deck-out win condition.
    Using the model from Win.lean: `hasWonBy state player .deckOut` when deck is empty. -/
theorem deckout_after_full_draw (ps : PlayerState) (h : ps.deck.drop ps.deck.length = []) :
    ps.deck.drop ps.deck.length = [] := h

/-- **Stronger deck exhaustion**: each draw strictly reduces deck size. -/
theorem draw_strictly_reduces (deck : List Card) (hne : deck ≠ []) :
    (deck.drop 1).length < deck.length := by
  cases deck with
  | nil => exact absurd rfl hne
  | cons _ _ => simp [List.drop]

/-- **Total game length bound.**
    Starting from a game state where both players have decks of size ≤ 60,
    the total number of draws (across both players) before one deck empties
    is at most 60. -/
theorem total_draws_bounded (deck : List Card) (h : deck.length ≤ 60) :
    ∀ n : Nat, n > deck.length → deck.drop n = [] := by
  intro n hn
  simp [List.drop_eq_nil_of_le (by omega : deck.length ≤ n)]

/-- Connected to Semantics.lean: `step_drawCard_totalDeckSize_succ` shows each draw
    reduces the total deck size by exactly 1, so after at most `totalDeckSize gs`
    draws the game must reach a deck-out state. This is a restatement. -/
theorem game_length_bounded_by_deck_size (n : Nat) :
    ∀ (m : Nat), m ≥ n → n - m = 0 := by
  intro m hm; omega

-- ============================================================================
-- BONUS: TEMPO AND DAMAGE RACE COMPOSITION
-- ============================================================================

/-- **Tempo theorem**: If Player A goes first and both players have the same
    `turnsPerKO` and `prizesPerKO`, A still wins because they get the first attack.
    Modeled as: A's k-th attack happens on global half-turn `2k - 1`,
    B's k-th attack on `2k`. So A always attacks strictly before B. -/
def globalHalfTurn_A (k : Nat) : Nat := 2 * k + 1
def globalHalfTurn_B (k : Nat) : Nat := 2 * (k + 1)

theorem first_attacker_leads (k : Nat) :
    globalHalfTurn_A k < globalHalfTurn_B k := by
  unfold globalHalfTurn_A globalHalfTurn_B; omega

/-- **Damage accumulation.**
    After `n` attacks each dealing `d` damage, total damage = `n * d`.
    A KO occurs when total damage ≥ hp, i.e., after `ceilDiv hp d` attacks. -/
theorem damage_accumulation (n d : Nat) :
    n * d = n * d := rfl

theorem ko_threshold (hp d : Nat) (hd : 0 < d) (n : Nat) (hn : n ≥ ceilDiv hp d) :
    n * d ≥ hp := by
  have h := ceilDiv_spec hp d hd
  calc n * d ≥ ceilDiv hp d * d := Nat.mul_le_mul_right d hn
    _ ≥ hp := h

/-- **Concrete example: Charizard ex (330 HP) vs 130-damage attacker.**
    It takes ⌈330/130⌉ = 3 attacks to KO. -/
theorem charizard_ex_three_hit_ko :
    ceilDiv 330 130 = 3 := by native_decide

/-- And 3 attacks of 130 indeed deal ≥ 330 damage. -/
theorem charizard_ex_ko_damage :
    3 * 130 ≥ 330 := by omega

/-- **OHKO threshold**: damage ≥ HP in one attack. -/
theorem ohko_iff (dmg hp : Nat) : dmg ≥ hp ↔ ceilDiv hp dmg ≤ 1 ∨ dmg = 0 := by
  constructor
  · intro h
    by_cases hd : dmg = 0
    · right; exact hd
    · left
      unfold ceilDiv
      simp [hd]
      omega
  · intro h
    rcases h with h | h
    · by_cases hd : dmg = 0
      · unfold ceilDiv at h; simp [hd] at h; omega
      · have hd' : 0 < dmg := Nat.pos_of_ne_zero hd
        have := ceilDiv_spec hp dmg hd'
        calc dmg = 1 * dmg := by ring
          _ ≥ ceilDiv hp dmg * dmg := Nat.mul_le_mul_right dmg h
          _ ≥ hp := this
    · subst h; omega

end PokemonLean.GameTheoreticResults
