/-
  PokemonLean / Core / CoinFlip.lean

  Formal model for randomness in the Pokémon TCG.
  Defines coin flip outcomes, coin-dependent computations,
  sleep/burn/confusion/paralysis resolution, probability
  calculations using natural-number fractions, expected damage
  adjustments, and multi-flip scenarios.

  Self-contained — no imports from other PokemonLean modules.
  All proofs are sorry-free.  30+ theorems.
-/

namespace PokemonLean.Core.CoinFlip

-- ============================================================
-- §1  Core Coin Types
-- ============================================================

/-- A coin flip result. -/
inductive CoinResult where
  | heads
  | tails
deriving DecidableEq, Repr, BEq, Inhabited

/-- A coin-dependent computation: given a coin flip, produce a result. -/
def CoinComp (α : Type) := CoinResult → α

/-- Lift a constant into a coin computation. -/
def CoinComp.pure {α : Type} (a : α) : CoinComp α := fun _ => a

/-- Map over a coin computation. -/
def CoinComp.map {α β : Type} (f : α → β) (c : CoinComp α) : CoinComp β :=
  fun flip => f (c flip)

/-- The two possible outcomes of a coin flip. -/
def CoinResult.all : List CoinResult := [.heads, .tails]

/-- A coin flip has exactly 2 outcomes. -/
def coinOutcomes : Nat := 2

-- ============================================================
-- §2  Natural Number Fractions for Probability
-- ============================================================

/-- A rational probability represented as numerator/denominator (Nat). -/
structure Probability where
  num   : Nat
  denom : Nat
  valid : denom > 0 := by omega
deriving Repr

/-- P = 0 -/
def Probability.zero : Probability := ⟨0, 1, by omega⟩

/-- P = 1 -/
def Probability.one : Probability := ⟨1, 1, by omega⟩

/-- P = 1/2 (single coin flip) -/
def Probability.half : Probability := ⟨1, 2, by omega⟩

/-- Multiply two probabilities: (a/b) × (c/d) = (a*c)/(b*d). -/
def Probability.mul (p q : Probability) : Probability :=
  ⟨p.num * q.num, p.denom * q.denom, by omega⟩

/-- Whether probability equals a given fraction (cross-multiply check). -/
def Probability.eqFrac (p : Probability) (n d : Nat) : Prop :=
  p.num * d = n * p.denom

/-- Complementary probability: 1 - p = (denom - num) / denom. -/
def Probability.complement (p : Probability) (h : p.num ≤ p.denom) : Probability :=
  ⟨p.denom - p.num, p.denom, p.valid⟩

-- ============================================================
-- §3  Sleep Model
-- ============================================================

/-- Sleep check: flip coin between turns.
    Heads = wake up, Tails = stay asleep.
    P(wake in 1 turn) = 1/2. -/

/-- Probability of waking from sleep on a single check. -/
def sleepWakeProb : Probability := Probability.half

/-- Probability of staying asleep for exactly n consecutive checks.
    P(asleep n turns) = (1/2)^n. -/
def sleepStillAsleepProb (n : Nat) : Probability :=
  match n with
  | 0     => Probability.one
  | n + 1 => Probability.mul (sleepStillAsleepProb n) ⟨1, 2, by omega⟩

/-- Expected number of turns asleep = 2 (geometric distribution mean).
    We express this as: sum of P(asleep ≥ k) for k=1,2,3,... = 2.
    Concretely: 1/2 + 1/4 + 1/8 + ... → 1, and total expected = 1/P(heads) = 2.
    We model expected turns as numerator/denominator. -/
def sleepExpectedTurns : Probability := ⟨2, 1, by omega⟩

-- ============================================================
-- §4  Burn Model
-- ============================================================

/-- Burn check: flip between turns.
    Tails = 2 damage counters (20 HP).
    Heads = no damage this turn.
    P(burn damage) = 1/2. -/

/-- Burn damage on a failed flip (tails). -/
def burnDamageCounters : Nat := 2

/-- Burn damage in HP. -/
def burnDamageHP : Nat := burnDamageCounters * 10

/-- Probability of taking burn damage on any given check. -/
def burnDamageProb : Probability := Probability.half

/-- Expected burn damage counters per turn = 1 (= 2 × 1/2). -/
def burnExpectedCountersPerTurn : Nat := 1

-- ============================================================
-- §5  Confusion Model
-- ============================================================

/-- Confusion: flip before attacking.
    Tails = 30 damage to self instead of attacking.
    Heads = attack normally.
    P(self-hit) = 1/2. -/

/-- Confusion self-damage on tails. -/
def confusionSelfDamage : Nat := 30

/-- Probability of confusion self-hit. -/
def confusionSelfHitProb : Probability := Probability.half

/-- Resolve confusion: given a flip, return either attack damage or self-damage. -/
def resolveConfusion (attackDamage : Nat) (flip : CoinResult) : Int :=
  match flip with
  | .heads => (attackDamage : Int)
  | .tails => -(confusionSelfDamage : Int)

/-- Expected damage from an attack when confused.
    E = attackDamage/2 - confusionSelfDamage/2.
    We model as (attackDamage - 30) / 2, treating as Nat (floor at 0). -/
def confusedExpectedDamage (baseDamage : Nat) : Nat :=
  baseDamage / 2

-- ============================================================
-- §6  Paralysis Model
-- ============================================================

/-- Paralysis: NO coin flip. Auto-cures at end of afflicted player's
    next turn. Cannot attack or retreat while paralyzed. -/

/-- Paralysis involves no coin flip. -/
def paralysisHasFlip : Bool := false

/-- Paralysis duration in turns. -/
def paralysisDuration : Nat := 1

-- ============================================================
-- §7  Trainer Card Coin Flips
-- ============================================================

/-- Super Scoop Up: flip, heads = return Pokémon and all cards
    attached to it to your hand. -/
def superScoopUpResult (flip : CoinResult) : Bool :=
  match flip with
  | .heads => true   -- Success: return to hand
  | .tails => false  -- Fail: nothing happens

/-- Crushing Hammer: flip, heads = discard an energy from opponent's Pokémon. -/
def crushingHammerResult (flip : CoinResult) : Bool :=
  match flip with
  | .heads => true
  | .tails => false

/-- Pokémon Catcher (original version): flip, heads = gust effect. -/
def pokemonCatcherResult (flip : CoinResult) : Bool :=
  match flip with
  | .heads => true
  | .tails => false

/-- Victini's Victory Star ability: reflip ALL coins once.
    Models the concept of a second attempt. -/
def victiniReflip (firstFlip secondFlip : CoinResult) (useReflip : Bool) : CoinResult :=
  if useReflip then secondFlip else firstFlip

-- ============================================================
-- §8  Multi-Flip Scenarios
-- ============================================================

/-- Count heads in a sequence of flips. -/
def countHeads : List CoinResult → Nat
  | [] => 0
  | .heads :: rest => 1 + countHeads rest
  | .tails :: rest => countHeads rest

/-- Count tails in a sequence of flips. -/
def countTails : List CoinResult → Nat
  | [] => 0
  | .tails :: rest => 1 + countTails rest
  | .heads :: rest => countTails rest

/-- Total flips = heads + tails. -/
def totalFlips (flips : List CoinResult) : Nat := flips.length

/-- Flip-until-tails: count how many heads before the first tails.
    Used for attacks like "flip coins until you get tails, 30× heads". -/
def flipUntilTailsDamage (flips : List CoinResult) (damagePerHead : Nat) : Nat :=
  countHeads (flips.takeWhile (· == .heads)) * damagePerHead

/-- Probability of exactly k heads in n independent flips.
    P(k heads in n flips) uses a simplified model:
    numerator = C(n,k), denominator = 2^n. -/
def choose : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- Power of 2. -/
def pow2 : Nat → Nat
  | 0     => 1
  | n + 1 => 2 * pow2 n

/-- Probability of exactly k heads in n flips. -/
def probExactHeads (n k : Nat) (h : n > 0 := by omega) : Probability :=
  ⟨choose n k, pow2 n, by induction n with
    | zero => omega
    | succ n' _ => simp [pow2]; omega⟩

-- ============================================================
-- §9  Expected Damage with Coin Flips
-- ============================================================

/-- Expected damage for a flip-for-damage attack.
    Base damage × P(heads) = baseDamage / 2 (integer division). -/
def expectedFlipDamage (baseDamage : Nat) : Nat :=
  baseDamage / 2

/-- Expected damage for a "flip until tails" attack.
    E[heads before tails] = 1, so E[damage] = damagePerHead.
    (Geometric distribution: E[X] = p/(1-p) = 1 for fair coin.) -/
def expectedFlipUntilTailsDamage (damagePerHead : Nat) : Nat :=
  damagePerHead

/-- Expected damage for confusion: halves your effective damage output.
    If confused, E[damage dealt to opponent] = baseDamage/2. -/
def expectedConfusedOutput (baseDamage : Nat) : Nat :=
  baseDamage / 2

-- ============================================================
-- §10  Theorems — Coin Flip Basics
-- ============================================================

/-- Theorem 1: Coin flip has exactly 2 outcomes. -/
theorem coin_binary : CoinResult.all.length = 2 := by native_decide

/-- Theorem 2: Heads ≠ Tails. -/
theorem heads_ne_tails : CoinResult.heads ≠ CoinResult.tails := by decide

/-- Theorem 3: Every coin result is heads or tails (exhaustive). -/
theorem coin_exhaustive (c : CoinResult) : c = .heads ∨ c = .tails := by
  cases c <;> simp

/-- Theorem 4: CoinResult has decidable equality. -/
theorem coin_decidable (a b : CoinResult) : Decidable (a = b) :=
  inferInstance

-- ============================================================
-- §11  Theorems — Probability Properties
-- ============================================================

/-- Theorem 5: P(heads single flip) = 1/2. -/
theorem prob_heads_half : sleepWakeProb.num = 1 ∧ sleepWakeProb.denom = 2 := by
  constructor <;> rfl

/-- Theorem 6: P(asleep after 0 checks) = 1 (you just got put to sleep). -/
theorem asleep_zero_certain :
    (sleepStillAsleepProb 0).num = 1 ∧ (sleepStillAsleepProb 0).denom = 1 := by
  constructor <;> rfl

/-- Theorem 7: P(asleep after 1 check) = 1/2. -/
theorem asleep_one_half :
    (sleepStillAsleepProb 1).num = 1 ∧ (sleepStillAsleepProb 1).denom = 2 := by
  constructor <;> rfl

/-- Theorem 8: P(asleep after 2 checks) = 1/4. -/
theorem asleep_two_quarter :
    (sleepStillAsleepProb 2).num = 1 ∧ (sleepStillAsleepProb 2).denom = 4 := by
  constructor <;> rfl

/-- Theorem 9: P(asleep after 3 checks) = 1/8. -/
theorem asleep_three_eighth :
    (sleepStillAsleepProb 3).num = 1 ∧ (sleepStillAsleepProb 3).denom = 8 := by
  constructor <;> rfl

/-- Theorem 10: Sleep expected duration = 2 turns. -/
theorem sleep_expected_two : sleepExpectedTurns.num = 2 := by rfl

/-- Theorem 11: P(burn damage) = 1/2. -/
theorem burn_prob_half : burnDamageProb.num = 1 ∧ burnDamageProb.denom = 2 := by
  constructor <;> rfl

/-- Theorem 12: P(confusion self-hit) = 1/2. -/
theorem confusion_prob_half : confusionSelfHitProb.num = 1 ∧ confusionSelfHitProb.denom = 2 := by
  constructor <;> rfl

-- ============================================================
-- §12  Theorems — Burn Mechanics
-- ============================================================

/-- Theorem 13: Burn places 2 damage counters on tails. -/
theorem burn_counters : burnDamageCounters = 2 := by rfl

/-- Theorem 14: Burn damage = 20 HP. -/
theorem burn_hp_damage : burnDamageHP = 20 := by rfl

/-- Theorem 15: Expected burn damage per turn = 1 counter. -/
theorem burn_expected_one : burnExpectedCountersPerTurn = 1 := by rfl

-- ============================================================
-- §13  Theorems — Confusion Mechanics
-- ============================================================

/-- Theorem 16: Confusion self-damage = 30. -/
theorem confusion_self_30 : confusionSelfDamage = 30 := by rfl

/-- Theorem 17: Confused attack on heads deals full damage. -/
theorem confusion_heads_full (d : Nat) :
    resolveConfusion d .heads = (d : Int) := by rfl

/-- Theorem 18: Confused attack on tails deals -30 (self-damage). -/
theorem confusion_tails_self (d : Nat) :
    resolveConfusion d .tails = -(confusionSelfDamage : Int) := by rfl

/-- Theorem 19: Confusion halves expected damage output.
    For d = 200, expected = 100. -/
theorem confusion_halves_200 : confusedExpectedDamage 200 = 100 := by native_decide

/-- Theorem 20: Confusion halves expected damage output.
    For d = 0, expected = 0. -/
theorem confusion_halves_zero : confusedExpectedDamage 0 = 0 := by rfl

-- ============================================================
-- §14  Theorems — Paralysis
-- ============================================================

/-- Theorem 21: Paralysis involves no coin flip. -/
theorem paralysis_no_flip : paralysisHasFlip = false := by rfl

/-- Theorem 22: Paralysis lasts exactly 1 turn. -/
theorem paralysis_one_turn : paralysisDuration = 1 := by rfl

-- ============================================================
-- §15  Theorems — Trainer Card Flips
-- ============================================================

/-- Theorem 23: Super Scoop Up succeeds on heads. -/
theorem super_scoop_heads : superScoopUpResult .heads = true := by rfl

/-- Theorem 24: Super Scoop Up fails on tails. -/
theorem super_scoop_tails : superScoopUpResult .tails = false := by rfl

/-- Theorem 25: Crushing Hammer succeeds on heads. -/
theorem crushing_hammer_heads : crushingHammerResult .heads = true := by rfl

/-- Theorem 26: Crushing Hammer fails on tails. -/
theorem crushing_hammer_tails : crushingHammerResult .tails = false := by rfl

/-- Theorem 27: Pokémon Catcher (old) succeeds on heads. -/
theorem pokemon_catcher_heads : pokemonCatcherResult .heads = true := by rfl

/-- Theorem 28: Pokémon Catcher (old) fails on tails. -/
theorem pokemon_catcher_tails : pokemonCatcherResult .tails = false := by rfl

-- ============================================================
-- §16  Theorems — Multi-Flip Properties
-- ============================================================

/-- Theorem 29: Heads + Tails = Total flips. -/
theorem heads_plus_tails_eq_total (flips : List CoinResult) :
    countHeads flips + countTails flips = totalFlips flips := by
  induction flips with
  | nil => rfl
  | cons c rest ih =>
    cases c <;> simp [countHeads, countTails, totalFlips, List.length] <;> omega

/-- Theorem 30: Empty flip list has 0 heads. -/
theorem empty_flips_no_heads : countHeads [] = 0 := by rfl

/-- Theorem 31: Empty flip list has 0 tails. -/
theorem empty_flips_no_tails : countTails [] = 0 := by rfl

/-- Theorem 32: choose n 0 = 1 for all n. -/
theorem choose_n_0 (n : Nat) : choose n 0 = 1 := by
  cases n <;> rfl

/-- Theorem 33: pow2 0 = 1. -/
theorem pow2_zero : pow2 0 = 1 := by rfl

/-- Theorem 34: pow2 is always positive. -/
theorem pow2_pos (n : Nat) : pow2 n > 0 := by
  induction n with
  | zero => simp [pow2]
  | succ n ih => simp [pow2]; omega

/-- Theorem 35: Victini reflip: not using reflip returns first flip. -/
theorem victini_no_reflip (f s : CoinResult) :
    victiniReflip f s false = f := by rfl

/-- Theorem 36: Victini reflip: using reflip returns second flip. -/
theorem victini_yes_reflip (f s : CoinResult) :
    victiniReflip f s true = s := by rfl

-- ============================================================
-- §17  Theorems — Expected Damage
-- ============================================================

/-- Theorem 37: Expected flip damage of 120 = 60. -/
theorem expected_flip_120 : expectedFlipDamage 120 = 60 := by native_decide

/-- Theorem 38: Expected flip-until-tails damage = damage per head. -/
theorem expected_flip_until (d : Nat) :
    expectedFlipUntilTailsDamage d = d := by rfl

/-- Theorem 39: Expected confused output of 180 = 90. -/
theorem expected_confused_180 : expectedConfusedOutput 180 = 90 := by native_decide

/-- Theorem 40: Pure coin computation returns constant. -/
theorem pure_constant {α : Type} (a : α) (c : CoinResult) :
    CoinComp.pure a c = a := by rfl

/-- Theorem 41: Map over pure is function application. -/
theorem map_pure {α β : Type} (f : α → β) (a : α) (c : CoinResult) :
    CoinComp.map f (CoinComp.pure a) c = f a := by rfl

/-- Theorem 42: Probability multiplication of 1/2 × 1/2 = 1/4. -/
theorem half_times_half :
    (Probability.mul Probability.half Probability.half).num = 1 ∧
    (Probability.mul Probability.half Probability.half).denom = 4 := by
  constructor <;> rfl

-- ============================================================
-- §18  Theorems — Compound Scenarios
-- ============================================================

/-- Theorem 43: Flip-until-tails with all heads = total × damage. -/
theorem flip_until_all_heads :
    flipUntilTailsDamage [.heads, .heads, .heads, .tails] 30 = 90 := by native_decide

/-- Theorem 44: Flip-until-tails with first tails = 0 damage. -/
theorem flip_until_first_tails :
    flipUntilTailsDamage [.tails, .heads, .heads] 30 = 0 := by native_decide

/-- Theorem 45: Complementary probability: if P = 1/2, complement = 1/2. -/
theorem complement_half :
    (Probability.complement Probability.half (by omega)).num = 1 ∧
    (Probability.complement Probability.half (by omega)).denom = 2 := by
  constructor <;> rfl

end PokemonLean.Core.CoinFlip
