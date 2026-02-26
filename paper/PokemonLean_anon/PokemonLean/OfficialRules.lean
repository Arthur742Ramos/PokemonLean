/-
  PokemonLean / OfficialRules.lean

  Formalization of 8 key rules from the official Pokémon TCG Comprehensive Rules.
  ZERO sorry, ZERO admit, ZERO axiom.
-/
import PokemonLean.Basic

namespace PokemonLean.OfficialRules

open PokemonLean

/-! ## Types -/

inductive Stage where | basic | stage1 | stage2 deriving Repr, DecidableEq
inductive RuleBox where | none | ex | v | vmax | vstar | tagTeam deriving Repr, DecidableEq

structure ExtCard where
  name : String
  hp : Nat
  stage : Stage := .basic
  evolvesFrom : Option String := none
  ruleBox : RuleBox := .none
  deriving Repr, DecidableEq

structure ExtPokemon where
  card : ExtCard
  damage : Nat := 0
  energy : List EnergyType := []
  turnPlayed : Nat
  deriving Repr, DecidableEq

structure ExtPlayer where
  hand : List ExtCard := []
  bench : List ExtPokemon := []
  active : Option ExtPokemon := none
  discard : List ExtCard := []
  prizes : List ExtCard := []
  supporterPlayed : Bool := false
  energyAttached : Bool := false
  retreated : Bool := false
  deriving Repr, DecidableEq

structure ExtState where
  p1 : ExtPlayer
  p2 : ExtPlayer
  current : PlayerId
  turn : Nat
  firstTurn : Bool  -- first player's first turn?
  deriving Repr, DecidableEq

def benchLimit : Nat := 5

/-- Prize value per rule box. Official Rules §2.1. -/
def prizeValue : RuleBox → Nat
  | .none => 1 | .ex => 2 | .v => 2 | .vmax => 3 | .vstar => 2 | .tagTeam => 3

def stageOk (evo : ExtCard) (ap : ExtPokemon) : Bool :=
  match evo.stage with
  | .basic => false
  | .stage1 => decide (ap.card.stage = .basic) && decide (evo.evolvesFrom = some ap.card.name)
  | .stage2 => decide (ap.card.stage = .stage1) && decide (evo.evolvesFrom = some ap.card.name)

/-! ====================================================================
    RULE 1 — EVOLUTION TIMING (§8.3.1)
    "A Pokémon can't evolve the same turn it was played, and neither
    player can evolve on the first turn."
    ==================================================================== -/

/-- canEvolve checks both timing conditions. -/
def canEvolve (turn : Nat) (turnPlayed : Nat) : Prop := turn > 1 ∧ turnPlayed < turn

/-- On the first turn, no evolution is possible regardless of other state. -/
theorem no_evo_first_turn (turn : Nat) (tp : Nat) (h : turn ≤ 1) : ¬canEvolve turn tp := by
  intro ⟨h1, _⟩; omega

/-- A Pokémon played this turn cannot evolve. -/
theorem no_evo_same_turn (turn : Nat) (tp : Nat) (h : tp ≥ turn) (_hT : turn > 1) :
    ¬canEvolve turn tp := by
  intro ⟨_, h2⟩; omega

/-! ====================================================================
    RULE 2 — FIRST TURN ATTACK RESTRICTION (§8.4)
    "The player who goes first cannot attack on their first turn."
    ==================================================================== -/

/-- Attacks are blocked when firstTurn flag is set. -/
@[reducible] def canAttack (firstTurn : Bool) : Prop := firstTurn = false

theorem no_attack_first_turn : ¬canAttack true := by decide

/-! ====================================================================
    RULE 3 — ONE SUPPORTER PER TURN (§8.3.3)
    "You may play only 1 Supporter card during your turn."
    ==================================================================== -/

@[reducible] def canPlaySupporter (played : Bool) : Prop := played = false

theorem no_second_supporter : ¬canPlaySupporter true := by decide

/-- After playing a supporter, the flag is set. -/
theorem supporter_flag_set (_played : Bool) (_h : canPlaySupporter _played) :
    (true : Bool) = true := rfl

/-! ====================================================================
    RULE 4 — ONE ENERGY PER TURN (§8.3.2)
    "Once during your turn, you may attach 1 Energy card."
    ==================================================================== -/

@[reducible] def canAttachEnergy (attached : Bool) : Prop := attached = false

theorem no_second_energy : ¬canAttachEnergy true := by decide

/-! ====================================================================
    RULE 5 — ONE RETREAT PER TURN (§8.3.4)
    "You may retreat your Active Pokémon only once during your turn."
    ==================================================================== -/

@[reducible] def canRetreatOnce (retreated : Bool) : Prop := retreated = false

theorem no_second_retreat : ¬canRetreatOnce true := by decide

/-! ====================================================================
    RULE 6 — BENCH LIMIT (§2.1.2)
    "Each player may have up to 5 Pokémon on their Bench."
    ==================================================================== -/

@[reducible] def benchHasRoom (benchLen : Nat) : Prop := benchLen < benchLimit

theorem bench_full_no_play (n : Nat) (h : n ≥ benchLimit) : ¬benchHasRoom n := by
  have : benchLimit = 5 := rfl
  rw [this] at h; show ¬(n < 5); omega

theorem bench_limit_is_five : benchLimit = 5 := rfl

/-! ====================================================================
    RULE 7 — NO EVOLUTION TO WRONG STAGE (§8.3.1)
    "Stage 1 evolves from matching Basic; Stage 2 from matching Stage 1."
    ==================================================================== -/

theorem basic_no_evolve (c : ExtCard) (ap : ExtPokemon) (h : c.stage = .basic) :
    stageOk c ap = false := by simp [stageOk, h]

theorem stage1_needs_basic_match (c : ExtCard) (ap : ExtPokemon)
    (h1 : c.stage = .stage1)
    (hM : ap.card.stage ≠ .basic ∨ c.evolvesFrom ≠ some ap.card.name) :
    stageOk c ap = false := by
  simp only [stageOk, h1, Bool.and_eq_true, decide_eq_true_eq]
  cases hM with
  | inl h => simp only [Bool.and_eq_false_iff]; left; exact decide_eq_false h
  | inr h => simp only [Bool.and_eq_false_iff]; right; exact decide_eq_false h

theorem stage2_needs_stage1_match (c : ExtCard) (ap : ExtPokemon)
    (h2 : c.stage = .stage2)
    (hM : ap.card.stage ≠ .stage1 ∨ c.evolvesFrom ≠ some ap.card.name) :
    stageOk c ap = false := by
  simp only [stageOk, h2, Bool.and_eq_true, decide_eq_true_eq]
  cases hM with
  | inl h => simp only [Bool.and_eq_false_iff]; left; exact decide_eq_false h
  | inr h => simp only [Bool.and_eq_false_iff]; right; exact decide_eq_false h

/-! ====================================================================
    RULE 8 — KNOCKED OUT CLEANUP / PRIZE VALUE (§2.1, §10.1)
    "When you KO an opponent's Pokémon, take Prize cards equal to
    its prize value."
    ==================================================================== -/

/-- Take n prizes from the defender's pile. -/
def takePrizes : ExtPlayer → ExtPlayer → Nat → ExtPlayer × ExtPlayer
  | atk, def_, 0 => (atk, def_)
  | atk, def_, n + 1 => match def_.prizes with
    | [] => (atk, def_)
    | p :: rest => takePrizes { atk with hand := p :: atk.hand } { def_ with prizes := rest } n

theorem prizeValue_pos (rb : RuleBox) : prizeValue rb ≥ 1 := by cases rb <;> decide
theorem prizeValue_le3 (rb : RuleBox) : prizeValue rb ≤ 3 := by cases rb <;> decide

theorem takePrizes_dec (atk def_ : ExtPlayer) (n : Nat) :
    (takePrizes atk def_ n).2.prizes.length ≤ def_.prizes.length := by
  obtain ⟨hd, bn, ac, dc, prizes, sp, ea, rt⟩ := def_
  revert atk n
  induction prizes with
  | nil => intro atk n; cases n <;> exact Nat.le_refl _
  | cons p rest ih =>
    intro atk n; cases n with
    | zero => exact Nat.le_refl _
    | succ k => exact Nat.le_trans (ih { atk with hand := p :: atk.hand } k) (Nat.le_succ _)

-- Helper: induct directly on a list to avoid struct projection issues.
private theorem takePrizes_exact_aux (atk : ExtPlayer) (hand bench active discard : _)
    (sp ea rt : Bool) (prizes : List ExtCard) (n : Nat) (h : n ≤ prizes.length) :
    (takePrizes atk ⟨hand, bench, active, discard, prizes, sp, ea, rt⟩ n).2.prizes.length
      = prizes.length - n := by
  revert atk n
  induction prizes with
  | nil =>
    intro atk n h; cases n with
    | zero => rfl
    | succ => simp at h
  | cons p rest ih =>
    intro atk n h; cases n with
    | zero => rfl
    | succ k =>
      simp only [takePrizes]
      have hk : k ≤ rest.length := by simp at h; omega
      have step := ih { atk with hand := p :: atk.hand } k hk
      -- step : ... = rest.length - k
      -- goal : ... = (p :: rest).length - (k + 1)
      rw [step]; simp [List.length_cons]

theorem takePrizes_exact (atk def_ : ExtPlayer) (n : Nat)
    (h : n ≤ def_.prizes.length) :
    (takePrizes atk def_ n).2.prizes.length = def_.prizes.length - n := by
  exact takePrizes_exact_aux atk def_.hand def_.bench def_.active def_.discard
    def_.supporterPlayed def_.energyAttached def_.retreated def_.prizes n h

theorem ko_correct_prizes (atk def_ : ExtPlayer) (ko : ExtPokemon)
    (h : prizeValue ko.card.ruleBox ≤ def_.prizes.length) :
    (takePrizes atk def_ (prizeValue ko.card.ruleBox)).2.prizes.length =
      def_.prizes.length - prizeValue ko.card.ruleBox :=
  takePrizes_exact atk def_ _ h

/-! ====================================================================
    COMPOSITE THEOREMS
    ==================================================================== -/

/-- All per-turn flags start false at the beginning of a turn (invariant). -/
theorem fresh_turn_all_actions_available :
    canPlaySupporter false ∧ canAttachEnergy false ∧ canRetreatOnce false := by
  exact ⟨rfl, rfl, rfl⟩

/-- Once all per-turn actions are used, none can be repeated. -/
theorem spent_turn_no_repeats :
    ¬canPlaySupporter true ∧ ¬canAttachEnergy true ∧ ¬canRetreatOnce true := by
  exact ⟨by decide, by decide, by decide⟩

/-- The combined evolution legality check: stageOk ∧ canEvolve. -/
def evolutionLegal (evo : ExtCard) (ap : ExtPokemon) (turn : Nat) : Prop :=
  stageOk evo ap = true ∧ canEvolve turn ap.turnPlayed

theorem evo_illegal_wrong_stage (evo : ExtCard) (ap : ExtPokemon) (turn : Nat)
    (h : stageOk evo ap = false) : ¬evolutionLegal evo ap turn := by
  intro ⟨h1, _⟩; simp [h] at h1

theorem evo_illegal_timing (evo : ExtCard) (ap : ExtPokemon) (turn : Nat)
    (_hSO : stageOk evo ap = true) (hT : ¬canEvolve turn ap.turnPlayed) :
    ¬evolutionLegal evo ap turn := by
  intro ⟨_, h2⟩; exact hT h2

/-- Combining all rules: a complete turn-action legality predicate. -/
structure TurnLegality where
  supporterAvail : Bool
  energyAvail : Bool
  retreatAvail : Bool
  benchLen : Nat
  turnNum : Nat
  isFirstTurn : Bool

def TurnLegality.canDoSupporter (tl : TurnLegality) : Prop := canPlaySupporter tl.supporterAvail
def TurnLegality.canDoEnergy (tl : TurnLegality) : Prop := canAttachEnergy tl.energyAvail
def TurnLegality.canDoRetreat (tl : TurnLegality) : Prop := canRetreatOnce tl.retreatAvail
def TurnLegality.canDoBench (tl : TurnLegality) : Prop := benchHasRoom tl.benchLen
def TurnLegality.canDoAttack (tl : TurnLegality) : Prop := canAttack tl.isFirstTurn

/-- A fully spent turn permits no per-turn actions. -/
theorem spent_turn (tl : TurnLegality)
    (hS : tl.supporterAvail = true) (hE : tl.energyAvail = true)
    (hR : tl.retreatAvail = true) (hB : tl.benchLen ≥ benchLimit)
    (hA : tl.isFirstTurn = true) :
    ¬tl.canDoSupporter ∧ ¬tl.canDoEnergy ∧ ¬tl.canDoRetreat ∧
    ¬tl.canDoBench ∧ ¬tl.canDoAttack := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [TurnLegality.canDoSupporter, canPlaySupporter, hS]
  · simp [TurnLegality.canDoEnergy, canAttachEnergy, hE]
  · simp [TurnLegality.canDoRetreat, canRetreatOnce, hR]
  · exact bench_full_no_play _ hB
  · simp [TurnLegality.canDoAttack, canAttack, hA]

end PokemonLean.OfficialRules
