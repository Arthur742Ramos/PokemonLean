/-
  PokemonLean / Core / CharizardDeck.lean

  Charizard ex archetype formalization (SV-era 2024 dominant shell).
  Self-contained, sorry-free, with 35+ theorems.
-/

set_option linter.unusedVariables false

namespace PokemonLean.Core.CharizardDeck

-- ============================================================
-- §1  Core evolution line and card data
-- ============================================================

inductive Stage where
  | basic
  | stage1
  | stage2
  deriving DecidableEq, Repr

structure PokemonCard where
  name : String
  hp : Nat
  stage : Stage
  deriving DecidableEq, Repr

def charmander : PokemonCard := ⟨"Charmander", 70, .basic⟩
def charmeleon : PokemonCard := ⟨"Charmeleon", 90, .stage1⟩
def charizardEx : PokemonCard := ⟨"Charizard ex", 330, .stage2⟩
def pidgeotEx : PokemonCard := ⟨"Pidgeot ex", 280, .stage2⟩
def arcanineEx : PokemonCard := ⟨"Arcanine ex", 280, .stage1⟩

/-- [T1] Charmander HP is 70. -/
theorem charmander_hp_value : charmander.hp = 70 := rfl

/-- [T2] Charmeleon HP is 90. -/
theorem charmeleon_hp_value : charmeleon.hp = 90 := rfl

/-- [T3] Charizard ex HP is 330. -/
theorem charizard_hp_value : charizardEx.hp = 330 := rfl

/-- [T4] Charmander is Basic. -/
theorem charmander_is_basic : charmander.stage = .basic := rfl

/-- [T5] Charmeleon is Stage 1. -/
theorem charmeleon_is_stage1 : charmeleon.stage = .stage1 := rfl

/-- [T6] Charizard ex is Stage 2. -/
theorem charizard_is_stage2 : charizardEx.stage = .stage2 := rfl

/-- [T7] HP increases from Charmander to Charmeleon. -/
theorem hp_growth_basic_to_stage1 : charmander.hp < charmeleon.hp := by
  native_decide

/-- [T8] HP increases from Charmeleon to Charizard ex. -/
theorem hp_growth_stage1_to_stage2 : charmeleon.hp < charizardEx.hp := by
  native_decide

/-- [T9] Full line grows from Charmander to Charizard ex. -/
theorem hp_growth_full_line : charmander.hp < charizardEx.hp := by
  native_decide

-- ============================================================
-- §2  Burning Darkness damage scaling
-- ============================================================

/-- Burning Darkness base damage. -/
def burningBase : Nat := 180

/-- Burning Darkness bonus per prize already taken. -/
def burningPerPrize : Nat := 30

/-- Charizard ex can only attack before taking all 6 prizes, so legal cap is 5. -/
def legalPrizeCap : Nat := 5

/-- Burning Darkness damage formula. -/
def burningDarkness (prizesTaken : Nat) : Nat :=
  burningBase + burningPerPrize * prizesTaken

/-- Legal prize counts while the game is still ongoing. -/
def legalPrizesTaken (n : Nat) : Prop := n ≤ legalPrizeCap

/-- [T10] Base constant is 180. -/
theorem burning_base_value : burningBase = 180 := rfl

/-- [T11] Per-prize constant is 30. -/
theorem burning_per_prize_value : burningPerPrize = 30 := rfl

/-- [T12] Damage at 0 prizes is 180. -/
theorem burning_at_0 : burningDarkness 0 = 180 := by
  native_decide

/-- [T13] Damage at 1 prize is 210. -/
theorem burning_at_1 : burningDarkness 1 = 210 := by
  native_decide

/-- [T14] Damage at 2 prizes is 240. -/
theorem burning_at_2 : burningDarkness 2 = 240 := by
  native_decide

/-- [T15] Damage at 3 prizes is 270. -/
theorem burning_at_3 : burningDarkness 3 = 270 := by
  native_decide

/-- [T16] Damage at 4 prizes is 300. -/
theorem burning_at_4 : burningDarkness 4 = 300 := by
  native_decide

/-- [T17] Damage at 5 prizes is 330. -/
theorem burning_at_5 : burningDarkness 5 = 330 := by
  native_decide

/-- [T18] Formula is exactly 180 + 30 × prizes. -/
theorem burning_formula_exact (p : Nat) :
    burningDarkness p = 180 + 30 * p := rfl

/-- [T19] Each additional prize adds exactly 30 damage. -/
theorem burning_step_adds_30 (p : Nat) :
    burningDarkness (p + 1) = burningDarkness p + 30 := by
  unfold burningDarkness burningBase burningPerPrize
  omega

/-- [T20] Burning Darkness is monotone in prizes taken. -/
theorem burning_monotone (p q : Nat) (h : p ≤ q) :
    burningDarkness p ≤ burningDarkness q := by
  unfold burningDarkness burningBase burningPerPrize
  omega

/-- [T21] Burning Darkness is strictly increasing with prizes. -/
theorem burning_strict_mono (p q : Nat) (h : p < q) :
    burningDarkness p < burningDarkness q := by
  unfold burningDarkness
  have hPos : 0 < burningPerPrize := by
    native_decide
  have hMul : burningPerPrize * p < burningPerPrize * q := by
    exact Nat.mul_lt_mul_of_pos_left h hPos
  exact Nat.add_lt_add_left hMul burningBase

/-- [T22] Legal damage is bounded above by 330. -/
theorem burning_legal_max_bound (p : Nat) (h : legalPrizesTaken p) :
    burningDarkness p ≤ 330 := by
  unfold legalPrizesTaken legalPrizeCap at h
  unfold burningDarkness burningBase burningPerPrize
  omega

/-- [T23] 5 prizes is legal. -/
theorem five_prizes_legal : legalPrizesTaken 5 := by
  unfold legalPrizesTaken legalPrizeCap
  omega

/-- [T24] 6 prizes is not legal for attack-state modeling. -/
theorem six_prizes_not_legal : ¬ legalPrizesTaken 6 := by
  unfold legalPrizesTaken legalPrizeCap
  omega

/-- [T25] Max legal damage equals 330. -/
theorem max_legal_damage_is_330 :
    legalPrizesTaken 5 ∧ burningDarkness 5 = 330 := by
  constructor
  · exact five_prizes_legal
  · exact burning_at_5

/-- [T26] Prize-based scaling means damage grows as game progresses. -/
theorem stronger_late_game (early late : Nat) (h : early < late) :
    burningDarkness early < burningDarkness late := by
  exact burning_strict_mono early late h

-- ============================================================
-- §3  Rare Candy tempo advantage
-- ============================================================

/-- Normal path needs Basic -> Stage1 -> Stage2: two evolution turns. -/
def turnsToStage2Normal : Nat := 2

/-- Rare Candy path skips Stage1: one evolution turn. -/
def turnsToStage2WithCandy : Nat := 1

/-- Turn savings from Rare Candy. -/
def rareCandyTurnSavings : Nat :=
  turnsToStage2Normal - turnsToStage2WithCandy

/-- Stage-2 ready turn from a given starting turn. -/
def stage2ReadyTurnNormal (startTurn : Nat) : Nat := startTurn + turnsToStage2Normal

def stage2ReadyTurnCandy (startTurn : Nat) : Nat := startTurn + turnsToStage2WithCandy

/-- [T27] Normal evolution takes 2 turns. -/
theorem normal_evolution_turns_value : turnsToStage2Normal = 2 := rfl

/-- [T28] Rare Candy evolution takes 1 turn. -/
theorem candy_evolution_turns_value : turnsToStage2WithCandy = 1 := rfl

/-- [T29] Rare Candy saves exactly 1 turn. -/
theorem rare_candy_saves_one_turn : rareCandyTurnSavings = 1 := by
  native_decide

/-- [T30] Candy-ready is one turn earlier than normal-ready. -/
theorem candy_ready_one_turn_earlier (startTurn : Nat) :
    stage2ReadyTurnCandy startTurn + 1 = stage2ReadyTurnNormal startTurn := by
  unfold stage2ReadyTurnCandy stage2ReadyTurnNormal turnsToStage2WithCandy turnsToStage2Normal
  omega

/-- [T31] Rare Candy path is never slower than normal path. -/
theorem candy_not_slower (startTurn : Nat) :
    stage2ReadyTurnCandy startTurn ≤ stage2ReadyTurnNormal startTurn := by
  unfold stage2ReadyTurnCandy stage2ReadyTurnNormal turnsToStage2WithCandy turnsToStage2Normal
  omega

/-- [T32] Rare Candy gives strict tempo gain from any start turn. -/
theorem candy_strict_tempo_gain (startTurn : Nat) :
    stage2ReadyTurnCandy startTurn < stage2ReadyTurnNormal startTurn := by
  unfold stage2ReadyTurnCandy stage2ReadyTurnNormal turnsToStage2WithCandy turnsToStage2Normal
  omega

-- ============================================================
-- §4  Pidgeot ex Quick Search consistency
-- ============================================================

structure SearchState where
  deck : List String
  hand : List String
  quickSearchUsed : Bool
  deriving DecidableEq, Repr

/-- Quick Search: once per turn, search any card from deck into hand. -/
def quickSearch (s : SearchState) (target : String) : SearchState :=
  if hUsed : s.quickSearchUsed then
    s
  else if hDeck : target ∈ s.deck then
    { deck := s.deck.erase target
      hand := target :: s.hand
      quickSearchUsed := true }
  else
    { s with quickSearchUsed := true }

/-- "Have answer" abstraction. -/
def hasAnswer (s : SearchState) (answer : String) : Prop := answer ∈ s.hand

/-- [T33] Using Quick Search marks the ability as used. -/
theorem quick_search_marks_used (s : SearchState) (target : String) :
    (quickSearch s target).quickSearchUsed = true := by
  unfold quickSearch
  by_cases hUsed : s.quickSearchUsed
  · simp [hUsed]
  · by_cases hDeck : target ∈ s.deck
    · simp [hUsed, hDeck]
    · simp [hUsed, hDeck]

/-- [T34] If already used this turn, Quick Search does nothing. -/
theorem quick_search_once_per_turn (s : SearchState) (target : String)
    (hUsed : s.quickSearchUsed = true) :
    quickSearch s target = s := by
  unfold quickSearch
  simp [hUsed]

/-- [T35] If target is in deck and Quick Search is unused, target enters hand. -/
theorem quick_search_finds_target (s : SearchState) (target : String)
    (hUsed : s.quickSearchUsed = false) (hDeck : target ∈ s.deck) :
    target ∈ (quickSearch s target).hand := by
  unfold quickSearch
  simp [hUsed, hDeck]

/-- [T36] If target is in deck and Quick Search is unused, one copy leaves deck. -/
theorem quick_search_removes_one_copy (s : SearchState) (target : String)
    (hUsed : s.quickSearchUsed = false) (hDeck : target ∈ s.deck) :
    (quickSearch s target).deck.length = s.deck.length - 1 := by
  unfold quickSearch
  simp [hUsed, hDeck, List.length_erase_of_mem]

/-- [T37] Missing target still consumes the once-per-turn usage. -/
theorem quick_search_miss_still_used (s : SearchState) (target : String)
    (hUsed : s.quickSearchUsed = false) (hDeck : target ∉ s.deck) :
    (quickSearch s target).quickSearchUsed = true := by
  unfold quickSearch
  simp [hUsed, hDeck]

/-- [T38] Missing target leaves hand unchanged. -/
theorem quick_search_miss_keeps_hand (s : SearchState) (target : String)
    (hUsed : s.quickSearchUsed = false) (hDeck : target ∉ s.deck) :
    (quickSearch s target).hand = s.hand := by
  unfold quickSearch
  simp [hUsed, hDeck]

/-- [T39] Pidgeot consistency: if an answer card is in deck and ability unused,
    you can guarantee that answer in hand this turn. -/
theorem pidgeot_consistency_any_answer (s : SearchState) (answer : String)
    (hUsed : s.quickSearchUsed = false) (hDeck : answer ∈ s.deck) :
    hasAnswer (quickSearch s answer) answer := by
  unfold hasAnswer
  exact quick_search_finds_target s answer hUsed hDeck

/-- [T40] Quick Search provides at least one-card hand growth on a hit. -/
theorem quick_search_hit_increases_hand_length (s : SearchState) (target : String)
    (hUsed : s.quickSearchUsed = false) (hDeck : target ∈ s.deck) :
    (quickSearch s target).hand.length = s.hand.length + 1 := by
  unfold quickSearch
  simp [hUsed, hDeck]

-- ============================================================
-- §5  Energy acceleration package (Arcanine ex, Magma Basin)
-- ============================================================

structure EnergyState where
  activeFire : Nat
  benchFire : Nat
  discardFire : Nat
  benchDamage : Nat
  deriving DecidableEq, Repr

/-- Magma Basin places 2 damage counters (20 damage) on the benched Pokémon. -/
def magmaBasinDamage : Nat := 20

/-- Magma Basin: attach one Fire from discard to bench, place 20 damage. -/
def magmaBasin (s : EnergyState) : EnergyState :=
  if h : s.discardFire = 0 then s
  else { s with
      benchFire := s.benchFire + 1
      discardFire := s.discardFire - 1
      benchDamage := s.benchDamage + magmaBasinDamage }

/-- Arcanine ex modeled as accelerating 2 Fire energy to active attacker. -/
def arcanineAccelerate (s : EnergyState) : EnergyState :=
  { s with activeFire := s.activeFire + 2 }

/-- [T41] Magma Basin damage constant is 20. -/
theorem magma_basin_damage_value : magmaBasinDamage = 20 := rfl

/-- [T42] Arcanine acceleration adds exactly 2 active Fire energy. -/
theorem arcanine_accel_adds_two (s : EnergyState) :
    (arcanineAccelerate s).activeFire = s.activeFire + 2 := rfl

/-- [T43] If discard has no Fire, Magma Basin is a no-op. -/
theorem magma_basin_no_discard_noop (s : EnergyState) (h : s.discardFire = 0) :
    magmaBasin s = s := by
  unfold magmaBasin
  simp [h]

/-- [T44] If discard has Fire, Magma Basin adds 1 bench Fire. -/
theorem magma_basin_adds_bench_energy (s : EnergyState) (h : s.discardFire ≠ 0) :
    (magmaBasin s).benchFire = s.benchFire + 1 := by
  unfold magmaBasin
  simp [h]

/-- [T45] If discard has Fire, Magma Basin adds 20 bench damage. -/
theorem magma_basin_adds_damage (s : EnergyState) (h : s.discardFire ≠ 0) :
    (magmaBasin s).benchDamage = s.benchDamage + 20 := by
  unfold magmaBasin
  simp [h, magmaBasinDamage]

/-- [T46] If discard has Fire, Magma Basin consumes 1 discard Fire. -/
theorem magma_basin_consumes_one_discard (s : EnergyState) (h : s.discardFire ≠ 0) :
    (magmaBasin s).discardFire = s.discardFire - 1 := by
  unfold magmaBasin
  simp [h]

/-- [T47] Arcanine acceleration is monotone in active energy. -/
theorem arcanine_accel_monotone (s : EnergyState) :
    s.activeFire ≤ (arcanineAccelerate s).activeFire := by
  simp [arcanineAccelerate]

/-- [T48] Magma Basin never decreases bench damage. -/
theorem magma_basin_damage_monotone (s : EnergyState) :
    s.benchDamage ≤ (magmaBasin s).benchDamage := by
  unfold magmaBasin
  by_cases h : s.discardFire = 0
  · simp [h]
  · simp [h, magmaBasinDamage]

-- ============================================================
-- §6  OHKO thresholds for Burning Darkness
-- ============================================================

/-- OHKO relation: damage at least target HP. -/
def ohko (damage hp : Nat) : Prop := damage ≥ hp

/-- [T49] At 0 prizes, Charizard ex OHKOs 180 HP targets. -/
theorem ohko_180_at_zero_prizes : ohko (burningDarkness 0) 180 := by
  unfold ohko
  rw [burning_at_0]
  omega

/-- [T50] At 2 prizes, Charizard ex OHKOs 220 HP targets (240 damage). -/
theorem ohko_220_at_two_prizes : ohko (burningDarkness 2) 220 := by
  unfold ohko
  rw [burning_at_2]
  omega

/-- [T51] At 4 prizes, Charizard ex OHKOs 280 HP targets (300 damage). -/
theorem ohko_280_at_four_prizes : ohko (burningDarkness 4) 280 := by
  unfold ohko
  rw [burning_at_4]
  omega

/-- [T52] At 5 prizes, Charizard ex OHKOs 330 HP targets. -/
theorem ohko_330_at_five_prizes : ohko (burningDarkness 5) 330 := by
  unfold ohko
  rw [burning_at_5]
  omega

/-- [T53] At 4 prizes, 300 damage is not enough for 330 HP. -/
theorem no_ohko_330_at_four_prizes : ¬ ohko (burningDarkness 4) 330 := by
  unfold ohko
  rw [burning_at_4]
  omega

/-- [T54] Even at 5 prizes, 340 HP is not OHKOed. -/
theorem no_ohko_340_at_five_prizes : ¬ ohko (burningDarkness 5) 340 := by
  unfold ohko
  rw [burning_at_5]
  omega

/-- [T55] Charizard mirror OHKO occurs at 5 prizes (330 into 330). -/
theorem charizard_mirror_ohko_at_five :
    ohko (burningDarkness 5) charizardEx.hp := by
  unfold ohko
  rw [charizard_hp_value, burning_at_5]
  omega

/-- [T56] General OHKO criterion from damage bound. -/
theorem ohko_if_damage_ge_hp (p hp : Nat) (h : burningDarkness p ≥ hp) :
    ohko (burningDarkness p) hp := h

/-- [T57] If legal prizes are taken, damage is at most 330. -/
theorem legal_damage_upper_bound (p : Nat) (h : legalPrizesTaken p) :
    burningDarkness p ≤ 330 :=
  burning_legal_max_bound p h

-- ============================================================
-- §7  Prize-race pressure and game progression
-- ============================================================

/-- Extra damage over base from taken prizes. -/
def bonusDamageFromPrizes (p : Nat) : Nat := burningDarkness p - burningBase

/-- [T58] Bonus at 0 prizes is 0. -/
theorem bonus_at_zero : bonusDamageFromPrizes 0 = 0 := by
  native_decide

/-- [T59] Bonus at 1 prize is 30. -/
theorem bonus_at_one : bonusDamageFromPrizes 1 = 30 := by
  native_decide

/-- [T60] Bonus at 3 prizes is 90. -/
theorem bonus_at_three : bonusDamageFromPrizes 3 = 90 := by
  native_decide

/-- [T61] Bonus at 5 prizes is 150. -/
theorem bonus_at_five : bonusDamageFromPrizes 5 = 150 := by
  native_decide

/-- [T62] Bonus damage is monotone. -/
theorem bonus_formula (p : Nat) :
    bonusDamageFromPrizes p = burningPerPrize * p := by
  unfold bonusDamageFromPrizes burningDarkness burningBase burningPerPrize
  omega

/-- [T63] Bonus damage is monotone. -/
theorem bonus_monotone (p q : Nat) (h : p ≤ q) :
    bonusDamageFromPrizes p ≤ bonusDamageFromPrizes q := by
  rw [bonus_formula, bonus_formula]
  exact Nat.mul_le_mul_left _ h

/-- [T64] Bonus damage strictly increases with prizes. -/
theorem bonus_strict_mono (p q : Nat) (h : p < q) :
    bonusDamageFromPrizes p < bonusDamageFromPrizes q := by
  rw [bonus_formula, bonus_formula]
  have hPos : 0 < burningPerPrize := by
    native_decide
  exact Nat.mul_lt_mul_of_pos_left h hPos

/-- [T65] At legal max, total formula is 180 + 150. -/
theorem max_formula_breakdown :
    burningDarkness 5 = burningBase + 150 := by
  unfold burningDarkness burningBase burningPerPrize
  omega

/-- [T66] Charizard ex becomes stronger as the prize race advances. -/
theorem prize_scaling_progression_statement (p : Nat) :
    burningDarkness (p + 1) = burningDarkness p + burningPerPrize := by
  rw [burning_step_adds_30]
  rfl

end PokemonLean.Core.CharizardDeck
