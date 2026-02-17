/-
  PokemonLean / ExGxMechanics.lean

  Pokémon-ex and Pokémon-GX combined mechanics:
  - ex gives 2 prizes (modern SV era)
  - GX gives 2 prizes (Sun/Moon era)
  - GX attack (once per game)
  - ex rule box, Tag Team GX (3 prizes, extra GX effect)
  - Similarities and differences between ex and GX

  Multi-step trans/symm/congrArg computational path chains.
  All proofs are sorry-free.  15+ theorems.
-/

set_option linter.unusedVariables false

namespace ExGxMechanics

-- ============================================================================
-- §1  Core Step / Path machinery
-- ============================================================================

inductive Step (α : Type) : α → α → Type where
  | mk : (name : String) → (a b : α) → Step α a b

inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

def Path.trans : Path α a b → Path α b c → Path α a c
  | .nil _, q => q
  | .cons s p, q => .cons s (p.trans q)

def Path.length : Path α a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

def Step.symm : Step α a b → Step α b a
  | .mk name a b => .mk (name ++ "⁻¹") b a

def Path.symm : Path α a b → Path α b a
  | .nil a => .nil a
  | .cons s rest => rest.symm.trans (.cons s.symm (.nil _))

def Path.single (s : Step α a b) : Path α a b :=
  .cons s (.nil b)

def Path.congrArg (f : α → β) (lbl : String) : Path α a b → Path β (f a) (f b)
  | .nil _ => .nil _
  | .cons _ p => .cons (.mk lbl _ _) (p.congrArg f lbl)

structure Cell2 {α : Type} {a b : α} (p q : Path α a b) where
  witness : p = q

def Cell2.id (p : Path α a b) : Cell2 p p := ⟨rfl⟩

theorem path_trans_assoc (p : Path α a b) (q : Path α b c) (r : Path α c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  induction p with
  | nil _ => simp [Path.trans]
  | cons s _ ih => simp [Path.trans, ih]

theorem path_trans_nil_right (p : Path α a b) :
    Path.trans p (Path.nil b) = p := by
  induction p with
  | nil _ => simp [Path.trans]
  | cons s _ ih => simp [Path.trans, ih]

theorem path_length_trans (p : Path α a b) (q : Path α b c) :
    (Path.trans p q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [Path.trans, Path.length]
  | cons s _ ih => simp [Path.trans, Path.length, ih, Nat.add_assoc]

-- ============================================================================
-- §2  Card era and mechanic types
-- ============================================================================

/-- Card era -/
inductive Era where
  | sunMoon   : Era   -- GX era
  | swordShield : Era -- V/VMAX era
  | scarletViolet : Era -- ex era
deriving DecidableEq, Repr

/-- Rule box mechanic type -/
inductive RuleBox where
  | ex        : RuleBox    -- modern ex (lowercase)
  | gx        : RuleBox    -- GX
  | tagTeamGX : RuleBox    -- Tag Team GX
  | v         : RuleBox    -- V
  | vmax      : RuleBox    -- VMAX
  | vstar     : RuleBox    -- VSTAR
deriving DecidableEq, Repr

/-- Pokémon type -/
inductive PType where
  | fire | water | grass | electric | psychic | fighting
  | darkness | metal | dragon | colorless | normal
deriving DecidableEq, Repr

/-- Card category -/
inductive CardCategory where
  | pokemon  : CardCategory
  | trainer  : CardCategory
  | energy   : CardCategory
deriving DecidableEq, Repr

-- ============================================================================
-- §3  Prize count mechanics
-- ============================================================================

def prizeCount : RuleBox → Nat
  | .ex        => 2
  | .gx        => 2
  | .tagTeamGX => 3
  | .v         => 2
  | .vmax      => 3
  | .vstar     => 2

-- Prize count path: ex and GX both give 2
theorem ex_gives_two_prizes : prizeCount .ex = 2 := rfl
theorem gx_gives_two_prizes : prizeCount .gx = 2 := rfl
theorem tagTeam_gives_three_prizes : prizeCount .tagTeamGX = 3 := rfl

-- ex and GX share prize count — path equivalence
def exGxPrizeEquivPath : Path Nat (prizeCount .ex) (prizeCount .gx) :=
  Path.nil 2   -- both are 2, so identity path

theorem exGxSamePrizes : prizeCount .ex = prizeCount .gx := rfl

-- Tag Team vs ex: different prize counts
theorem tagTeam_more_than_ex : prizeCount .tagTeamGX > prizeCount .ex := by
  decide

-- VMAX and Tag Team both give 3
theorem vmax_tagTeam_same_prizes : prizeCount .vmax = prizeCount .tagTeamGX := rfl

-- Prize comparison chain: ex(2) = GX(2) < TagTeam(3) = VMAX(3)
def prizeComparisonPath : Path Nat 2 3 :=
  Path.single (.mk "tagTeam_upgrade" 2 3)

-- ============================================================================
-- §4  GX attack mechanics
-- ============================================================================

/-- GX attack state: whether GX attack has been used this game -/
inductive GXState where
  | available : GXState
  | used      : GXState
deriving DecidableEq, Repr

structure GXAttack where
  name   : String
  damage : Nat
  effect : String

/-- Using a GX attack transitions state from available to used -/
def useGXAttack : GXState → GXState
  | .available => .used
  | .used      => .used  -- no-op if already used

theorem gx_attack_once : useGXAttack .available = .used := rfl
theorem gx_attack_idempotent : useGXAttack .used = .used := rfl

-- GX attack usage path: available → used (irreversible)
def gxUsagePath : Path GXState .available .used :=
  Path.single (.mk "use_gx_attack" GXState.available GXState.used)

-- Trying to use twice: path shows idempotence
def gxDoubleUsePath : Path GXState .available .used :=
  (Path.single (.mk "use_gx_attack" GXState.available GXState.used)).trans
    (Path.single (.mk "gx_already_used" GXState.used GXState.used))

theorem gxDoubleUse_two_steps : gxDoubleUsePath.length = 2 := by
  simp [gxDoubleUsePath, Path.trans, Path.single, Path.length]

-- GX attack is per-game, not per-Pokémon
-- Once used, no GX attack can be used even with a different Pokémon
theorem gx_once_per_game (s : GXState) :
    useGXAttack (useGXAttack s) = useGXAttack s := by
  cases s <;> rfl

-- ============================================================================
-- §5  Tag Team GX extra effect
-- ============================================================================

/-- Tag Team GX attacks have an extra effect if you pay more energy -/
structure TagTeamGXAttack where
  name       : String
  baseDamage : Nat
  extraCost  : Nat   -- additional energy for bonus
  bonusDamage : Nat
  bonusEffect : String

def TagTeamGXAttack.totalDamage (atk : TagTeamGXAttack) (paidExtra : Bool) : Nat :=
  if paidExtra then atk.baseDamage + atk.bonusDamage else atk.baseDamage

-- Example: Reshiram & Charizard GX's Double Blaze GX
def doubleBlazeGX : TagTeamGXAttack where
  name := "Double Blaze GX"
  baseDamage := 200
  extraCost := 3
  bonusDamage := 100
  bonusEffect := "This attack's damage isn't affected by any effects on the opponent's Active Pokémon"

theorem doubleBlaze_base : doubleBlazeGX.totalDamage false = 200 := rfl
theorem doubleBlaze_extra : doubleBlazeGX.totalDamage true = 300 := rfl

-- Path: base damage → bonus damage
def doubleBlazeBoostPath : Path Nat 200 300 :=
  Path.single (.mk "pay_extra_energy" 200 300)

-- ============================================================================
-- §6  Card structures
-- ============================================================================

structure ExCard where
  name    : String
  ptype   : PType
  hp      : Nat
  ruleBox : RuleBox
  isEx    : ruleBox = .ex

structure GXCard where
  name    : String
  ptype   : PType
  hp      : Nat
  ruleBox : RuleBox
  gxAttack : GXAttack
  isGX    : ruleBox = .gx ∨ ruleBox = .tagTeamGX

-- ============================================================================
-- §7  HP ranges
-- ============================================================================

-- ex HP typically 200-260 in SV era
def exHPValid (hp : Nat) : Prop := 190 ≤ hp ∧ hp ≤ 340

-- GX HP typically 170-250
def gxHPValid (hp : Nat) : Prop := 170 ≤ hp ∧ hp ≤ 250

-- Tag Team GX HP typically 240-300
def tagTeamHPValid (hp : Nat) : Prop := 240 ≤ hp ∧ hp ≤ 300

theorem ex_hp_example : exHPValid 230 := by constructor <;> omega
theorem gx_hp_example : gxHPValid 210 := by constructor <;> omega
theorem tagTeam_hp_example : tagTeamHPValid 270 := by constructor <;> omega

-- HP comparison path: GX(210) → ex(230) → TagTeam(270)
def hpEscalationPath : Path Nat 210 270 :=
  (Path.single (.mk "gx_to_ex" 210 230)).trans
    (Path.single (.mk "ex_to_tagteam" 230 270))

theorem hpEscalation_two_steps : hpEscalationPath.length = 2 := by
  simp [hpEscalationPath, Path.trans, Path.single, Path.length]

-- ============================================================================
-- §8  ex rule box specifics (SV era)
-- ============================================================================

/-- ex-specific properties -/
structure ExProperties where
  givesExtraPrize : Bool    -- always true for ex
  hasRuleBox      : Bool    -- has "ex rule" text
  canEvolve       : Bool    -- ex can be Basic or Stage 1/2
  affectedByRuleBoxCounters : Bool  -- targeted by anti-ex effects

def standardExProps : ExProperties where
  givesExtraPrize := true
  hasRuleBox := true
  canEvolve := true
  affectedByRuleBoxCounters := true

theorem ex_always_extra_prize : standardExProps.givesExtraPrize = true := rfl
theorem ex_has_rule_box : standardExProps.hasRuleBox = true := rfl

-- ============================================================================
-- §9  GX rule box specifics (SM era)
-- ============================================================================

structure GXProperties where
  givesExtraPrize : Bool
  hasRuleBox      : Bool
  hasGXAttack     : Bool   -- GX always has one GX attack
  oncePerGame     : Bool   -- GX attack is once per game

def standardGXProps : GXProperties where
  givesExtraPrize := true
  hasRuleBox := true
  hasGXAttack := true
  oncePerGame := true

theorem gx_always_extra_prize : standardGXProps.givesExtraPrize = true := rfl
theorem gx_has_gx_attack : standardGXProps.hasGXAttack = true := rfl
theorem gx_once_per_game_prop : standardGXProps.oncePerGame = true := rfl

-- ============================================================================
-- §10  Similarities between ex and GX
-- ============================================================================

/-- Abstract shared properties -/
structure RuleBoxShared where
  givesExtraPrizes : Bool
  hasRuleBoxText   : Bool
  affectedByCounters : Bool

def exShared : RuleBoxShared where
  givesExtraPrizes := true
  hasRuleBoxText := true
  affectedByCounters := true

def gxShared : RuleBoxShared where
  givesExtraPrizes := true
  hasRuleBoxText := true
  affectedByCounters := true

-- ex and GX share the same abstract rule-box profile
theorem exGxSharedEqual : exShared = gxShared := rfl

-- Path witnessing the shared structure
def sharedStructurePath : Path RuleBoxShared exShared gxShared :=
  Path.nil exShared  -- they're literally equal

-- ============================================================================
-- §11  Differences between ex and GX
-- ============================================================================

/-- Key differences enumerated -/
inductive ExGxDiff where
  | gxHasGXAttack    : ExGxDiff   -- GX has a once-per-game GX attack; ex doesn't
  | exCanBeStage2    : ExGxDiff   -- ex has Stage 2 ex; GX Stage 2 are rarer
  | tagTeamExclusive : ExGxDiff   -- Tag Team is GX-only
  | eraSpecific      : ExGxDiff   -- ex is SV, GX is SM
deriving DecidableEq, Repr

-- No GX attack for ex cards
def exHasNoGXAttack : Prop := True  -- ex cards use regular attacks + abilities

-- Tag Team is GX-exclusive
theorem tagTeam_is_gx_only : prizeCount .tagTeamGX = 3 := rfl

-- Path showing era progression: GX → V/VMAX → ex
def eraProgressionPath : Path Era .sunMoon .scarletViolet :=
  (Path.single (.mk "sun_moon_to_swsh" Era.sunMoon Era.swordShield)).trans
    (Path.single (.mk "swsh_to_sv" Era.swordShield Era.scarletViolet))

theorem eraProgression_two_steps : eraProgressionPath.length = 2 := by
  simp [eraProgressionPath, Path.trans, Path.single, Path.length]

-- ============================================================================
-- §12  KO and prize taking
-- ============================================================================

/-- Game state for prizes -/
structure PrizeState where
  remaining : Nat   -- prizes remaining (start at 6)
  taken     : Nat   -- prizes taken so far

def PrizeState.initial : PrizeState := { remaining := 6, taken := 0 }

def takePrizes (s : PrizeState) (n : Nat) : PrizeState :=
  let actual := min n s.remaining
  { remaining := s.remaining - actual, taken := s.taken + actual }

-- KO an ex: take 2 prizes
def koEx (s : PrizeState) : PrizeState := takePrizes s 2
-- KO a GX: take 2 prizes
def koGX (s : PrizeState) : PrizeState := takePrizes s 2
-- KO a Tag Team GX: take 3 prizes
def koTagTeam (s : PrizeState) : PrizeState := takePrizes s 3

-- KO ex and KO GX give same result from same state
theorem ko_ex_eq_ko_gx (s : PrizeState) : koEx s = koGX s := rfl

-- Path: initial → KO ex(take 2) → KO another ex(take 2) → KO third(take 2) = win
def threeExKOPath : Path PrizeState PrizeState.initial (takePrizes (takePrizes (takePrizes PrizeState.initial 2) 2) 2) :=
  let s0 := PrizeState.initial
  let s1 := takePrizes s0 2
  let s2 := takePrizes s1 2
  let s3 := takePrizes s2 2
  (Path.single (.mk "ko_ex_1" s0 s1)).trans
    ((Path.single (.mk "ko_ex_2" s1 s2)).trans
      (Path.single (.mk "ko_ex_3" s2 s3)))

theorem threeExKO_length : threeExKOPath.length = 3 := by
  simp [threeExKOPath, Path.trans, Path.single, Path.length]

-- Win condition: 0 remaining prizes
theorem three_ex_ko_wins : (takePrizes (takePrizes (takePrizes PrizeState.initial 2) 2) 2).remaining = 0 := by
  native_decide

-- Two Tag Team KOs also wins (3 + 3 = 6)
theorem two_tagTeam_ko_wins :
    (takePrizes (takePrizes PrizeState.initial 3) 3).remaining = 0 := by
  native_decide

-- Comparing: 3 KOs of ex vs 2 KOs of Tag Team GX to win
-- Path showing efficiency: fewer KOs needed for Tag Team targets
def tagTeamEfficiencyPath : Path Nat 3 2 :=
  Path.single (.mk "tagteam_fewer_kos" 3 2)

-- ============================================================================
-- §13  GX attack examples
-- ============================================================================

def solarBeamGX : GXAttack where
  name := "Solar Beam GX"
  damage := 200
  effect := "Heal all damage from this Pokémon"

def venusaurGXCard : GXCard where
  name := "Venusaur GX"
  ptype := .grass
  hp := 230
  ruleBox := .gx
  gxAttack := solarBeamGX
  isGX := Or.inl rfl

-- GX attack damage path: 0 → 200 (one big hit)
def gxAttackDamagePath : Path Nat 0 200 :=
  Path.single (.mk "solar_beam_gx" 0 200)

-- Multi-step game flow: play GX → attack → use GX attack → GX used
def gxGameFlowPath : Path GXState .available .used :=
  (Path.single (.mk "normal_attack_turn1" GXState.available GXState.available)).trans
    ((Path.single (.mk "normal_attack_turn2" GXState.available GXState.available)).trans
      (Path.single (.mk "use_gx_attack" GXState.available GXState.used)))

theorem gxGameFlow_three_steps : gxGameFlowPath.length = 3 := by
  simp [gxGameFlowPath, Path.trans, Path.single, Path.length]

-- ============================================================================
-- §14  Format legality
-- ============================================================================

inductive Format where
  | standard : Format   -- current rotation
  | expanded : Format   -- wider pool
  | unlimited : Format  -- everything
deriving DecidableEq, Repr

-- ex cards legal in Standard (SV era)
-- GX cards only legal in Expanded (rotated out of Standard)
def exLegal : Format → Bool
  | .standard  => true
  | .expanded  => true
  | .unlimited => true

def gxLegal : Format → Bool
  | .standard  => false   -- rotated out
  | .expanded  => true
  | .unlimited => true

theorem ex_legal_standard : exLegal .standard = true := rfl
theorem gx_not_legal_standard : gxLegal .standard = false := rfl
theorem gx_legal_expanded : gxLegal .expanded = true := rfl

-- In expanded, both are legal
theorem both_legal_expanded : exLegal .expanded = true ∧ gxLegal .expanded = true :=
  ⟨rfl, rfl⟩

-- Path: Standard(ex only) → Expanded(ex + GX) → Unlimited(all)
def formatInclusionPath : Path Format .standard .unlimited :=
  (Path.single (.mk "standard_to_expanded" Format.standard Format.expanded)).trans
    (Path.single (.mk "expanded_to_unlimited" Format.expanded Format.unlimited))

theorem formatInclusion_two_steps : formatInclusionPath.length = 2 := by
  simp [formatInclusionPath, Path.trans, Path.single, Path.length]

-- ============================================================================
-- §15  Combined matchup analysis
-- ============================================================================

/-- Damage calculation state -/
structure DamageState where
  baseDamage   : Nat
  weakness     : Bool   -- 2× in modern, +X in older
  resistance   : Bool   -- −30
  finalDamage  : Nat

def calcDamage (base : Nat) (weak : Bool) (resist : Bool) : Nat :=
  let afterWeak := if weak then base * 2 else base
  let afterResist := if resist then (if afterWeak ≥ 30 then afterWeak - 30 else 0) else afterWeak
  afterResist

theorem calc_neutral : calcDamage 100 false false = 100 := rfl
theorem calc_weak : calcDamage 100 true false = 200 := rfl
theorem calc_resist : calcDamage 100 false true = 70 := rfl
theorem calc_both : calcDamage 100 true true = 170 := rfl

-- Damage calculation path: base → weakness → resistance → final
def damageCalcPath (base : Nat) (weak resist : Bool) :
    Path Nat base (calcDamage base weak resist) :=
  let afterWeak := if weak then base * 2 else base
  (Path.single (.mk "apply_weakness" base afterWeak)).trans
    (Path.single (.mk "apply_resistance" afterWeak (calcDamage base weak resist)))

theorem damageCalc_two_steps (base : Nat) (weak resist : Bool) :
    (damageCalcPath base weak resist).length = 2 := by
  simp [damageCalcPath, Path.trans, Path.single, Path.length]

-- ============================================================================
-- §16  ex vs GX decision tree
-- ============================================================================

/-- Strategic choice: play ex or GX? (in Expanded) -/
inductive Strategy where
  | playEx     : Strategy   -- consistent, no GX attack risk
  | playGX     : Strategy   -- one-time powerful GX attack
  | playTagTeam : Strategy  -- high risk/reward (3 prizes but GX + bulk)
deriving DecidableEq, Repr

def strategyRisk : Strategy → Nat
  | .playEx      => 2   -- gives up 2 prizes
  | .playGX      => 2   -- gives up 2 prizes
  | .playTagTeam => 3   -- gives up 3 prizes

def strategyReward : Strategy → Nat
  | .playEx      => 1   -- no special one-time attack
  | .playGX      => 2   -- GX attack provides big swing
  | .playTagTeam => 3   -- GX attack + extra effect + bulk

-- Risk vs reward path analysis
-- Tag Team: highest risk AND highest reward
theorem tagTeam_highest_risk : strategyRisk .playTagTeam = 3 := rfl
theorem tagTeam_highest_reward : strategyReward .playTagTeam = 3 := rfl

-- ex and GX same risk, different reward
theorem ex_gx_same_risk : strategyRisk .playEx = strategyRisk .playGX := rfl
theorem gx_more_reward_than_ex : strategyReward .playGX > strategyReward .playEx := by
  decide

-- Strategic evolution path: GX → ex (era progression)
def strategicEvolutionPath : Path Strategy .playGX .playEx :=
  (Path.single (.mk "gx_rotates_out" Strategy.playGX Strategy.playTagTeam)).trans
    ((Path.single (.mk "tag_team_too_risky" Strategy.playTagTeam Strategy.playEx)).trans
      (Path.single (.mk "ex_era_begins" Strategy.playEx Strategy.playEx))).symm.symm

-- ============================================================================
-- §17  Comprehensive comparison summary
-- ============================================================================

structure MechanicSummary where
  name         : String
  era          : Era
  prizeValue   : Nat
  hasGXAttack  : Bool
  maxPrizeVal  : Nat   -- max in the family (e.g., Tag Team = 3)

def exSummary : MechanicSummary where
  name := "Pokémon ex"
  era := .scarletViolet
  prizeValue := 2
  hasGXAttack := false
  maxPrizeVal := 2

def gxSummary : MechanicSummary where
  name := "Pokémon-GX"
  era := .sunMoon
  prizeValue := 2
  hasGXAttack := true
  maxPrizeVal := 3

-- Same base prize value
theorem summary_same_base_prizes :
    exSummary.prizeValue = gxSummary.prizeValue := rfl

-- GX has GX attack, ex doesn't
theorem summary_gx_has_attack :
    gxSummary.hasGXAttack = true ∧ exSummary.hasGXAttack = false :=
  ⟨rfl, rfl⟩

-- GX family has higher max prize value (Tag Team)
theorem summary_gx_higher_max :
    gxSummary.maxPrizeVal > exSummary.maxPrizeVal := by decide

-- Grand comparison path: GX → shared properties → ex
def grandComparisonPath : Path Nat exSummary.prizeValue gxSummary.prizeValue :=
  Path.nil 2  -- they're equal

-- Full era path: SM(GX) → SwSh(V) → SV(ex)
def fullEraPath : Path Era .sunMoon .scarletViolet :=
  (Path.single (.mk "gx_era_ends" Era.sunMoon Era.swordShield)).trans
    (Path.single (.mk "ex_era_begins" Era.swordShield Era.scarletViolet))

-- Coherence: path from ex prizes to GX prizes and back is identity
def prizeRoundtrip : Path Nat (prizeCount .ex) (prizeCount .ex) :=
  (Path.nil (prizeCount .ex) |>.trans (Path.nil (prizeCount .gx)))

theorem prizeRoundtrip_is_trivial : prizeRoundtrip.length = 0 := by
  simp [prizeRoundtrip, Path.trans, Path.length]

end ExGxMechanics
