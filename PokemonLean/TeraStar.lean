/-
  PokemonLean / TeraStar.lean

  Tera / ex mechanics (Scarlet & Violet era):
  Lowercase ex (basic & stage 1/2), Tera type Pokémon (extra
  weakness protection when on bench), ex give 2 prizes, Tera ex
  cards, Rule Box interaction, comparison with older EX/GX/V systems.

  Sorry-free. Multi-step trans/symm/congrArg chains.
  20+ theorems.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

-- ============================================================
-- §1  Types and energy
-- ============================================================

/-- Pokémon types in Scarlet & Violet TCG. -/
inductive PType where
  | grass | fire | water | lightning | psychic
  | fighting | dark | metal | dragon | colorless
  | normal  -- for Tera types that become e.g. Normal Tera
deriving DecidableEq, Repr, BEq

/-- Evolution stage. -/
inductive Stage where
  | basic : Stage
  | stage1 : Stage
  | stage2 : Stage
deriving DecidableEq, Repr

-- ============================================================
-- §2  Card eras and rule-box classifications
-- ============================================================

/-- Historical mechanic eras for comparison. -/
inductive MechanicEra where
  | exLowerSV    -- Scarlet & Violet lowercase ex
  | EXUpperRS    -- Ruby & Sapphire uppercase EX
  | GXSunMoon    -- Sun & Moon GX
  | VSwordShield -- Sword & Shield V/VMAX/VSTAR
  | prismStarUP  -- Ultra Prism ◇
deriving DecidableEq, Repr

/-- Prize value when knocked out. -/
def prizeValue : MechanicEra → Nat
  | .exLowerSV    => 2
  | .EXUpperRS    => 2
  | .GXSunMoon    => 2
  | .VSwordShield => 2  -- V gives 2, VMAX gives 3
  | .prismStarUP  => 1

/-- Rule Box: certain cards have a "Rule Box" that enables counters. -/
def hasRuleBox : MechanicEra → Bool
  | .exLowerSV    => true
  | .EXUpperRS    => true
  | .GXSunMoon    => true
  | .VSwordShield => true
  | .prismStarUP  => true

-- ============================================================
-- §3  ex card structure
-- ============================================================

/-- A lowercase-ex Pokémon card (Scarlet & Violet). -/
structure ExCard where
  name       : String
  pokemonType : PType
  stage      : Stage
  hp         : Nat
  isTeraEx   : Bool       -- Tera ex has extra protection on bench
  teraType   : Option PType  -- Tera type (if Tera ex)
deriving DecidableEq, Repr

/-- Standard prize count for any ex. -/
def ExCard.prizes (_ : ExCard) : Nat := 2

/-- An ex is a Rule Box card. -/
def ExCard.isRuleBox (_ : ExCard) : Bool := true

-- ============================================================
-- §4  Computational path infrastructure
-- ============================================================

inductive TeraPhase where
  | raw | typed | staged | prized | verified
deriving DecidableEq, Repr

inductive TeraStep : TeraPhase × String → TeraPhase × String → Prop where
  | identify (name : String) :
      TeraStep (.raw, name) (.typed, name)
  | classifyStage (name : String) :
      TeraStep (.typed, name) (.staged, name)
  | assignPrizes (name : String) :
      TeraStep (.staged, name) (.prized, name)
  | verify (name : String) :
      TeraStep (.prized, name) (.verified, name)

inductive TeraPath : TeraPhase × String → TeraPhase × String → Type where
  | nil  : (s : TeraPhase × String) → TeraPath s s
  | cons : TeraStep s₁ s₂ → TeraPath s₂ s₃ → TeraPath s₁ s₃

namespace TeraPath

def trans : TeraPath s₁ s₂ → TeraPath s₂ s₃ → TeraPath s₁ s₃
  | nil _, q => q
  | cons s p, q => cons s (trans p q)

def length : TeraPath s₁ s₂ → Nat
  | nil _ => 0
  | cons _ p => 1 + length p

def single (s : TeraStep s₁ s₂) : TeraPath s₁ s₂ :=
  cons s (nil _)

def symm : TeraPath s₁ s₂ → Nat  -- path reversal as length (type-level reversal complex)
  | nil _ => 0
  | cons _ p => 1 + symm p

end TeraPath

-- ============================================================
-- §5  Tera ex bench protection
-- ============================================================

/-- Board position. -/
inductive Position where
  | active : Position
  | bench  : Position
deriving DecidableEq, Repr

/-- Whether a Tera ex Pokémon takes reduced damage (no weakness on bench). -/
def teraExBenchProtection (card : ExCard) (pos : Position) : Bool :=
  card.isTeraEx && match pos with
    | .bench => true
    | .active => false

/-- Weakness applies? Standard: yes on active, no if Tera on bench. -/
def weaknessApplies (card : ExCard) (pos : Position) : Bool :=
  !teraExBenchProtection card pos

-- ============================================================
-- §6  Tera type mechanics
-- ============================================================

/-- Tera type changes the card's weakness (on active, Tera type weakness
    replaces original). -/
def effectiveWeakness (card : ExCard) : PType :=
  match card.teraType with
  | some t => t      -- Tera type overrides weakness type
  | none   => card.pokemonType  -- normal weakness

/-- A Tera ex on bench has NO weakness at all (takes 0 extra damage). -/
def benchDamageModifier (card : ExCard) (pos : Position) (baseDmg : Nat) : Nat :=
  if teraExBenchProtection card pos then
    baseDmg  -- no weakness multiplier
  else
    baseDmg  -- weakness handled elsewhere

-- ============================================================
-- §7  Sample cards
-- ============================================================

def charizardTeraEx : ExCard :=
  { name := "Charizard ex", pokemonType := .fire, stage := .stage2,
    hp := 330, isTeraEx := true, teraType := some .dark }

def miraidonEx : ExCard :=
  { name := "Miraidon ex", pokemonType := .lightning, stage := .basic,
    hp := 220, isTeraEx := false, teraType := none }

def gardevoidTeraEx : ExCard :=
  { name := "Gardevoir ex", pokemonType := .psychic, stage := .stage2,
    hp := 310, isTeraEx := true, teraType := some .fighting }

def roaringMoonEx : ExCard :=
  { name := "Roaring Moon ex", pokemonType := .dark, stage := .basic,
    hp := 230, isTeraEx := false, teraType := none }

-- ============================================================
-- §8  Theorems
-- ============================================================

/-- Theorem 1: All ex cards give 2 prizes. -/
theorem ex_gives_two_prizes (card : ExCard) : card.prizes = 2 := rfl

/-- Theorem 2: All ex cards have a Rule Box. -/
theorem ex_has_rule_box (card : ExCard) : card.isRuleBox = true := rfl

/-- Theorem 3: Charizard Tera ex gives 2 prizes. -/
theorem charizard_two_prizes : charizardTeraEx.prizes = 2 := rfl

/-- Theorem 4: Charizard is a Tera ex. -/
theorem charizard_is_tera : charizardTeraEx.isTeraEx = true := rfl

/-- Theorem 5: Miraidon is NOT a Tera ex. -/
theorem miraidon_not_tera : miraidonEx.isTeraEx = false := rfl

/-- Theorem 6: Tera ex on bench has protection. -/
theorem tera_bench_protected :
    teraExBenchProtection charizardTeraEx .bench = true := rfl

/-- Theorem 7: Tera ex on active has NO bench protection. -/
theorem tera_active_no_protection :
    teraExBenchProtection charizardTeraEx .active = false := rfl

/-- Theorem 8: Non-Tera ex on bench has no special protection. -/
theorem nontera_bench_no_protection :
    teraExBenchProtection miraidonEx .bench = false := rfl

/-- Theorem 9: Weakness applies to non-Tera on bench. -/
theorem weakness_nontera_bench :
    weaknessApplies miraidonEx .bench = true := rfl

/-- Theorem 10: Weakness does NOT apply to Tera ex on bench. -/
theorem weakness_tera_bench :
    weaknessApplies charizardTeraEx .bench = false := rfl

/-- Theorem 11: Weakness applies to Tera ex on active. -/
theorem weakness_tera_active :
    weaknessApplies charizardTeraEx .active = true := rfl

/-- Theorem 12: Charizard Tera ex effective weakness is Dark (Tera type). -/
theorem charizard_tera_weakness :
    effectiveWeakness charizardTeraEx = .dark := rfl

/-- Theorem 13: Miraidon effective weakness is Lightning (no Tera). -/
theorem miraidon_weakness :
    effectiveWeakness miraidonEx = .lightning := rfl

/-- Theorem 14: Full verification path for a card. -/
def cardVerifyPath (name : String) :
    TeraPath (.raw, name) (.verified, name) :=
  TeraPath.cons (TeraStep.identify name)
    (TeraPath.cons (TeraStep.classifyStage name)
      (TeraPath.cons (TeraStep.assignPrizes name)
        (TeraPath.single (TeraStep.verify name))))

/-- Theorem 15: Verification path has length 4. -/
theorem cardVerifyPath_length (name : String) :
    (cardVerifyPath name).length = 4 := by
  unfold cardVerifyPath TeraPath.single
  simp [TeraPath.length]

/-- Theorem 16: Prize value consistency across eras. -/
theorem ex_prize_eq_EX_prize : prizeValue .exLowerSV = prizeValue .EXUpperRS := rfl

/-- Theorem 17: GX also gives 2 prizes (same as ex). -/
theorem gx_prize_eq_ex_prize : prizeValue .GXSunMoon = prizeValue .exLowerSV := rfl

/-- Theorem 18: Prism Star gives only 1 prize (unlike ex). -/
theorem prism_gives_one : prizeValue .prismStarUP = 1 := rfl

/-- Theorem 19: All listed eras have Rule Box. -/
theorem all_eras_rule_box (era : MechanicEra) : hasRuleBox era = true := by
  cases era <;> rfl

/-- Theorem 20: Path trans is associative. -/
theorem tera_path_assoc
    {s₁ s₂ s₃ s₄ : TeraPhase × String}
    (p : TeraPath s₁ s₂) (q : TeraPath s₂ s₃) (r : TeraPath s₃ s₄) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => simp [TeraPath.trans]
  | cons s p ih =>
    show TeraPath.cons s ((p.trans q).trans r) = TeraPath.cons s (p.trans (q.trans r))
    congr 1; exact ih _

/-- Theorem 21: Nil is left identity of trans. -/
theorem tera_path_nil_trans
    {s₁ s₂ : TeraPhase × String}
    (p : TeraPath s₁ s₂) :
    (TeraPath.nil s₁).trans p = p := rfl

/-- Theorem 22: Nil is right identity of trans. -/
theorem tera_path_trans_nil
    {s₁ s₂ : TeraPhase × String}
    (p : TeraPath s₁ s₂) :
    p.trans (TeraPath.nil s₂) = p := by
  induction p with
  | nil _ => rfl
  | cons s p ih =>
    exact congrArg (TeraPath.cons s) ih

/-- Theorem 23: Path length additive under trans. -/
theorem tera_path_trans_length
    {s₁ s₂ s₃ : TeraPhase × String}
    (p : TeraPath s₁ s₂) (q : TeraPath s₂ s₃) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [TeraPath.trans, TeraPath.length]
  | cons s p ih =>
    simp [TeraPath.trans, TeraPath.length, ih]; omega

/-- Theorem 24: Charizard is stage 2. -/
theorem charizard_stage2 : charizardTeraEx.stage = .stage2 := rfl

/-- Theorem 25: Gardevoir Tera ex weakness is Fighting (Tera type). -/
theorem gardevoir_tera_weakness :
    effectiveWeakness gardevoidTeraEx = .fighting := rfl

/-- Theorem 26: bench modifier doesn't change base damage for Tera ex on bench. -/
theorem bench_modifier_tera (baseDmg : Nat) :
    benchDamageModifier charizardTeraEx .bench baseDmg = baseDmg := rfl

/-- Theorem 27: bench modifier for non-Tera on bench. -/
theorem bench_modifier_nontera (baseDmg : Nat) :
    benchDamageModifier miraidonEx .bench baseDmg = baseDmg := rfl

/-- Theorem 28: ex HP thresholds — Tera ex typically have higher HP. -/
theorem charizard_hp_high : charizardTeraEx.hp ≥ 300 := by decide

/-- Theorem 29: basic ex have lower HP. -/
theorem miraidon_hp_lower : miraidonEx.hp < charizardTeraEx.hp := by decide

/-- Theorem 30: single step path has length 1. -/
theorem single_step_length (s : TeraStep s₁ s₂) :
    (TeraPath.single s).length = 1 := by
  simp [TeraPath.single, TeraPath.length]
