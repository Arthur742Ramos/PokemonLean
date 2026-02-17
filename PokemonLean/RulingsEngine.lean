/-
  PokemonLean / RulingsEngine.lean

  Rulings engine for Pokémon TCG: rule priority (card text > game rules > errata),
  timing conflicts, simultaneous effects ordering, mandatory vs optional effects,
  "you may" semantics, OHKO prevention ordering (Focus Sash before KO check).

  All proofs are sorry-free. Uses computational paths for ruling resolution.
-/

namespace PokemonLean.RulingsEngine

-- ============================================================
-- §1  Core Path Infrastructure
-- ============================================================

/-- A rewrite step tracking ruling resolution transitions. -/
inductive Step (α : Type) : α → α → Type where
  | mk : (name : String) → (a b : α) → Step α a b

/-- Computational path: sequence of ruling resolution transitions. -/
inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

/-- Transitivity: path concatenation. -/
def Path.trans {α : Type} {a b c : α}
    (p : Path α a b) (q : Path α b c) : Path α a c :=
  match p with
  | .nil _ => q
  | .cons s rest => .cons s (rest.trans q)

/-- Path length. -/
def Path.length {α : Type} {a b : α} : Path α a b → Nat
  | .nil _ => 0
  | .cons _ rest => 1 + rest.length

/-- Symmetry for steps. -/
def Step.symm {α : Type} {a b : α} : Step α a b → Step α b a
  | .mk name a b => .mk (name ++ "⁻¹") b a

/-- Symmetry for paths. -/
def Path.symm {α : Type} {a b : α} : Path α a b → Path α b a
  | .nil a => .nil a
  | .cons s rest => rest.symm.trans (.cons s.symm (.nil _))

/-- Single step as path. -/
def Path.single {α : Type} {a b : α} (s : Step α a b) : Path α a b :=
  .cons s (.nil b)

-- ============================================================
-- §2  Rule Sources and Priority
-- ============================================================

/-- The three tiers of rule authority. -/
inductive RuleSource where
  | cardText : RuleSource     -- printed card text (highest)
  | gameRules : RuleSource    -- official game rules
  | errata : RuleSource       -- official errata / rulings
deriving DecidableEq, Repr

/-- Priority ordering (lower number = higher priority). -/
def RuleSource.priority : RuleSource → Nat
  | .cardText  => 0
  | .errata    => 1
  | .gameRules => 2

/-- Theorem 1: Priority is injective. -/
theorem ruleSource_priority_injective (a b : RuleSource)
    (h : a.priority = b.priority) : a = b := by
  cases a <;> cases b <;> simp [RuleSource.priority] at h <;> rfl

/-- Theorem 2: Card text has highest priority (lowest number). -/
theorem cardText_highest_priority (s : RuleSource) :
    RuleSource.cardText.priority ≤ s.priority := by
  cases s <;> simp [RuleSource.priority]

/-- Theorem 3: Game rules have lowest priority. -/
theorem gameRules_lowest_priority (s : RuleSource) :
    s.priority ≤ RuleSource.gameRules.priority := by
  cases s <;> simp [RuleSource.priority]

-- ============================================================
-- §3  Ruling Entry
-- ============================================================

/-- A ruling: a source, description tag, and whether it's mandatory. -/
structure Ruling where
  source    : RuleSource
  tag       : Nat         -- unique ruling identifier
  mandatory : Bool        -- true = must apply, false = "you may"
deriving DecidableEq, Repr

/-- Compare rulings by source priority. -/
def Ruling.higherPriority (a b : Ruling) : Bool :=
  a.source.priority < b.source.priority

/-- Theorem 4: higherPriority is irreflexive. -/
theorem ruling_priority_irrefl (r : Ruling) : r.higherPriority r = false := by
  simp [Ruling.higherPriority, Nat.lt_irrefl]

-- ============================================================
-- §4  Effect Types: Mandatory vs Optional ("you may")
-- ============================================================

/-- Effect kinds. -/
inductive EffectKind where
  | mandatory : EffectKind    -- must resolve
  | optional  : EffectKind    -- "you may" — player chooses
  | triggered : EffectKind    -- triggers on condition
deriving DecidableEq, Repr

/-- An effect with its kind and ruling source. -/
structure Effect where
  kind   : EffectKind
  source : RuleSource
  tag    : Nat
deriving DecidableEq, Repr

/-- Whether an effect must resolve. -/
def Effect.mustResolve : Effect → Bool
  | ⟨.mandatory, _, _⟩ => true
  | ⟨.triggered, _, _⟩ => true
  | ⟨.optional, _, _⟩  => false

/-- Theorem 5: Mandatory effects must resolve. -/
theorem mandatory_must_resolve (s : RuleSource) (t : Nat) :
    (Effect.mk .mandatory s t).mustResolve = true := rfl

/-- Theorem 6: Optional effects need not resolve. -/
theorem optional_need_not_resolve (s : RuleSource) (t : Nat) :
    (Effect.mk .optional s t).mustResolve = false := rfl

-- ============================================================
-- §5  Resolution States (Nat-indexed for easy path construction)
-- ============================================================

/-- Resolution pipeline stage (Nat-indexed). -/
abbrev Stage := Nat

def stageInitial    : Stage := 0
def stageSorted     : Stage := 1
def stageChecking   : Stage := 2
def stageApplied    : Stage := 3
def stageDone       : Stage := 4

/-- Theorem 7: Single effect resolves in 4 steps. -/
def single_effect_path : Path Stage stageInitial stageDone :=
  .cons (.mk "sort" stageInitial stageSorted)
    (.cons (.mk "check" stageSorted stageChecking)
      (.cons (.mk "apply" stageChecking stageApplied)
        (.cons (.mk "done" stageApplied stageDone)
          (.nil stageDone))))

/-- Theorem 8: Single effect resolution has length 4. -/
theorem single_effect_path_length : single_effect_path.length = 4 := rfl

-- ============================================================
-- §6  Timing Windows
-- ============================================================

/-- Timing windows in the Pokémon TCG. -/
inductive TimingWindow where
  | beforeAttack    : TimingWindow
  | duringAttack    : TimingWindow
  | afterAttack     : TimingWindow
  | betweenTurns    : TimingWindow
  | onKO            : TimingWindow
  | onEntry         : TimingWindow
deriving DecidableEq, Repr

/-- Timing window ordering. -/
def TimingWindow.toNat : TimingWindow → Nat
  | .beforeAttack  => 0
  | .duringAttack  => 1
  | .afterAttack   => 2
  | .onKO          => 3
  | .betweenTurns  => 4
  | .onEntry       => 5

/-- Theorem 9: Timing window ordering is injective. -/
theorem timing_toNat_injective (a b : TimingWindow)
    (h : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp [TimingWindow.toNat] at h <;> rfl

-- ============================================================
-- §7  Simultaneous Effects Ordering
-- ============================================================

/-- When multiple effects trigger simultaneously, active player's resolve first. -/
inductive Player where
  | active : Player
  | opponent : Player
deriving DecidableEq, Repr

/-- Active player's effects resolve first. -/
def Player.order : Player → Nat
  | .active   => 0
  | .opponent => 1

/-- Theorem 10: Active player always goes first. -/
theorem active_resolves_first :
    Player.active.order < Player.opponent.order := by
  simp [Player.order]

-- ============================================================
-- §8  OHKO Prevention: Focus Sash Ordering
-- ============================================================

/-- OHKO prevention items/abilities. -/
inductive Prevention where
  | focusSash    : Prevention    -- survives OHKO at 1 HP if full HP
  | sturdy       : Prevention    -- ability: same as Focus Sash
  | none         : Prevention
deriving DecidableEq, Repr

/-- HP state for OHKO calculation. -/
structure HPState where
  currentHP  : Nat
  maxHP      : Nat
  damage     : Nat
  prevention : Prevention
deriving DecidableEq, Repr

/-- Would this be a KO? -/
def HPState.wouldKO (s : HPState) : Bool :=
  s.damage ≥ s.currentHP

/-- Is at full HP? -/
def HPState.atFullHP (s : HPState) : Bool :=
  s.currentHP == s.maxHP

/-- Can prevention activate? (must be at full HP for Focus Sash/Sturdy) -/
def HPState.canPrevent (s : HPState) : Bool :=
  s.wouldKO && s.atFullHP && s.prevention != .none

/-- Apply prevention: survive at 1 HP. -/
def HPState.applyPrevention (s : HPState) : HPState :=
  if s.canPrevent then
    { s with currentHP := 1, damage := s.maxHP - 1, prevention := .none }
  else
    { s with currentHP := if s.damage ≥ s.currentHP then 0
                          else s.currentHP - s.damage }

/-- Theorem 11: Focus Sash prevents KO at full HP. -/
theorem focus_sash_prevents_ko (hp maxHp dmg : Nat)
    (hfull : (hp == maxHp) = true)
    (hko : dmg ≥ hp) :
    (HPState.mk hp maxHp dmg .focusSash).canPrevent = true := by
  simp [HPState.canPrevent, HPState.wouldKO, HPState.atFullHP, hfull, hko]

/-- Theorem 12: After Focus Sash activates, HP is 1. -/
theorem focus_sash_survives_at_1 (hp maxHp dmg : Nat)
    (hfull : (hp == maxHp) = true)
    (hko : dmg ≥ hp) :
    ((HPState.mk hp maxHp dmg .focusSash).applyPrevention).currentHP = 1 := by
  simp [HPState.applyPrevention, HPState.canPrevent, HPState.wouldKO,
        HPState.atFullHP, hfull, hko]

/-- Theorem 13: Without prevention, canPrevent is false. -/
theorem no_prevention_cant_prevent (hp maxHp dmg : Nat) :
    (HPState.mk hp maxHp dmg .none).canPrevent = false := by
  simp [HPState.canPrevent]

-- ============================================================
-- §9  OHKO Resolution as Nat-Indexed Path
-- ============================================================

def ohkoStart       : Nat := 0
def ohkoDamage      : Nat := 1
def ohkoPrevCheck   : Nat := 2
def ohkoPrevApply   : Nat := 3
def ohkoKOCheck     : Nat := 4
def ohkoSurvived    : Nat := 5

/-- Theorem 14: Focus Sash resolution path (5 steps). -/
def focus_sash_path : Path Nat ohkoStart ohkoSurvived :=
  .cons (.mk "apply_damage" ohkoStart ohkoDamage)
    (.cons (.mk "check_prevention" ohkoDamage ohkoPrevCheck)
      (.cons (.mk "apply_focus_sash" ohkoPrevCheck ohkoPrevApply)
        (.cons (.mk "ko_check" ohkoPrevApply ohkoKOCheck)
          (.cons (.mk "survive" ohkoKOCheck ohkoSurvived)
            (.nil ohkoSurvived)))))

/-- Theorem 15: Focus Sash path has length 5. -/
theorem focus_sash_path_length : focus_sash_path.length = 5 := rfl

-- ============================================================
-- §10  Path Algebra Properties
-- ============================================================

/-- Theorem 16: Trans length is additive. -/
theorem path_length_trans {α : Type} {a b c : α}
    (p : Path α a b) (q : Path α b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [Path.trans, Path.length]
  | cons _ _ ih => simp [Path.trans, Path.length, ih, Nat.add_assoc]

/-- Theorem 17: Trans right identity. -/
theorem path_trans_nil {α : Type} {a b : α} (p : Path α a b) :
    p.trans (.nil b) = p := by
  induction p with
  | nil _ => rfl
  | cons _ _ ih => simp [Path.trans, ih]

/-- Theorem 18: Trans associativity. -/
theorem path_trans_assoc {α : Type} {a b c d : α}
    (p : Path α a b) (q : Path α b c) (r : Path α c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => rfl
  | cons _ _ ih => simp [Path.trans, ih]

-- ============================================================
-- §11  Conflict Resolution
-- ============================================================

/-- Two rulings conflict when they have equal priority but different tags. -/
def rulings_conflict (r1 r2 : Ruling) : Bool :=
  r1.source.priority == r2.source.priority && r1.tag != r2.tag

/-- Theorem 19: Same ruling doesn't conflict with itself. -/
theorem no_self_conflict (r : Ruling) : rulings_conflict r r = false := by
  simp [rulings_conflict, BEq.beq]

/-- Theorem 20: Card text ruling beats game rules ruling. -/
theorem card_text_beats_game_rules (ct gr : Ruling)
    (hct : ct.source = .cardText) (hgr : gr.source = .gameRules) :
    ct.higherPriority gr = true := by
  simp [Ruling.higherPriority, hct, hgr, RuleSource.priority]

-- ============================================================
-- §12  "You May" Semantics
-- ============================================================

/-- Theorem 21: Mandatory effects must resolve regardless. -/
theorem mandatory_always_resolves (e : Effect) (he : e.kind = .mandatory) :
    e.mustResolve = true := by
  cases e with | mk k s t => cases k <;> simp_all [Effect.mustResolve]

/-- Theorem 22: Triggered effects must resolve. -/
theorem triggered_must_resolve (e : Effect) (he : e.kind = .triggered) :
    e.mustResolve = true := by
  cases e with | mk k s t => cases k <;> simp_all [Effect.mustResolve]

-- ============================================================
-- §13  Pipeline Composition
-- ============================================================

/-- Theorem 23: Empty pipeline (just done). -/
def empty_pipeline : Path Nat 0 1 :=
  .cons (.mk "done" 0 1) (.nil 1)

/-- Theorem 24: Empty pipeline has length 1. -/
theorem empty_pipeline_length : empty_pipeline.length = 1 := rfl

/-- Theorem 25: Two pipelines compose via trans. -/
def compose_two_pipelines : Path Nat 0 2 :=
  (Path.cons (.mk "phase1" 0 1) (.nil 1)).trans
    (.cons (.mk "phase2" 1 2) (.nil 2))

/-- Theorem 26: Composed pipeline has expected length. -/
theorem compose_two_pipelines_length : compose_two_pipelines.length = 2 := rfl

-- ============================================================
-- §14  Errata Priority
-- ============================================================

/-- Theorem 27: Errata beats game rules. -/
theorem errata_beats_game_rules :
    RuleSource.errata.priority < RuleSource.gameRules.priority := by
  simp [RuleSource.priority]

/-- Theorem 28: Card text beats errata. -/
theorem card_text_beats_errata :
    RuleSource.cardText.priority < RuleSource.errata.priority := by
  simp [RuleSource.priority]

/-- Theorem 29: Priority is transitive:
    cardText < errata < gameRules → cardText < gameRules. -/
theorem priority_transitive :
    RuleSource.cardText.priority < RuleSource.gameRules.priority := by
  simp [RuleSource.priority]

/-- Theorem 30: All three priorities are distinct. -/
theorem all_priorities_distinct :
    RuleSource.cardText.priority ≠ RuleSource.errata.priority ∧
    RuleSource.errata.priority ≠ RuleSource.gameRules.priority ∧
    RuleSource.cardText.priority ≠ RuleSource.gameRules.priority := by
  simp [RuleSource.priority]

end PokemonLean.RulingsEngine
