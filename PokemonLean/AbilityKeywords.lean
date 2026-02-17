/-
  PokemonLean / AbilityKeywords.lean

  Ability keywords for the Pokémon TCG formalised with computational paths.
  Covers: Rush In (free switch-in), Safeguard (prevent effects),
  Intimidate (reduce damage), Adaptive Evolution (type change),
  Ditto's Transform, Unaware (ignore stat changes),
  ability interaction priority.

  All proofs are sorry-free. 20+ theorems using computational paths.
-/

namespace PokemonLean.AbilityKeywords

-- ============================================================
-- §1  Core types
-- ============================================================

inductive PType where
  | fire | water | grass | electric | psychic | fighting
  | dark | metal | dragon | fairy | normal | ice | flying
  | poison | ground | rock | bug | ghost | steel
  deriving DecidableEq, Repr

inductive CardKind where
  | basic | stage1 | stage2 | ex | gx | vstar | vmax | ruleBox
  deriving DecidableEq, Repr

def CardKind.isRuleBox : CardKind → Bool
  | .ex | .gx | .vstar | .vmax | .ruleBox => true
  | _ => false

-- ============================================================
-- §2  Ability keywords
-- ============================================================

inductive AbilityKeyword where
  | rushIn            -- Free switch-in from bench to active
  | safeguard         -- Prevent all effects of attacks from certain Pokémon
  | intimidate        -- On entry: reduce opponent's attack damage
  | adaptiveEvolution -- Change this Pokémon's type
  | transform         -- Ditto: copy opponent's Pokémon
  | unaware           -- Ignore opponent's stat changes
  | shieldDust        -- Prevent additional effects of attacks
  | moldBreaker       -- Ignore opponent's abilities when attacking
  | regenerator       -- Heal when retreating to bench
  | prankster         -- Trainer cards have priority
  | noAbility
  deriving DecidableEq, Repr

/-- Priority tier for ability resolution order. -/
inductive PriorityTier where
  | immediate    -- Resolves as soon as the Pokémon enters play (Rush In)
  | onEntry      -- Resolves after entering (Intimidate)
  | passive      -- Always active (Safeguard, Unaware)
  | triggered    -- Resolves on specific conditions (Regenerator)
  | overriding   -- Overrides other abilities (Mold Breaker)
  deriving DecidableEq, Repr

def abilityPriority : AbilityKeyword → PriorityTier
  | .rushIn            => .immediate
  | .intimidate        => .onEntry
  | .safeguard         => .passive
  | .adaptiveEvolution => .triggered
  | .transform         => .onEntry
  | .unaware           => .passive
  | .shieldDust        => .passive
  | .moldBreaker       => .overriding
  | .regenerator       => .triggered
  | .prankster         => .passive
  | .noAbility         => .passive

/-- Numeric priority for ordering. -/
def PriorityTier.toNat : PriorityTier → Nat
  | .overriding => 4
  | .immediate  => 3
  | .onEntry    => 2
  | .passive    => 1
  | .triggered  => 0

-- ============================================================
-- §3  Pokémon and game state
-- ============================================================

structure Pokemon where
  name     : String
  kind     : CardKind
  ptype    : PType
  ability  : AbilityKeyword
  hp       : Nat
  maxHp    : Nat
  damage   : Nat
  atkBoost : Int     -- stat change to attack
  isActive : Bool
  deriving DecidableEq, Repr

structure GameState where
  playerActive   : Pokemon
  opponentActive : Pokemon
  playerBench    : List Pokemon
  opponentBench  : List Pokemon
  damageReduction : Int
  moldBreakerActive : Bool
  deriving Repr

-- ============================================================
-- §4  Computational paths
-- ============================================================

inductive Step : GameState → GameState → Type where
  | refl : (gs : GameState) → Step gs gs
  | rule : (name : String) → (a b : GameState) → Step a b

inductive Path : GameState → GameState → Type where
  | nil  : (gs : GameState) → Path gs gs
  | cons : Step a b → Path b c → Path a c

def Path.trans : Path a b → Path b c → Path a c
  | Path.nil _, q => q
  | Path.cons s p, q => Path.cons s (Path.trans p q)

def Step.symm : Step a b → Step b a
  | Step.refl gs => Step.refl gs
  | Step.rule name a b => Step.rule (name ++ "⁻¹") b a

def Path.symm : Path a b → Path b a
  | Path.nil gs => Path.nil gs
  | Path.cons s p => Path.trans (Path.symm p) (Path.cons (Step.symm s) (Path.nil _))

def Path.single (s : Step a b) : Path a b :=
  Path.cons s (Path.nil _)

def Path.length : Path a b → Nat
  | Path.nil _ => 0
  | Path.cons _ p => 1 + Path.length p

-- ============================================================
-- §5  Ability activation predicates
-- ============================================================

def canActivate (gs : GameState) (p : Pokemon) : Bool :=
  if gs.moldBreakerActive then
    p.ability == .moldBreaker
  else
    true

/-- Is the ability a passive ability? -/
def isPassive (ak : AbilityKeyword) : Bool :=
  match abilityPriority ak with
  | .passive => true
  | _ => false

-- ============================================================
-- §6  Rush In — free switch-in
-- ============================================================

def applyRushIn (gs : GameState) (benchIdx : Nat) : Option GameState :=
  match gs.playerBench[benchIdx]? with
  | some benchMon =>
    if benchMon.ability == .rushIn then
      some {
        gs with
        playerActive := { benchMon with isActive := true }
        playerBench := { gs.playerActive with isActive := false } ::
          gs.playerBench.eraseIdx benchIdx
      }
    else none
  | none => none

-- 1: Rush In has immediate priority
theorem rushIn_is_immediate :
    abilityPriority .rushIn = .immediate := rfl

-- 2: Rush In priority is highest non-overriding
theorem rushIn_priority_value :
    PriorityTier.toNat (abilityPriority .rushIn) = 3 := rfl

-- 3: Rush In produces a valid switch when bench mon has ability
theorem rushIn_valid_switch (gs : GameState) (idx : Nat)
    (mon : Pokemon)
    (hget : gs.playerBench[idx]? = some mon)
    (hab : mon.ability = .rushIn) :
    (applyRushIn gs idx).isSome = true := by
  simp [applyRushIn, hget, hab]

-- ============================================================
-- §7  Safeguard — prevent effects
-- ============================================================

def hasSafeguard (p : Pokemon) : Bool :=
  p.ability == .safeguard

def safeguardBlocks (attacker defender : Pokemon) : Bool :=
  hasSafeguard defender && attacker.kind.isRuleBox

-- 4: Safeguard blocks Rule Box attackers
theorem safeguard_blocks_ruleBox (attacker defender : Pokemon)
    (hsafe : defender.ability = .safeguard)
    (hrb : attacker.kind.isRuleBox = true) :
    safeguardBlocks attacker defender = true := by
  simp [safeguardBlocks, hasSafeguard, hsafe, hrb]

-- 5: Safeguard does NOT block non-Rule Box
theorem safeguard_allows_basic (attacker defender : Pokemon)
    (hsafe : defender.ability = .safeguard)
    (hnrb : attacker.kind.isRuleBox = false) :
    safeguardBlocks attacker defender = false := by
  simp [safeguardBlocks, hasSafeguard, hsafe, hnrb]

-- 6: Safeguard is passive
theorem safeguard_is_passive :
    abilityPriority .safeguard = .passive := rfl

-- ============================================================
-- §8  Intimidate — reduce damage
-- ============================================================

def applyIntimidate (gs : GameState) (amount : Int) : GameState :=
  if gs.playerActive.ability == .intimidate && !gs.moldBreakerActive then
    { gs with damageReduction := gs.damageReduction + amount }
  else gs

-- 7: Intimidate reduces damage when active and no mold breaker
theorem intimidate_reduces (gs : GameState) (amount : Int)
    (hab : gs.playerActive.ability = .intimidate)
    (hnmb : gs.moldBreakerActive = false) :
    (applyIntimidate gs amount).damageReduction = gs.damageReduction + amount := by
  simp [applyIntimidate, hab, hnmb]

-- 8: Intimidate blocked by Mold Breaker
theorem intimidate_blocked_by_moldbreaker (gs : GameState) (amount : Int)
    (hab : gs.playerActive.ability = .intimidate)
    (hmb : gs.moldBreakerActive = true) :
    (applyIntimidate gs amount).damageReduction = gs.damageReduction := by
  simp [applyIntimidate, hab, hmb]

-- 9: Intimidate is onEntry
theorem intimidate_is_onEntry :
    abilityPriority .intimidate = .onEntry := rfl

-- ============================================================
-- §9  Adaptive Evolution — type change
-- ============================================================

def applyAdaptiveEvolution (gs : GameState) (newType : PType) : GameState :=
  if gs.playerActive.ability == .adaptiveEvolution then
    { gs with playerActive := { gs.playerActive with ptype := newType } }
  else gs

-- 10: Adaptive Evolution changes type
theorem adaptive_evolution_changes_type (gs : GameState) (newType : PType)
    (hab : gs.playerActive.ability = .adaptiveEvolution) :
    (applyAdaptiveEvolution gs newType).playerActive.ptype = newType := by
  simp [applyAdaptiveEvolution, hab]

-- 11: Adaptive Evolution is triggered
theorem adaptive_evolution_is_triggered :
    abilityPriority .adaptiveEvolution = .triggered := rfl

-- ============================================================
-- §10  Ditto's Transform
-- ============================================================

def applyTransform (gs : GameState) : GameState :=
  if gs.playerActive.ability == .transform then
    { gs with playerActive := {
        gs.playerActive with
        ptype := gs.opponentActive.ptype
        atkBoost := gs.opponentActive.atkBoost
      }
    }
  else gs

-- 12: Transform copies opponent's type
theorem transform_copies_type (gs : GameState)
    (hab : gs.playerActive.ability = .transform) :
    (applyTransform gs).playerActive.ptype = gs.opponentActive.ptype := by
  simp [applyTransform, hab]

-- 13: Transform copies opponent's atkBoost
theorem transform_copies_boost (gs : GameState)
    (hab : gs.playerActive.ability = .transform) :
    (applyTransform gs).playerActive.atkBoost = gs.opponentActive.atkBoost := by
  simp [applyTransform, hab]

-- 14: Transform preserves HP
theorem transform_preserves_hp (gs : GameState)
    (hab : gs.playerActive.ability = .transform) :
    (applyTransform gs).playerActive.hp = gs.playerActive.hp := by
  simp [applyTransform, hab]

-- ============================================================
-- §11  Unaware — ignore stat changes
-- ============================================================

def effectiveDamage (baseDmg : Nat) (atkBoost : Int) (ignoreStats : Bool) : Nat :=
  if ignoreStats then baseDmg
  else if atkBoost ≥ 0 then baseDmg + atkBoost.toNat
  else baseDmg - (-atkBoost).toNat

def calcDamageWithUnaware (gs : GameState) (baseDmg : Nat) : Nat :=
  let ignoreStats := gs.opponentActive.ability == .unaware
  effectiveDamage baseDmg gs.playerActive.atkBoost ignoreStats

-- 15: Unaware ignores attack boosts
theorem unaware_ignores_boosts (gs : GameState) (baseDmg : Nat)
    (hunaware : gs.opponentActive.ability = .unaware) :
    calcDamageWithUnaware gs baseDmg = baseDmg := by
  simp [calcDamageWithUnaware, effectiveDamage, hunaware]

-- 16: Without Unaware, positive boost increases damage
theorem no_unaware_boost_applies (gs : GameState) (baseDmg : Nat)
    (hnotUnaware : gs.opponentActive.ability ≠ .unaware)
    (hpos : gs.playerActive.atkBoost ≥ 0) :
    calcDamageWithUnaware gs baseDmg =
      baseDmg + gs.playerActive.atkBoost.toNat := by
  simp [calcDamageWithUnaware, effectiveDamage]
  split
  · next h => exact absurd h hnotUnaware
  · simp [hpos]

-- 17: Unaware is passive
theorem unaware_is_passive :
    abilityPriority .unaware = .passive := rfl

-- ============================================================
-- §12  Ability interaction priority
-- ============================================================

def higherPriority (a b : AbilityKeyword) : Bool :=
  PriorityTier.toNat (abilityPriority a) > PriorityTier.toNat (abilityPriority b)

-- 18: Mold Breaker has highest priority
theorem moldBreaker_highest_vs_safeguard :
    higherPriority .moldBreaker .safeguard = true := rfl

-- 19: Rush In resolves before Intimidate
theorem rushIn_before_intimidate :
    higherPriority .rushIn .intimidate = true := rfl

-- 20: Overriding > Immediate
theorem overriding_gt_immediate :
    PriorityTier.toNat .overriding > PriorityTier.toNat .immediate := by
  decide

-- ============================================================
-- §13  Ability path compositions
-- ============================================================

-- 21: trans_nil
theorem path_trans_nil (p : Path a b) :
    Path.trans p (Path.nil b) = p := by
  induction p with
  | nil _ => rfl
  | cons s _ ih => simp [Path.trans, ih]

-- 22: trans_assoc
theorem path_trans_assoc (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  induction p with
  | nil _ => simp [Path.trans]
  | cons s _ ih => simp [Path.trans, ih]

-- 23: Single step has length 1
theorem path_single_length (s : Step a b) :
    Path.length (Path.single s) = 1 := by
  simp [Path.single, Path.length]

-- 24: Intimidate + Rush In composition path
def intimidate_rushIn_sequence (gs : GameState)
    (gs' : GameState) (gs'' : GameState) :
    Path gs gs' → Path gs' gs'' → Path gs gs'' :=
  Path.trans

-- 25: Shield Dust is passive
theorem shieldDust_is_passive :
    abilityPriority .shieldDust = .passive := rfl

-- 26: Regenerator is triggered
theorem regenerator_is_triggered :
    abilityPriority .regenerator = .triggered := rfl

-- 27: No ability is passive (default)
theorem noAbility_is_passive :
    abilityPriority .noAbility = .passive := rfl

-- ============================================================
-- §14  Mold Breaker interaction
-- ============================================================

def moldBreakerBypass (gs : GameState) : GameState :=
  if gs.playerActive.ability == .moldBreaker then
    { gs with moldBreakerActive := true }
  else gs

-- 28: Mold Breaker activates the bypass flag
theorem moldBreaker_activates (gs : GameState)
    (hab : gs.playerActive.ability = .moldBreaker) :
    (moldBreakerBypass gs).moldBreakerActive = true := by
  simp [moldBreakerBypass, hab]

-- 29: Without Mold Breaker, bypass stays unchanged
theorem no_moldBreaker_unchanged (gs : GameState)
    (hab : gs.playerActive.ability ≠ .moldBreaker) :
    (moldBreakerBypass gs).moldBreakerActive = gs.moldBreakerActive := by
  simp [moldBreakerBypass]
  split
  · next h => exact absurd h hab
  · rfl

-- 30: Mold Breaker overrides Safeguard (priority ordering)
theorem moldBreaker_overrides_safeguard :
    higherPriority .moldBreaker .safeguard = true := rfl

end PokemonLean.AbilityKeywords
