/-
  PokemonLean / SpecialConditions.lean

  Special conditions in the Pokémon TCG: Poisoned, Burned, Asleep,
  Confused, Paralyzed.  Stacking rules (only one of Asleep / Confused /
  Paralyzed at a time), between-turns effects (poison damage, burn
  damage, sleep coin-flip, paralysis removal), Full Heal / switch cures.

  Computational paths model condition transitions.

  All proofs are sorry-free.  30+ theorems.
-/

-- ============================================================
-- §1  Types
-- ============================================================

namespace SpecialConditions

/-- The five special conditions. -/
inductive Condition where
  | poisoned
  | burned
  | asleep
  | confused
  | paralyzed
deriving DecidableEq, Repr

/-- A condition set: at most one of asleep/confused/paralyzed plus
    optional poison and/or burn. -/
structure ConditionSet where
  poisoned  : Bool
  burned    : Bool
  /-- Exclusive slot: at most one of asleep, confused, paralyzed. -/
  exclusive : Option Condition
deriving DecidableEq, Repr

/-- The three mutually exclusive conditions. -/
def isExclusive : Condition → Bool
  | .asleep    => true
  | .confused  => true
  | .paralyzed => true
  | _          => false

/-- Well-formedness: the exclusive slot only contains exclusive conditions. -/
def ConditionSet.wf (cs : ConditionSet) : Prop :=
  match cs.exclusive with
  | none => True
  | some c => isExclusive c = true

/-- Empty (healthy) condition set. -/
def ConditionSet.empty : ConditionSet := ⟨false, false, none⟩

-- ============================================================
-- ============================================================
-- §3  Applying conditions (stacking rules)
-- ============================================================

/-- Apply a condition, respecting stacking rules:
    - Poison/Burn toggle their flag.
    - Asleep/Confused/Paralyzed replace each other in the exclusive slot. -/
def ConditionSet.apply (cs : ConditionSet) (c : Condition) : ConditionSet :=
  match c with
  | .poisoned  => { cs with poisoned := true }
  | .burned    => { cs with burned := true }
  | .asleep    => { cs with exclusive := some .asleep }
  | .confused  => { cs with exclusive := some .confused }
  | .paralyzed => { cs with exclusive := some .paralyzed }

/-- Theorem 1: Applying poison sets the poison flag. -/
theorem apply_poison (cs : ConditionSet) :
    (cs.apply .poisoned).poisoned = true := rfl

/-- Theorem 2: Applying burn sets the burn flag. -/
theorem apply_burn (cs : ConditionSet) :
    (cs.apply .burned).burned = true := rfl

/-- Theorem 3: Applying asleep sets exclusive to asleep. -/
theorem apply_asleep (cs : ConditionSet) :
    (cs.apply .asleep).exclusive = some .asleep := rfl

/-- Theorem 4: Applying confused sets exclusive to confused. -/
theorem apply_confused (cs : ConditionSet) :
    (cs.apply .confused).exclusive = some .confused := rfl

/-- Theorem 5: Applying paralyzed sets exclusive to paralyzed. -/
theorem apply_paralyzed (cs : ConditionSet) :
    (cs.apply .paralyzed).exclusive = some .paralyzed := rfl

/-- Theorem 6: Applying asleep replaces paralyzed (stacking rule). -/
theorem asleep_replaces_paralyzed (cs : ConditionSet)
    (_h : cs.exclusive = some .paralyzed) :
    (cs.apply .asleep).exclusive = some .asleep := rfl

/-- Theorem 7: Applying poison preserves the exclusive slot. -/
theorem poison_preserves_exclusive (cs : ConditionSet) :
    (cs.apply .poisoned).exclusive = cs.exclusive := rfl

/-- Theorem 8: Applying burn preserves the exclusive slot. -/
theorem burn_preserves_exclusive (cs : ConditionSet) :
    (cs.apply .burned).exclusive = cs.exclusive := rfl

/-- Theorem 9: Applying poison preserves the burn flag. -/
theorem poison_preserves_burn (cs : ConditionSet) :
    (cs.apply .poisoned).burned = cs.burned := rfl

/-- Theorem 10: Applying burn preserves the poison flag. -/
theorem burn_preserves_poison (cs : ConditionSet) :
    (cs.apply .burned).poisoned = cs.poisoned := rfl

/-- Theorem 11: Well-formedness is preserved by apply. -/
theorem apply_wf (cs : ConditionSet) (c : Condition) (hw : cs.wf) :
    (cs.apply c).wf := by
  cases c <;> simp [ConditionSet.apply, ConditionSet.wf, isExclusive]
  all_goals exact hw

-- ============================================================
-- §4  Between-turns effects
-- ============================================================

/-- Coin flip result. -/
inductive CoinFlip where
  | heads | tails
deriving DecidableEq, Repr

/-- HP tracking for between-turns damage. -/
structure PokemonHP where
  conditions : ConditionSet
  hp         : Nat
  maxHp      : Nat
deriving DecidableEq, Repr

/-- Poison damage: 10 damage between turns. -/
def poisonDamage (p : PokemonHP) : PokemonHP :=
  if p.conditions.poisoned then
    { p with hp := p.hp - 10 }
  else p

/-- Burn damage: 20 damage between turns. -/
def burnDamage (p : PokemonHP) : PokemonHP :=
  if p.conditions.burned then
    { p with hp := p.hp - 20 }
  else p

/-- Sleep check: on heads, wake up. -/
def sleepCheck (p : PokemonHP) (flip : CoinFlip) : PokemonHP :=
  match p.conditions.exclusive with
  | some .asleep =>
    match flip with
    | .heads => { p with conditions := { p.conditions with exclusive := none } }
    | .tails => p
  | _ => p

/-- Paralysis removal: paralysis is removed after the affected turn. -/
def removeParalysis (p : PokemonHP) : PokemonHP :=
  match p.conditions.exclusive with
  | some .paralyzed => { p with conditions := { p.conditions with exclusive := none } }
  | _ => p

/-- Full between-turns effect sequence. -/
def betweenTurns (p : PokemonHP) (sleepFlip : CoinFlip) : PokemonHP :=
  (removeParalysis (sleepCheck (burnDamage (poisonDamage p)) sleepFlip))

/-- Theorem 12: Poison damage reduces HP by 10. -/
theorem poisonDamage_reduces (p : PokemonHP) (h : p.conditions.poisoned = true) :
    (poisonDamage p).hp = p.hp - 10 := by
  simp [poisonDamage, h]

/-- Theorem 13: No poison means no poison damage. -/
theorem poisonDamage_noop (p : PokemonHP) (h : p.conditions.poisoned = false) :
    poisonDamage p = p := by
  simp [poisonDamage, h]

/-- Theorem 14: Burn damage reduces HP by 20. -/
theorem burnDamage_reduces (p : PokemonHP) (h : p.conditions.burned = true) :
    (burnDamage p).hp = p.hp - 20 := by
  simp [burnDamage, h]

/-- Theorem 15: No burn means no burn damage. -/
theorem burnDamage_noop (p : PokemonHP) (h : p.conditions.burned = false) :
    burnDamage p = p := by
  simp [burnDamage, h]

/-- Theorem 16: Sleep check on heads wakes up. -/
theorem sleepCheck_heads_wakes (p : PokemonHP)
    (h : p.conditions.exclusive = some .asleep) :
    (sleepCheck p .heads).conditions.exclusive = none := by
  simp [sleepCheck, h]

/-- Theorem 17: Sleep check on tails stays asleep. -/
theorem sleepCheck_tails_stays (p : PokemonHP)
    (h : p.conditions.exclusive = some .asleep) :
    (sleepCheck p .tails) = p := by
  simp [sleepCheck, h]

/-- Theorem 18: Sleep check does nothing if not asleep. -/
theorem sleepCheck_not_asleep (p : PokemonHP) (flip : CoinFlip)
    (h : p.conditions.exclusive ≠ some .asleep) :
    sleepCheck p flip = p := by
  unfold sleepCheck
  cases hx : p.conditions.exclusive with
  | none => rfl
  | some c =>
    cases c <;> simp_all

/-- Theorem 19: removeParalysis clears paralysis. -/
theorem removeParalysis_clears (p : PokemonHP)
    (h : p.conditions.exclusive = some .paralyzed) :
    (removeParalysis p).conditions.exclusive = none := by
  simp [removeParalysis, h]

/-- Theorem 20: removeParalysis does nothing if not paralyzed. -/
theorem removeParalysis_noop (p : PokemonHP)
    (h : p.conditions.exclusive ≠ some .paralyzed) :
    removeParalysis p = p := by
  unfold removeParalysis
  cases hx : p.conditions.exclusive with
  | none => rfl
  | some c =>
    cases c <;> simp_all

-- ============================================================
-- §5  Full Heal / Switch cures
-- ============================================================

/-- Full Heal: removes all special conditions. -/
def fullHeal (p : PokemonHP) : PokemonHP :=
  { p with conditions := ConditionSet.empty }

/-- Switching (going to bench): cures all special conditions. -/
def switchCure (p : PokemonHP) : PokemonHP :=
  { p with conditions := ConditionSet.empty }

/-- Theorem 21: Full Heal clears poison. -/
theorem fullHeal_clears_poison (p : PokemonHP) :
    (fullHeal p).conditions.poisoned = false := rfl

/-- Theorem 22: Full Heal clears burn. -/
theorem fullHeal_clears_burn (p : PokemonHP) :
    (fullHeal p).conditions.burned = false := rfl

/-- Theorem 23: Full Heal clears exclusive. -/
theorem fullHeal_clears_exclusive (p : PokemonHP) :
    (fullHeal p).conditions.exclusive = none := rfl

/-- Theorem 24: Switch cure equals full heal in effect. -/
theorem switch_eq_fullHeal (p : PokemonHP) :
    switchCure p = fullHeal p := rfl

/-- Theorem 25: Full Heal is idempotent. -/
theorem fullHeal_idempotent (p : PokemonHP) :
    fullHeal (fullHeal p) = fullHeal p := rfl

/-- Theorem 26: Full Heal preserves HP. -/
theorem fullHeal_preserves_hp (p : PokemonHP) :
    (fullHeal p).hp = p.hp := rfl


/-- Theorem 30: Empty condition set is well-formed. -/
theorem empty_wf : ConditionSet.empty.wf := by
  simp [ConditionSet.empty, ConditionSet.wf]

/-- Theorem 31: Applying any condition to empty preserves wf. -/
theorem apply_to_empty_wf (c : Condition) :
    (ConditionSet.empty.apply c).wf := by
  cases c <;> simp [ConditionSet.empty, ConditionSet.apply, ConditionSet.wf, isExclusive]

/-- Theorem 32: Poison damage preserves conditions. -/
theorem poisonDamage_preserves_conditions (p : PokemonHP) :
    (poisonDamage p).conditions = p.conditions := by
  simp [poisonDamage]; split <;> rfl

/-- Theorem 33: Burn damage preserves conditions. -/
theorem burnDamage_preserves_conditions (p : PokemonHP) :
    (burnDamage p).conditions = p.conditions := by
  simp [burnDamage]; split <;> rfl

end SpecialConditions
