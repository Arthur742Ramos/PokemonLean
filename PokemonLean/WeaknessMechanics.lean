/-
  PokemonLean / WeaknessMechanics.lean

  Pokémon TCG weakness/resistance mechanics formalised in Lean 4.
  Covers: type effectiveness (2× weakness, −30 resistance),
  weakness policy item, multi-type interactions, damage calculation
  with weakness applied after base damage.

  All proofs are sorry‑free.  Uses computational paths for
  damage-calculation state transitions.
-/

namespace PokemonLean.WeaknessMechanics

-- ============================================================
-- §1  Types and effectiveness
-- ============================================================

/-- Pokémon energy / card types relevant to TCG. -/
inductive PType where
  | fire | water | grass | lightning | psychic | fighting
  | darkness | metal | dragon | fairy | normal | colorless
deriving DecidableEq, Repr

/-- Type effectiveness result. -/
inductive Effectiveness where
  | weak       -- 2× damage
  | resist     -- −30 damage
  | neutral    -- no modifier
deriving DecidableEq, Repr

/-- Core TCG weakness chart. -/
def typeChart : PType → PType → Effectiveness
  | .fire,      .water     => .weak
  | .water,     .grass     => .weak
  | .water,     .lightning => .weak
  | .grass,     .fire      => .weak
  | .lightning, .fighting  => .weak
  | .psychic,   .darkness  => .weak
  | .fighting,  .psychic   => .weak
  | .darkness,  .fighting  => .weak
  | .metal,     .fire      => .weak
  | .fairy,     .metal     => .weak
  | .fire,      .metal     => .resist
  | .grass,     .water     => .resist
  | .lightning, .metal     => .resist
  | .fighting,  .grass     => .resist
  | _,          _          => .neutral

-- ============================================================
-- §2  Damage calculation as a state machine
-- ============================================================

/-- Damage calculation phases. -/
inductive DmgPhase where
  | start | weakDone | resistDone | policyDone | complete
deriving DecidableEq, Repr

/-- Damage calculation step (computational path generator). -/
inductive DmgStep : DmgPhase × Nat → DmgPhase × Nat → Prop where
  | applyWeakness (dmg : Nat) :
      DmgStep (.start, dmg) (.weakDone, dmg * 2)
  | skipWeakness (dmg : Nat) :
      DmgStep (.start, dmg) (.weakDone, dmg)
  | applyResist (dmg : Nat) :
      DmgStep (.weakDone, dmg) (.resistDone, if dmg ≥ 30 then dmg - 30 else 0)
  | skipResist (dmg : Nat) :
      DmgStep (.weakDone, dmg) (.resistDone, dmg)
  | applyPolicy (dmg : Nat) :
      DmgStep (.resistDone, dmg) (.policyDone, dmg + 120)
  | skipPolicy (dmg : Nat) :
      DmgStep (.resistDone, dmg) (.policyDone, dmg)
  | finish (dmg : Nat) :
      DmgStep (.policyDone, dmg) (.complete, dmg)

/-- Damage calculation path (multi-step). -/
inductive DmgPath : DmgPhase × Nat → DmgPhase × Nat → Prop where
  | refl (s : DmgPhase × Nat) : DmgPath s s
  | step {s₁ s₂ s₃ : DmgPhase × Nat} :
      DmgStep s₁ s₂ → DmgPath s₂ s₃ → DmgPath s₁ s₃

-- ============================================================
-- §3  Path combinators
-- ============================================================

/-- Theorem 1: Transitivity of damage paths. -/
theorem DmgPath.trans {a b c : DmgPhase × Nat}
    (p : DmgPath a b) (q : DmgPath b c) : DmgPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact DmgPath.step s (ih q)

/-- Theorem 2: Single step as path. -/
theorem DmgPath.single {a b : DmgPhase × Nat} (s : DmgStep a b) : DmgPath a b :=
  DmgPath.step s (DmgPath.refl _)

/-- Theorem 3: Append a step. -/
theorem DmgPath.append {a b c : DmgPhase × Nat}
    (p : DmgPath a b) (s : DmgStep b c) : DmgPath a c :=
  DmgPath.trans p (DmgPath.single s)

-- ============================================================
-- §4  Weakness doubles damage
-- ============================================================

/-- Theorem 4: Weakness on 60 base yields 120. -/
theorem weakness_doubles_60 :
    DmgStep (.start, 60) (.weakDone, 120) :=
  DmgStep.applyWeakness 60

/-- Theorem 5: Weakness is exactly ×2. -/
theorem weakness_multiplier (base : Nat) :
    DmgStep (.start, base) (.weakDone, base * 2) :=
  DmgStep.applyWeakness base

/-- Theorem 6: Weakness on 0 damage is still 0. -/
theorem weakness_zero : DmgStep (.start, 0) (.weakDone, 0) := by
  have h := DmgStep.applyWeakness 0
  simp at h
  exact h

-- ============================================================
-- §5  Resistance subtracts 30
-- ============================================================

/-- Theorem 7: Resistance on 60 gives 30. -/
theorem resist_on_60 :
    DmgStep (.weakDone, 60) (.resistDone, 30) := by
  exact DmgStep.applyResist 60

/-- Theorem 8: Resistance on 20 gives 0 (floor). -/
theorem resist_floor_zero :
    DmgStep (.weakDone, 20) (.resistDone, 0) := by
  exact DmgStep.applyResist 20

-- ============================================================
-- §6  Multi-step paths: weakness then resistance
-- ============================================================

/-- Theorem 9: 60 base → weakness (120) → resistance (90). -/
theorem weakness_then_resist_60 :
    DmgPath (.start, 60) (.resistDone, 90) :=
  DmgPath.step (DmgStep.applyWeakness 60)
    (DmgPath.step (DmgStep.applyResist 120)
      (DmgPath.refl _))

/-- Theorem 10: 60 base → skip weakness (60) → resistance (30). -/
theorem neutral_then_resist_60 :
    DmgPath (.start, 60) (.resistDone, 30) :=
  DmgPath.step (DmgStep.skipWeakness 60)
    (DmgPath.step (DmgStep.applyResist 60)
      (DmgPath.refl _))

-- ============================================================
-- §7  Weakness Policy item
-- ============================================================

/-- Theorem 11: Full path with Weakness Policy:
    60 base → weakness (120) → skip resist (120) → policy (+120 = 240) → finish. -/
theorem weakness_policy_full :
    DmgPath (.start, 60) (.complete, 240) :=
  DmgPath.step (DmgStep.applyWeakness 60)
    (DmgPath.step (DmgStep.skipResist 120)
      (DmgPath.step (DmgStep.applyPolicy 120)
        (DmgPath.step (DmgStep.finish 240)
          (DmgPath.refl _))))

/-- Theorem 12: Policy adds exactly 120. -/
theorem policy_adds_120 (dmg : Nat) :
    DmgStep (.resistDone, dmg) (.policyDone, dmg + 120) :=
  DmgStep.applyPolicy dmg

-- ============================================================
-- §8  Full damage calculation paths
-- ============================================================

/-- Theorem 13: Neutral matchup — 60 base passes through unchanged. -/
theorem neutral_full_60 :
    DmgPath (.start, 60) (.complete, 60) :=
  DmgPath.step (DmgStep.skipWeakness 60)
    (DmgPath.step (DmgStep.skipResist 60)
      (DmgPath.step (DmgStep.skipPolicy 60)
        (DmgPath.step (DmgStep.finish 60)
          (DmgPath.refl _))))

/-- Theorem 14: Weakness-only matchup — 60 → 120 complete. -/
theorem weakness_only_60 :
    DmgPath (.start, 60) (.complete, 120) :=
  DmgPath.step (DmgStep.applyWeakness 60)
    (DmgPath.step (DmgStep.skipResist 120)
      (DmgPath.step (DmgStep.skipPolicy 120)
        (DmgPath.step (DmgStep.finish 120)
          (DmgPath.refl _))))

-- ============================================================
-- §9  Multi-type interactions
-- ============================================================

/-- Combined damage modifier for dual type. -/
def dualTypeDamage (base : Nat) (e1 e2 : Effectiveness) : Nat :=
  let after1 := match e1 with
    | .weak => base * 2
    | .resist => if base ≥ 30 then base - 30 else 0
    | .neutral => base
  match e2 with
    | .weak => after1 * 2
    | .resist => if after1 ≥ 30 then after1 - 30 else 0
    | .neutral => after1

/-- Theorem 15: Double weakness = ×4. -/
theorem double_weakness_x4 (base : Nat) :
    dualTypeDamage base .weak .weak = base * 4 := by
  simp [dualTypeDamage, Nat.mul_assoc]

/-- Theorem 16: Double neutral = base. -/
theorem double_neutral (base : Nat) :
    dualTypeDamage base .neutral .neutral = base := by
  simp [dualTypeDamage]

/-- Theorem 17: Weak + resist on 60 = 90. -/
theorem weak_resist_60 :
    dualTypeDamage 60 .weak .resist = 90 := by rfl

/-- Theorem 18: Double resist on 60 = 0. -/
theorem double_resist_60 :
    dualTypeDamage 60 .resist .resist = 0 := by rfl

-- ============================================================
-- §10  Type chart properties
-- ============================================================

/-- Theorem 19: Fire is weak to Water. -/
theorem fire_weak_to_water : typeChart .fire .water = .weak := rfl

/-- Theorem 20: Grass resists Water attacks. -/
theorem grass_resist_water : typeChart .grass .water = .resist := rfl

/-- Theorem 21: Water is weak to Grass. -/
theorem water_weak_to_grass : typeChart .water .grass = .weak := rfl

/-- Theorem 22: Colorless is neutral to everything. -/
theorem colorless_neutral (t : PType) : typeChart .colorless t = .neutral := by
  cases t <;> rfl

/-- Theorem 23: Dragon is neutral defensively. -/
theorem dragon_neutral_def (t : PType) : typeChart .dragon t = .neutral := by
  cases t <;> rfl

end PokemonLean.WeaknessMechanics
