/-
  PokemonLean / TerastalMechanics.lean

  Terastallization mechanics from Pokémon Scarlet/Violet formalised
  using computational paths.  Covers: Tera type change, Tera orb
  charge/use cycle, once-per-battle constraint, STAB bonus with
  Tera type, Stellar type (boosts all moves once), Tera Blast type
  change, defensive type override.

  All proofs are sorry‑free.  22 theorems.
-/

namespace PokemonLean.TerastalMechanics

-- ============================================================
-- §1  Types
-- ============================================================

inductive PType where
  | normal | fire | water | grass | electric | ice
  | fighting | poison | ground | flying | psychic
  | bug | rock | ghost | dragon | dark | steel | fairy
  | stellar
deriving DecidableEq, Repr

-- ============================================================
-- §2  Tera Orb State Machine
-- ============================================================

inductive OrbState where
  | charged | depleted
deriving DecidableEq, Repr

inductive TeraState where
  | notTera | terastallized
deriving DecidableEq, Repr

structure BattleState where
  orbState  : OrbState
  teraState : TeraState
  teraType  : PType
  origTypes : List PType
deriving DecidableEq, Repr

-- ============================================================
-- §3  Tera Step (computational path generator)
-- ============================================================

inductive TeraStep : BattleState → BattleState → Prop where
  | terastallize (orb : OrbState) (ts : TeraState) (tt : PType) (ots : List PType)
      (hcharged : orb = .charged) (hnotTera : ts = .notTera) :
      TeraStep ⟨orb, ts, tt, ots⟩ ⟨.depleted, .terastallized, tt, ots⟩
  | rechargeOrb (ts : TeraState) (tt : PType) (ots : List PType) :
      TeraStep ⟨.depleted, ts, tt, ots⟩ ⟨.charged, ts, tt, ots⟩

inductive TeraPath : BattleState → BattleState → Prop where
  | refl (s : BattleState) : TeraPath s s
  | step {a b c : BattleState} : TeraStep a b → TeraPath b c → TeraPath a c

-- ============================================================
-- §4  Path combinators
-- ============================================================

/-- Theorem 1: Transitivity of Tera paths. -/
theorem TeraPath.trans {a b c : BattleState}
    (p : TeraPath a b) (q : TeraPath b c) : TeraPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact TeraPath.step s (ih q)

/-- Theorem 2: Single step as path. -/
theorem TeraPath.single {a b : BattleState}
    (s : TeraStep a b) : TeraPath a b :=
  TeraPath.step s (TeraPath.refl _)

/-- Theorem 3: Append a step. -/
theorem TeraPath.append {a b c : BattleState}
    (p : TeraPath a b) (s : TeraStep b c) : TeraPath a c :=
  TeraPath.trans p (TeraPath.single s)

-- ============================================================
-- §5  Once-per-battle
-- ============================================================

/-- Theorem 4: Terastallization sets state to terastallized. -/
theorem tera_sets_state (tt : PType) (ots : List PType) :
    TeraStep ⟨.charged, .notTera, tt, ots⟩ ⟨.depleted, .terastallized, tt, ots⟩ :=
  TeraStep.terastallize .charged .notTera tt ots rfl rfl

/-- Theorem 5: Cannot Terastallize when already Terastallized. -/
theorem no_double_tera (b : BattleState) (tt : PType) (ots : List PType)
    (step : TeraStep ⟨.charged, .terastallized, tt, ots⟩ b) :
    b.teraState = .terastallized := by
  cases step with
  | terastallize _ _ _ _ _ hnt => simp at hnt

/-- Theorem 6: Cannot Terastallize with depleted orb. -/
theorem no_tera_depleted (b : BattleState) (tt : PType) (ots : List PType)
    (step : TeraStep ⟨.depleted, .notTera, tt, ots⟩ b) :
    b.orbState = .charged := by
  cases step with
  | terastallize _ _ _ _ hc _ => simp at hc
  | rechargeOrb => rfl

-- ============================================================
-- §6  Tera Orb Charge-Use Cycle
-- ============================================================

/-- Theorem 7: Full cycle: charged → tera → recharge. -/
theorem tera_cycle (tt : PType) (ots : List PType) :
    TeraPath ⟨.charged, .notTera, tt, ots⟩ ⟨.charged, .terastallized, tt, ots⟩ :=
  TeraPath.step (TeraStep.terastallize .charged .notTera tt ots rfl rfl)
    (TeraPath.step (TeraStep.rechargeOrb .terastallized tt ots)
      (TeraPath.refl _))

-- ============================================================
-- §7  STAB Bonus with Tera Type
-- ============================================================

/-- STAB multiplier × 10: 20 = 2.0×, 15 = 1.5×, 10 = 1.0×. -/
def stabMultiplier (moveType : PType) (origTypes : List PType)
    (teraType : PType) (isTera : Bool) : Nat :=
  if isTera then
    if moveType = teraType && moveType ∈ origTypes then 20
    else if moveType = teraType then 15
    else if moveType ∈ origTypes then 15
    else 10
  else
    if moveType ∈ origTypes then 15
    else 10

/-- Theorem 8: Tera type matching original type gives 2.0× STAB. -/
theorem tera_double_stab (mt : PType) (origs : List PType)
    (hmem : mt ∈ origs) :
    stabMultiplier mt origs mt true = 20 := by
  simp [stabMultiplier, hmem]

/-- Theorem 9: Tera type not matching original gives 1.5× STAB. -/
theorem tera_new_stab (mt : PType) (origs : List PType)
    (hnotmem : mt ∉ origs) :
    stabMultiplier mt origs mt true = 15 := by
  simp [stabMultiplier, hnotmem]

/-- Theorem 10: Non-Tera original STAB gives 1.5×. -/
theorem normal_stab (mt : PType) (origs : List PType) (teraT : PType)
    (hmem : mt ∈ origs) :
    stabMultiplier mt origs teraT false = 15 := by
  simp [stabMultiplier, hmem]

/-- Theorem 11: Non-Tera no STAB gives 1.0×. -/
theorem no_stab (mt : PType) (origs : List PType) (teraT : PType)
    (hnotmem : mt ∉ origs) :
    stabMultiplier mt origs teraT false = 10 := by
  simp [stabMultiplier, hnotmem]

-- ============================================================
-- §8  Stellar Type
-- ============================================================

structure StellarState where
  boostedTypes : List PType
deriving DecidableEq, Repr

inductive StellarStep : StellarState → PType → StellarState → Prop where
  | boost (ss : StellarState) (mt : PType)
      (hnotUsed : mt ∉ ss.boostedTypes) :
      StellarStep ss mt ⟨mt :: ss.boostedTypes⟩

inductive StellarPath : StellarState → StellarState → Prop where
  | refl (ss : StellarState) : StellarPath ss ss
  | step {a b c : StellarState} (mt : PType) :
      StellarStep a mt b → StellarPath b c → StellarPath a c

/-- Theorem 12: Stellar path transitivity. -/
theorem StellarPath.trans {a b c : StellarState}
    (p : StellarPath a b) (q : StellarPath b c) : StellarPath a c := by
  induction p with
  | refl _ => exact q
  | step mt s _ ih => exact StellarPath.step mt s (ih q)

/-- Theorem 13: After Stellar boost, the type is recorded. -/
theorem stellar_boost_recorded (ss : StellarState) (mt : PType)
    (_ : mt ∉ ss.boostedTypes) :
    mt ∈ (⟨mt :: ss.boostedTypes⟩ : StellarState).boostedTypes := by
  simp

/-- Theorem 14: Cannot boost same type twice. -/
theorem stellar_no_double_boost (ss : StellarState) (mt : PType)
    (hUsed : mt ∈ ss.boostedTypes) (ss' : StellarState)
    (step : StellarStep ss mt ss') : False := by
  cases step
  contradiction

-- ============================================================
-- §9  Tera Blast Type Change
-- ============================================================

def teraBlastType (isTera : Bool) (teraType : PType) : PType :=
  if isTera then teraType else PType.normal

/-- Theorem 15: Tera Blast is Normal when not Terastallized. -/
theorem teraBlast_normal_when_not_tera :
    teraBlastType false PType.fire = PType.normal := rfl

/-- Theorem 16: Tera Blast matches Tera type when Terastallized. -/
theorem teraBlast_matches_tera (tt : PType) :
    teraBlastType true tt = tt := by
  simp [teraBlastType]

-- ============================================================
-- §10  Defensive Type Override
-- ============================================================

def defensiveTypes (isTera : Bool) (teraType : PType) (origTypes : List PType) : List PType :=
  if isTera then [teraType] else origTypes

/-- Theorem 17: Terastallized → defensive type is Tera type. -/
theorem tera_defensive_override (tt : PType) (origs : List PType) :
    defensiveTypes true tt origs = [tt] := by
  simp [defensiveTypes]

/-- Theorem 18: Not Terastallized → defensive types are originals. -/
theorem normal_defensive (tt : PType) (origs : List PType) :
    defensiveTypes false tt origs = origs := by
  simp [defensiveTypes]

/-- Theorem 19: Tera type always in defense when Terastallized. -/
theorem tera_type_in_defense (tt : PType) (origs : List PType) :
    tt ∈ defensiveTypes true tt origs := by
  simp [defensiveTypes]

-- ============================================================
-- §11  Damage Calc With Tera (multi-step path)
-- ============================================================

inductive TDmgPhase where
  | start | stabApplied | typeApplied | done
deriving DecidableEq, Repr

inductive TDmgStep : TDmgPhase × Nat → TDmgPhase × Nat → Prop where
  | applyStab (dmg mult : Nat) :
      TDmgStep (.start, dmg) (.stabApplied, dmg * mult / 10)
  | applyTypeEffect (dmg mult : Nat) :
      TDmgStep (.stabApplied, dmg) (.typeApplied, dmg * mult)
  | finish (dmg : Nat) :
      TDmgStep (.typeApplied, dmg) (.done, dmg)

inductive TDmgPath : TDmgPhase × Nat → TDmgPhase × Nat → Prop where
  | refl (s : TDmgPhase × Nat) : TDmgPath s s
  | step {a b c : TDmgPhase × Nat} : TDmgStep a b → TDmgPath b c → TDmgPath a c

/-- Theorem 20: TDmg path transitivity. -/
theorem TDmgPath.trans {a b c : TDmgPhase × Nat}
    (p : TDmgPath a b) (q : TDmgPath b c) : TDmgPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact TDmgPath.step s (ih q)

/-- Theorem 21: 100 base, 2.0× STAB, 2× super effective → 400. -/
theorem tera_double_stab_super_effective :
    TDmgPath (.start, 100) (.done, 400) :=
  TDmgPath.step (TDmgStep.applyStab 100 20)
    (TDmgPath.step (TDmgStep.applyTypeEffect 200 2)
      (TDmgPath.step (TDmgStep.finish 400)
        (TDmgPath.refl _)))

/-- Theorem 22: No STAB, no super effective: 100 → 100. -/
theorem tera_neutral_damage :
    TDmgPath (.start, 100) (.done, 100) :=
  TDmgPath.step (TDmgStep.applyStab 100 10)
    (TDmgPath.step (TDmgStep.applyTypeEffect 100 1)
      (TDmgPath.step (TDmgStep.finish 100)
        (TDmgPath.refl _)))

end PokemonLean.TerastalMechanics
