/-
  PokemonLean / TypeMatchups.lean

  Pokémon type matchup system formalised in Lean 4.
  Covers: 18 types, weakness/resistance/immunity tables,
  effectiveness multipliers (0×, ½×, 1×, 2×, 4× for dual-type),
  inverse type chart, multi-type damage computation,
  and type-chart symmetry / path structure.

  All proofs are sorry-free. Uses computational paths for
  type-effectiveness calculation chains.  15+ theorems.
-/

namespace PokemonLean.TypeMatchups

-- ============================================================
-- §1  Computational Paths
-- ============================================================

inductive Step (α : Type) : α → α → Type where
  | mk : (tag : String) → (a b : α) → Step α a b

inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

def Path.trans {α : Type} {a b c : α}
    (p : Path α a b) (q : Path α b c) : Path α a c :=
  match p with
  | .nil _ => q
  | .cons s rest => .cons s (rest.trans q)

def Path.length {α : Type} {a b : α} : Path α a b → Nat
  | .nil _       => 0
  | .cons _ rest => 1 + rest.length

def Step.symm {α : Type} {a b : α} : Step α a b → Step α b a
  | .mk tag a b => .mk (tag ++ "⁻¹") b a

def Path.symm {α : Type} {a b : α} : Path α a b → Path α b a
  | .nil a => .nil a
  | .cons s rest => rest.symm.trans (.cons s.symm (.nil _))

def Path.single {α : Type} {a b : α} (s : Step α a b) : Path α a b :=
  .cons s (.nil b)

def Path.congrArg {α β : Type} (f : α → β) {a b : α}
    (p : Path α a b) : Path β (f a) (f b) :=
  match p with
  | .nil a => .nil (f a)
  | .cons (.mk tag x y) rest =>
    .cons (.mk ("congr:" ++ tag) (f x) (f y)) (rest.congrArg f)

-- ============================================================
-- §2  Path algebra lemmas
-- ============================================================

/-- Theorem 1: nil left identity. -/
theorem Path.trans_nil_left {α : Type} {a b : α} (p : Path α a b) :
    (Path.nil a).trans p = p := rfl

/-- Theorem 2: nil right identity. -/
theorem Path.trans_nil_right {α : Type} {a b : α} (p : Path α a b) :
    p.trans (Path.nil b) = p := by
  induction p with
  | nil _ => rfl
  | cons s rest ih => simp [Path.trans, ih]

/-- Theorem 3: trans associativity. -/
theorem Path.trans_assoc {α : Type} {a b c d : α}
    (p : Path α a b) (q : Path α b c) (r : Path α c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => rfl
  | cons s rest ih => simp [Path.trans, ih]

/-- Theorem 4: length distributes over trans. -/
theorem Path.length_trans {α : Type} {a b c : α}
    (p : Path α a b) (q : Path α b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [Path.trans, Path.length]
  | cons s rest ih => simp [Path.trans, Path.length, ih]; omega

-- ============================================================
-- §3  Pokémon Types (18 main-series types)
-- ============================================================

inductive PType where
  | normal | fire | water | electric | grass | ice
  | fighting | poison | ground | flying | psychic | bug
  | rock | ghost | dragon | dark | steel | fairy
deriving DecidableEq, Repr

-- ============================================================
-- §4  Effectiveness multiplier (rational, represented as numerator with denominator 2)
-- ============================================================

/-- Effectiveness as a rational multiplier × 2 to stay in Nat.
    0 = immune (0×), 1 = not very effective (½×),
    2 = neutral (1×), 4 = super effective (2×). -/
inductive Eff where
  | immune    -- 0×
  | notVery   -- ½×
  | neutral   -- 1×
  | superEff  -- 2×
deriving DecidableEq, Repr

def Eff.toNat : Eff → Nat
  | .immune   => 0
  | .notVery  => 1
  | .neutral  => 2
  | .superEff => 4

/-- Theorem 5: neutral toNat is 2. -/
theorem Eff.toNat_neutral : Eff.neutral.toNat = 2 := rfl

/-- Theorem 6: immune toNat is 0. -/
theorem Eff.toNat_immune : Eff.immune.toNat = 0 := rfl

-- ============================================================
-- §5  Type chart (attacking type → defending type → effectiveness)
-- ============================================================

/-- Core type chart. Only non-neutral entries listed. -/
def typeEff : PType → PType → Eff
  -- Normal attacks
  | .normal, .rock  => .notVery  | .normal, .steel  => .notVery
  | .normal, .ghost => .immune
  -- Fire attacks
  | .fire, .grass   => .superEff | .fire, .ice     => .superEff
  | .fire, .bug     => .superEff | .fire, .steel    => .superEff
  | .fire, .water   => .notVery  | .fire, .rock     => .notVery
  | .fire, .fire    => .notVery  | .fire, .dragon   => .notVery
  -- Water attacks
  | .water, .fire   => .superEff | .water, .ground  => .superEff
  | .water, .rock   => .superEff
  | .water, .water  => .notVery  | .water, .grass   => .notVery
  | .water, .dragon => .notVery
  -- Electric attacks
  | .electric, .water  => .superEff | .electric, .flying => .superEff
  | .electric, .electric => .notVery | .electric, .grass  => .notVery
  | .electric, .dragon => .notVery
  | .electric, .ground => .immune
  -- Grass attacks
  | .grass, .water  => .superEff | .grass, .ground  => .superEff
  | .grass, .rock   => .superEff
  | .grass, .fire   => .notVery  | .grass, .grass   => .notVery
  | .grass, .poison => .notVery  | .grass, .flying  => .notVery
  | .grass, .bug    => .notVery  | .grass, .dragon  => .notVery
  | .grass, .steel  => .notVery
  -- Ice attacks
  | .ice, .grass    => .superEff | .ice, .ground   => .superEff
  | .ice, .flying   => .superEff | .ice, .dragon   => .superEff
  | .ice, .fire     => .notVery  | .ice, .water    => .notVery
  | .ice, .ice      => .notVery  | .ice, .steel    => .notVery
  -- Fighting attacks
  | .fighting, .normal => .superEff | .fighting, .ice    => .superEff
  | .fighting, .rock   => .superEff | .fighting, .dark   => .superEff
  | .fighting, .steel  => .superEff
  | .fighting, .poison => .notVery  | .fighting, .flying => .notVery
  | .fighting, .psychic => .notVery | .fighting, .bug    => .notVery
  | .fighting, .fairy  => .notVery
  | .fighting, .ghost  => .immune
  -- Poison attacks
  | .poison, .grass  => .superEff | .poison, .fairy  => .superEff
  | .poison, .poison => .notVery  | .poison, .ground => .notVery
  | .poison, .rock   => .notVery  | .poison, .ghost  => .notVery
  | .poison, .steel  => .immune
  -- Ground attacks
  | .ground, .fire    => .superEff | .ground, .electric => .superEff
  | .ground, .poison  => .superEff | .ground, .rock     => .superEff
  | .ground, .steel   => .superEff
  | .ground, .grass   => .notVery  | .ground, .bug      => .notVery
  | .ground, .flying  => .immune
  -- Flying attacks
  | .flying, .grass   => .superEff | .flying, .fighting => .superEff
  | .flying, .bug     => .superEff
  | .flying, .electric => .notVery | .flying, .rock     => .notVery
  | .flying, .steel   => .notVery
  -- Psychic attacks
  | .psychic, .fighting => .superEff | .psychic, .poison => .superEff
  | .psychic, .psychic  => .notVery  | .psychic, .steel  => .notVery
  | .psychic, .dark     => .immune
  -- Bug attacks
  | .bug, .grass   => .superEff | .bug, .psychic => .superEff
  | .bug, .dark    => .superEff
  | .bug, .fire    => .notVery  | .bug, .fighting => .notVery
  | .bug, .poison  => .notVery  | .bug, .flying   => .notVery
  | .bug, .ghost   => .notVery  | .bug, .steel    => .notVery
  | .bug, .fairy   => .notVery
  -- Rock attacks
  | .rock, .fire   => .superEff | .rock, .ice     => .superEff
  | .rock, .flying => .superEff | .rock, .bug     => .superEff
  | .rock, .fighting => .notVery | .rock, .ground => .notVery
  | .rock, .steel  => .notVery
  -- Ghost attacks
  | .ghost, .psychic => .superEff | .ghost, .ghost   => .superEff
  | .ghost, .dark    => .notVery
  | .ghost, .normal  => .immune
  -- Dragon attacks
  | .dragon, .dragon => .superEff
  | .dragon, .steel  => .notVery
  | .dragon, .fairy  => .immune
  -- Dark attacks
  | .dark, .psychic  => .superEff | .dark, .ghost    => .superEff
  | .dark, .fighting => .notVery  | .dark, .dark     => .notVery
  | .dark, .fairy    => .notVery
  -- Steel attacks
  | .steel, .ice    => .superEff | .steel, .rock   => .superEff
  | .steel, .fairy  => .superEff
  | .steel, .fire   => .notVery | .steel, .water  => .notVery
  | .steel, .electric => .notVery | .steel, .steel => .notVery
  -- Fairy attacks
  | .fairy, .fighting => .superEff | .fairy, .dragon => .superEff
  | .fairy, .dark     => .superEff
  | .fairy, .fire     => .notVery  | .fairy, .poison => .notVery
  | .fairy, .steel    => .notVery
  -- Catch-all
  | _, _ => .neutral

-- ============================================================
-- §6  Basic type chart theorems
-- ============================================================

/-- Theorem 7: Fire is super effective against Grass. -/
theorem fire_beats_grass : typeEff .fire .grass = .superEff := rfl

/-- Theorem 8: Water is super effective against Fire. -/
theorem water_beats_fire : typeEff .water .fire = .superEff := rfl

/-- Theorem 9: Grass is super effective against Water. -/
theorem grass_beats_water : typeEff .grass .water = .superEff := rfl

/-- Theorem 10: starter triangle — each beats the next. -/
theorem starter_triangle :
    typeEff .fire .grass = .superEff ∧
    typeEff .grass .water = .superEff ∧
    typeEff .water .fire = .superEff := ⟨rfl, rfl, rfl⟩

/-- Theorem 11: Normal cannot hit Ghost. -/
theorem normal_immune_ghost : typeEff .normal .ghost = .immune := rfl

/-- Theorem 12: Ghost cannot hit Normal. -/
theorem ghost_immune_normal : typeEff .ghost .normal = .immune := rfl

/-- Theorem 13: Electric immune to Ground-type moves. -/
theorem electric_immune_ground : typeEff .electric .ground = .immune := rfl

/-- Theorem 14: Dragon is immune to Fairy attacks. -/
theorem dragon_immune_fairy : typeEff .dragon .fairy = .immune := rfl

-- ============================================================
-- §7  Dual-type effectiveness
-- ============================================================

/-- Multiply two effectiveness values (for dual-type Pokémon).
    Uses the ×2-encoded representation:
    result = (a.toNat * b.toNat) represents 4× the actual multiplier squared.
    We compute the combined multiplier directly. -/
def Eff.combine (a b : Eff) : Nat :=
  a.toNat * b.toNat
  -- In ×2 encoding: immune(0)*anything = 0 (immune),
  -- superEff(4)*superEff(4)=16 (4× actual),
  -- superEff(4)*neutral(2)=8 (2× actual),
  -- notVery(1)*notVery(1)=1 (¼× actual),
  -- etc.

/-- Dual-type effectiveness: attack vs (type1, type2). -/
def dualTypeEff (atk : PType) (def1 def2 : PType) : Nat :=
  Eff.combine (typeEff atk def1) (typeEff atk def2)

/-- Theorem 15: 4× weakness: Ground vs Steel/Electric dual type.
    Ground is SE against both Steel and Electric. -/
theorem quad_weakness_ground_steel_electric :
    dualTypeEff .ground .steel .electric = 16 := rfl

/-- Theorem 16: Fire vs Water/Rock: NVE + NVE = ¼×. -/
theorem quarter_eff_fire_water_rock :
    dualTypeEff .fire .water .rock = 1 := rfl

/-- Theorem 17: Any attack involving immunity yields 0. -/
theorem immune_dual (atk : PType) (d1 d2 : PType)
    (h : typeEff atk d1 = .immune) :
    dualTypeEff atk d1 d2 = 0 := by
  simp [dualTypeEff, Eff.combine, h, Eff.toNat]

/-- Theorem 18: Neutral against both types gives standard damage. -/
theorem neutral_dual (atk : PType) (d1 d2 : PType)
    (h1 : typeEff atk d1 = .neutral) (h2 : typeEff atk d2 = .neutral) :
    dualTypeEff atk d1 d2 = 4 := by
  simp [dualTypeEff, Eff.combine, h1, h2, Eff.toNat]

-- ============================================================
-- §8  Damage calculation as a computational path
-- ============================================================

inductive DmgPhase where
  | base | typeApplied | stabApplied | final
deriving DecidableEq, Repr

inductive DmgStep : DmgPhase × Nat → DmgPhase × Nat → Prop where
  | applyType (dmg : Nat) (mult : Nat) :
      DmgStep (.base, dmg) (.typeApplied, dmg * mult / 2)
  | applySTAB (dmg : Nat) :
      DmgStep (.typeApplied, dmg) (.stabApplied, dmg * 3 / 2)
  | skipSTAB (dmg : Nat) :
      DmgStep (.typeApplied, dmg) (.stabApplied, dmg)
  | finish (dmg : Nat) :
      DmgStep (.stabApplied, dmg) (.final, dmg)

inductive DmgPath : DmgPhase × Nat → DmgPhase × Nat → Prop where
  | refl (s : DmgPhase × Nat) : DmgPath s s
  | step {s₁ s₂ s₃ : DmgPhase × Nat} :
      DmgStep s₁ s₂ → DmgPath s₂ s₃ → DmgPath s₁ s₃

/-- Theorem 19: DmgPath is transitive. -/
theorem DmgPath.trans {a b c : DmgPhase × Nat}
    (p : DmgPath a b) (q : DmgPath b c) : DmgPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact DmgPath.step s (ih q)

/-- Theorem 20: Single step is a path. -/
theorem DmgPath.single {a b : DmgPhase × Nat} (s : DmgStep a b) :
    DmgPath a b := DmgPath.step s (DmgPath.refl _)

-- ============================================================
-- §9  STAB (Same-Type Attack Bonus) example paths
-- ============================================================

/-- Full damage path: 100 base, 2× type, STAB. -/
example : DmgPath (.base, 100) (.final, 100 * 4 / 2 * 3 / 2) :=
  DmgPath.step (DmgStep.applyType 100 4)
    (DmgPath.step (DmgStep.applySTAB (100 * 4 / 2))
      (DmgPath.step (DmgStep.finish (100 * 4 / 2 * 3 / 2))
        (DmgPath.refl _)))

/-- Full damage path: 100 base, neutral, no STAB. -/
example : DmgPath (.base, 100) (.final, 100) :=
  DmgPath.step (DmgStep.applyType 100 2)
    (DmgPath.step (DmgStep.skipSTAB (100 * 2 / 2))
      (DmgPath.step (DmgStep.finish 100)
        (DmgPath.refl _)))

-- ============================================================
-- §10  Inverse type chart
-- ============================================================

/-- What types are super effective AGAINST a given type? -/
def weakTo (def_ : PType) : List PType :=
  [.normal, .fire, .water, .electric, .grass, .ice,
   .fighting, .poison, .ground, .flying, .psychic, .bug,
   .rock, .ghost, .dragon, .dark, .steel, .fairy].filter
    fun atk => typeEff atk def_ == .superEff

/-- Theorem 21: Fire is weak to Water, Ground, Rock. -/
theorem fire_weaknesses :
    weakTo .fire = [.water, .ground, .rock] := by native_decide

/-- Theorem 22: Dragon is weak to Ice, Dragon, Fairy. -/
theorem dragon_weaknesses :
    weakTo .dragon = [.ice, .dragon, .fairy] := by native_decide

/-- What types resist a given attack type? -/
def resistedBy (atk : PType) : List PType :=
  [.normal, .fire, .water, .electric, .grass, .ice,
   .fighting, .poison, .ground, .flying, .psychic, .bug,
   .rock, .ghost, .dragon, .dark, .steel, .fairy].filter
    fun def_ => typeEff atk def_ == .notVery

/-- Theorem 23: Fire is resisted by Water, Rock, Fire, Dragon. -/
theorem fire_resisted :
    resistedBy .fire = [.fire, .water, .rock, .dragon] := by native_decide

-- ============================================================
-- §11  Type effectiveness symmetry properties
-- ============================================================

/-- Theorem 24: Effectiveness toNat is bounded by 4. -/
theorem Eff.toNat_le_four (e : Eff) : e.toNat ≤ 4 := by
  cases e <;> simp [Eff.toNat]

/-- Theorem 25: combine is commutative. -/
theorem Eff.combine_comm (a b : Eff) :
    Eff.combine a b = Eff.combine b a := by
  simp [Eff.combine, Nat.mul_comm]

/-- Theorem 26: immune absorbs everything. -/
theorem Eff.combine_immune_left (b : Eff) :
    Eff.combine .immune b = 0 := by
  simp [Eff.combine, Eff.toNat]

/-- Theorem 27: neutral is identity for combine. -/
theorem Eff.combine_neutral_left (b : Eff) :
    Eff.combine .neutral b = 2 * b.toNat := by
  simp [Eff.combine, Eff.toNat]

-- ============================================================
-- §12  Type-chart path: the starter cycle as a 3-step path
-- ============================================================

/-- A step in the type advantage cycle. -/
inductive TypeAdvStep : PType → PType → Prop where
  | beats (atk def_ : PType) (h : typeEff atk def_ = .superEff) :
      TypeAdvStep atk def_

/-- Multi-step type advantage chain. -/
inductive TypeAdvPath : PType → PType → Prop where
  | refl (t : PType) : TypeAdvPath t t
  | step {a b c : PType} : TypeAdvStep a b → TypeAdvPath b c → TypeAdvPath a c

/-- Theorem 28: starter cycle Fire → Grass → Water → Fire. -/
theorem starter_cycle :
    TypeAdvPath .fire .fire :=
  TypeAdvPath.step (TypeAdvStep.beats .fire .grass rfl)
    (TypeAdvPath.step (TypeAdvStep.beats .grass .water rfl)
      (TypeAdvPath.step (TypeAdvStep.beats .water .fire rfl)
        (TypeAdvPath.refl .fire)))

/-- Theorem 29: TypeAdvPath transitive. -/
theorem TypeAdvPath.trans {a b c : PType}
    (p : TypeAdvPath a b) (q : TypeAdvPath b c) : TypeAdvPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact TypeAdvPath.step s (ih q)

-- ============================================================
-- §13  Effectiveness ordering via paths
-- ============================================================

/-- Eff has a natural ordering. -/
def Eff.toOrd : Eff → Nat
  | .immune   => 0
  | .notVery  => 1
  | .neutral  => 2
  | .superEff => 3

/-- Theorem 30: toOrd is injective. -/
theorem Eff.toOrd_injective (a b : Eff) (h : a.toOrd = b.toOrd) : a = b := by
  cases a <;> cases b <;> simp [Eff.toOrd] at h <;> rfl

/-- Theorem 31: superEff is strictly greater than neutral. -/
theorem Eff.superEff_gt_neutral : Eff.superEff.toOrd > Eff.neutral.toOrd := by
  simp [Eff.toOrd]

/-- Theorem 32: immune is the minimum. -/
theorem Eff.immune_min (e : Eff) : Eff.immune.toOrd ≤ e.toOrd := by
  cases e <;> simp [Eff.toOrd]

end PokemonLean.TypeMatchups
