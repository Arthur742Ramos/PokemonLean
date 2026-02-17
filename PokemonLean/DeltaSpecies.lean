/-
  PokemonLean / DeltaSpecies.lean

  Delta Species mechanics from EX Delta Species / EX Holon Phantoms:
  Pokémon with different types than normal (e.g., Fire-type Pikachu),
  δ-type energy rules, δ-evolution compatibility, dual-typed δ Pokémon,
  δ interactions with normal type matchups, Holon energy cards.

  Multi-step trans/symm/congrArg computational path chains.
  All proofs sorry-free.  22+ theorems.
-/

namespace DeltaSpecies

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

def Path.congrArg (f : α → β) (lbl : String)
    : Path α a b → Path β (f a) (f b)
  | .nil _ => .nil _
  | .cons _ p => .cons (.mk lbl _ _) (p.congrArg f lbl)

theorem Path.trans_nil (p : Path α a b) : p.trans (.nil b) = p := by
  induction p with
  | nil _ => rfl
  | cons s _ ih => simp [Path.trans, ih]

theorem Path.trans_assoc (p : Path α a b) (q : Path α b c) (r : Path α c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => rfl
  | cons s _ ih => simp [Path.trans, ih]

theorem Path.length_trans (p : Path α a b) (q : Path α b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [Path.trans, Path.length]
  | cons _ _ ih => simp [Path.trans, Path.length, ih]; omega

-- ============================================================================
-- §2  Pokémon Types and Delta Species Core
-- ============================================================================

/-- TCG energy/type. -/
inductive PType where
  | fire | water | grass | lightning | psychic | fighting
  | darkness | metal | colorless | dragon
deriving DecidableEq, Repr

/-- Species identifier. -/
structure Species where
  dexNum : Nat
  name   : String
deriving DecidableEq, Repr

/-- Card stage. -/
inductive Stage where
  | basic | stage1 | stage2
deriving DecidableEq, Repr

/-- A Delta Species card: same species, different type than normal. -/
structure DeltaPokemon where
  species     : Species
  normalType  : PType      -- what this species is normally
  deltaType1  : PType      -- δ primary type
  deltaType2  : Option PType -- optional δ secondary type
  stage       : Stage
  hp          : Nat
  isDelta     : Bool
deriving DecidableEq, Repr

/-- Is this a dual-typed δ Pokémon? -/
def DeltaPokemon.isDualTyped (p : DeltaPokemon) : Bool :=
  match p.deltaType2 with
  | some _ => true
  | none   => false

/-- Does the δ type differ from the normal type? -/
def DeltaPokemon.hasTypeShift (p : DeltaPokemon) : Prop :=
  p.deltaType1 ≠ p.normalType

-- ============================================================================
-- §3  Canonical Delta Species Examples
-- ============================================================================

def pikachuDelta : DeltaPokemon :=
  ⟨⟨25, "Pikachu"⟩, .lightning, .metal, none, .basic, 50, true⟩

def charizardDelta : DeltaPokemon :=
  ⟨⟨6, "Charizard"⟩, .fire, .lightning, some .metal, .stage2, 120, true⟩

def mewtwoDelata : DeltaPokemon :=
  ⟨⟨150, "Mewtwo"⟩, .psychic, .fire, none, .basic, 70, true⟩

def tyranitarDelta : DeltaPokemon :=
  ⟨⟨248, "Tyranitar"⟩, .darkness, .lightning, some .metal, .stage2, 130, true⟩

def gardeviorDelta : DeltaPokemon :=
  ⟨⟨282, "Gardevoir"⟩, .psychic, .fire, some .darkness, .stage2, 100, true⟩

def raichuNormal : DeltaPokemon :=
  ⟨⟨26, "Raichu"⟩, .lightning, .lightning, none, .stage1, 80, false⟩

-- ============================================================================
-- §4  Holon Energy Cards
-- ============================================================================

/-- Holon energy types — special energies from the EX Delta Species era. -/
inductive HolonEnergy where
  | holonFF       -- provides Fire + Fighting
  | holonGL       -- provides Grass + Lightning
  | holonWP       -- provides Water + Psychic
  | holonCastform -- provides any type when attached to δ Pokémon
deriving DecidableEq, Repr

/-- What types does a Holon energy provide? -/
def HolonEnergy.providesTypes : HolonEnergy → List PType
  | .holonFF       => [.fire, .fighting]
  | .holonGL       => [.grass, .lightning]
  | .holonWP       => [.water, .psychic]
  | .holonCastform => [.fire, .water, .grass, .lightning, .psychic,
                        .fighting, .darkness, .metal, .colorless]

/-- A Holon energy provides a specific type. -/
def HolonEnergy.provides (e : HolonEnergy) (t : PType) : Bool :=
  match e, t with
  | .holonFF, .fire      => true
  | .holonFF, .fighting  => true
  | .holonGL, .grass     => true
  | .holonGL, .lightning => true
  | .holonWP, .water     => true
  | .holonWP, .psychic   => true
  | .holonCastform, _    => true
  | _, _                 => false

-- ============================================================================
-- §5  Energy Attachment Rules
-- ============================================================================

/-- Energy attachment state for a δ Pokémon. -/
structure EnergyState where
  pokemon       : DeltaPokemon
  basicEnergy   : List PType
  holonEnergy   : List HolonEnergy
  totalEnergy   : Nat
deriving Repr

def mkEnergyState (p : DeltaPokemon) : EnergyState :=
  ⟨p, [], [], 0⟩

def attachBasic (s : EnergyState) (t : PType) : EnergyState :=
  { s with basicEnergy := t :: s.basicEnergy,
           totalEnergy := s.totalEnergy + 1 }

def attachHolon (s : EnergyState) (e : HolonEnergy) : EnergyState :=
  { s with holonEnergy := e :: s.holonEnergy,
           totalEnergy := s.totalEnergy + 1 }

/-- Theorem 1: Attaching basic energy increases total. -/
theorem attach_basic_increases (s : EnergyState) (t : PType) :
    (attachBasic s t).totalEnergy = s.totalEnergy + 1 := by
  rfl

/-- Theorem 2: Attaching Holon energy increases total. -/
theorem attach_holon_increases (s : EnergyState) (e : HolonEnergy) :
    (attachHolon s e).totalEnergy = s.totalEnergy + 1 := by
  rfl

/-- Theorem 3: Basic energy list grows on attachment. -/
theorem attach_basic_list (s : EnergyState) (t : PType) :
    (attachBasic s t).basicEnergy.length = s.basicEnergy.length + 1 := by
  simp [attachBasic]

/-- Theorem 4: Holon energy list grows on attachment. -/
theorem attach_holon_list (s : EnergyState) (e : HolonEnergy) :
    (attachHolon s e).holonEnergy.length = s.holonEnergy.length + 1 := by
  simp [attachHolon]

-- ============================================================================
-- §6  Delta Evolution Compatibility
-- ============================================================================

/-- Evolution relation: can a δ card evolve from another? -/
structure DeltaEvolution where
  prevStage : DeltaPokemon
  nextStage : DeltaPokemon
  desc      : String
deriving Repr

/-- Valid δ evolution: stage increments correctly. -/
def validDeltaEvolution (evo : DeltaEvolution) : Prop :=
  (evo.prevStage.stage = .basic ∧ evo.nextStage.stage = .stage1) ∨
  (evo.prevStage.stage = .stage1 ∧ evo.nextStage.stage = .stage2)

/-- δ Pokémon can evolve from non-δ (and vice versa). -/
def crossDeltaEvolution (evo : DeltaEvolution) : Prop :=
  evo.prevStage.isDelta ≠ evo.nextStage.isDelta

/-- A hypothetical Raichu δ. -/
def raichuDelta : DeltaPokemon :=
  ⟨⟨26, "Raichu"⟩, .lightning, .metal, none, .stage1, 80, true⟩

def pikachuToRaichuDelta : DeltaEvolution :=
  ⟨pikachuDelta, raichuDelta, "Pikachu δ → Raichu δ"⟩

/-- Theorem 5: Pikachu δ → Raichu δ is a valid evolution (basic → stage1). -/
theorem pikachu_raichu_delta_valid :
    validDeltaEvolution pikachuToRaichuDelta := by
  left
  constructor <;> rfl

/-- Theorem 6: Non-δ Raichu evolving from δ Pikachu is cross-delta. -/
def pikachuToNormalRaichu : DeltaEvolution :=
  ⟨pikachuDelta, raichuNormal, "Pikachu δ → Raichu (normal)"⟩

theorem pikachu_normal_raichu_cross :
    crossDeltaEvolution pikachuToNormalRaichu := by
  simp [crossDeltaEvolution, pikachuToNormalRaichu, pikachuDelta, raichuNormal]

-- ============================================================================
-- §7  Type Matchup Interactions with δ Types
-- ============================================================================

/-- Weakness relation: type A is weak to type B. -/
def weakTo : PType → PType → Bool
  | .fire,      .water     => true
  | .water,     .lightning  => true
  | .grass,     .fire      => true
  | .lightning, .fighting  => true
  | .psychic,   .darkness  => true
  | .fighting,  .psychic   => true
  | .darkness,  .fighting  => true
  | .metal,     .fire      => true
  | .dragon,    .dragon    => true
  | _,          _          => false

/-- Resistance relation. -/
def resistsType : PType → PType → Bool
  | .fire,      .metal     => true
  | .water,     .fire      => true
  | .grass,     .water     => true
  | .lightning, .metal     => true
  | .metal,     .psychic   => true
  | .darkness,  .psychic   => true
  | .dragon,    .fire      => true
  | .dragon,    .water     => true
  | _,          _          => false

/-- A δ Pokémon uses its δ type for weakness/resistance, not its normal type. -/
def deltaWeakTo (p : DeltaPokemon) (atk : PType) : Bool :=
  weakTo p.deltaType1 atk

def deltaResists (p : DeltaPokemon) (atk : PType) : Bool :=
  resistsType p.deltaType1 atk

/-- Theorem 7: Metal-type Pikachu δ is weak to fire (not fighting). -/
theorem pikachu_delta_weak_fire :
    deltaWeakTo pikachuDelta .fire = true := by native_decide

/-- Theorem 8: Metal-type Pikachu δ resists psychic. -/
theorem pikachu_delta_resists_psychic :
    deltaResists pikachuDelta .psychic = true := by native_decide

/-- Theorem 9: Delta Pikachu (metal) is NOT weak to fighting. -/
theorem pikachu_delta_not_weak_fighting :
    deltaWeakTo pikachuDelta .fighting = false := by native_decide

-- ============================================================================
-- §8  Dual-Typed δ Pokémon
-- ============================================================================

/-- Theorem 10: Charizard δ is dual-typed. -/
theorem charizard_delta_dual : charizardDelta.isDualTyped = true := by native_decide

/-- Theorem 11: Pikachu δ is not dual-typed. -/
theorem pikachu_delta_not_dual : pikachuDelta.isDualTyped = false := by native_decide

/-- Theorem 12: Tyranitar δ is dual-typed. -/
theorem tyranitar_delta_dual : tyranitarDelta.isDualTyped = true := by native_decide

-- ============================================================================
-- §9  Holon Energy Provision Theorems
-- ============================================================================

/-- Theorem 13: Holon FF provides fire. -/
theorem holonFF_provides_fire : HolonEnergy.provides .holonFF .fire = true := by native_decide

/-- Theorem 14: Holon GL provides lightning. -/
theorem holonGL_provides_lightning : HolonEnergy.provides .holonGL .lightning = true := by native_decide

/-- Theorem 15: Holon WP provides water. -/
theorem holonWP_provides_water : HolonEnergy.provides .holonWP .water = true := by native_decide

/-- Theorem 16: Holon Castform provides darkness (any type). -/
theorem holonCastform_provides_darkness :
    HolonEnergy.provides .holonCastform .darkness = true := by native_decide

-- ============================================================================
-- §10  Energy Attachment Paths
-- ============================================================================

/-- Path witnessing a sequence of energy attachments. -/
def energyAttachPath (p : DeltaPokemon) (t1 t2 : PType) :
    Path EnergyState (mkEnergyState p)
      (attachBasic (attachBasic (mkEnergyState p) t1) t2) :=
  let s0 := mkEnergyState p
  let s1 := attachBasic s0 t1
  let s2 := attachBasic s1 t2
  Path.cons (.mk "attach-energy-1" s0 s1)
    (Path.cons (.mk "attach-energy-2" s1 s2)
      (.nil s2))

/-- Theorem 17: Energy attachment path has length 2. -/
theorem energy_attach_path_length (p : DeltaPokemon) (t1 t2 : PType) :
    (energyAttachPath p t1 t2).length = 2 := by
  simp [energyAttachPath, Path.length]

/-- Mixed energy path: basic then Holon. -/
def mixedEnergyPath (p : DeltaPokemon) (t : PType) (e : HolonEnergy) :
    Path EnergyState (mkEnergyState p)
      (attachHolon (attachBasic (mkEnergyState p) t) e) :=
  let s0 := mkEnergyState p
  let s1 := attachBasic s0 t
  let s2 := attachHolon s1 e
  Path.cons (.mk "attach-basic" s0 s1)
    (Path.cons (.mk "attach-holon" s1 s2)
      (.nil s2))

/-- Theorem 18: Mixed energy path has length 2. -/
theorem mixed_energy_path_length (p : DeltaPokemon) (t : PType) (e : HolonEnergy) :
    (mixedEnergyPath p t e).length = 2 := by
  simp [mixedEnergyPath, Path.length]

/-- Theorem 19: Energy path trans gives combined length. -/
theorem energy_path_trans_length (p : DeltaPokemon) (t1 t2 t3 : PType) :
    let p1 := energyAttachPath p t1 t2
    let s_mid := attachBasic (attachBasic (mkEnergyState p) t1) t2
    let ext := Path.single (Step.mk "attach-3" s_mid (attachBasic s_mid t3))
    (p1.trans ext).length = 3 := by
  simp [energyAttachPath, Path.trans, Path.single, Path.length]

-- ============================================================================
-- §11  Delta Species Type Shift Paths
-- ============================================================================

/-- Game state for type-matchup analysis. -/
structure MatchupState where
  attacker   : DeltaPokemon
  defender   : DeltaPokemon
  weakHit    : Bool
  resistHit  : Bool
deriving Repr

def computeMatchup (atk def_ : DeltaPokemon) : MatchupState :=
  ⟨atk, def_, deltaWeakTo def_ atk.deltaType1,
               deltaResists def_ atk.deltaType1⟩

/-- Theorem 20: Matchup computation is deterministic. -/
theorem matchup_deterministic (atk def_ : DeltaPokemon) :
    computeMatchup atk def_ = computeMatchup atk def_ := by rfl

/-- Theorem 21: Mewtwo δ (fire) attacking Metal Pikachu δ triggers weakness. -/
theorem mewtwo_vs_pikachu_delta :
    (computeMatchup mewtwoDelata pikachuDelta).weakHit = true := by native_decide

/-- Theorem 22: Charizard δ (lightning) vs Pikachu δ (metal) — no weakness. -/
theorem charizard_vs_pikachu_delta :
    (computeMatchup charizardDelta pikachuDelta).weakHit = false := by native_decide

-- ============================================================================
-- §12  Path symmetry and coherence for delta paths
-- ============================================================================

/-- Inversion length preservation for delta paths. -/
theorem delta_path_symm_length {α : Type} {a b : α} (p : Path α a b) :
    p.symm.length = p.length := by
  induction p with
  | nil _ => simp [Path.symm, Path.length]
  | cons s rest ih =>
    simp [Path.symm, Path.length]
    rw [Path.length_trans]
    simp [Path.length, ih]
    omega

end DeltaSpecies
