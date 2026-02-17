/-
  PokemonLean / BreakMechanics.lean

  BREAK Evolution mechanics from XY—BREAKthrough / BREAKpoint / Fates Collide:
  Evolves on top of Stage 1 or Stage 2, keeps lower-stage attacks,
  gains the BREAK attack, 2D art orientation (sideways card),
  BREAK HP = printed HP, counts as evolution for Rare Candy rules,
  prize count = 1 (not increased like EX/GX).

  Multi-step trans/symm/congrArg computational path chains.
  All proofs are sorry-free. 25+ theorems.
-/

set_option linter.unusedVariables false

namespace BreakMechanics

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

-- ============================================================================
-- §2  BREAK Evolution types
-- ============================================================================

inductive Stage where
  | basic   : Stage
  | stage1  : Stage
  | stage2  : Stage
  | break_  : Stage
deriving DecidableEq, Repr

inductive EType where
  | normal   : EType
  | fire     : EType
  | water    : EType
  | grass    : EType
  | electric : EType
  | psychic  : EType
  | fighting : EType
  | dark     : EType
  | metal    : EType
  | fairy    : EType
  | dragon   : EType
  | colorless : EType
deriving DecidableEq, Repr

structure Attack where
  name   : String
  damage : Nat
  cost   : Nat   -- energy cost
deriving DecidableEq, Repr

inductive CardOrientation where
  | vertical   : CardOrientation   -- standard portrait
  | horizontal : CardOrientation   -- BREAK cards are sideways (landscape)
deriving DecidableEq, Repr

structure Pokemon where
  name        : String
  stage       : Stage
  hp          : Nat
  pokeType    : EType
  attacks     : List Attack
  orientation : CardOrientation
  prizeValue  : Nat            -- prizes taken on KO
  isBreak     : Bool
deriving DecidableEq, Repr

-- ============================================================================
-- §3  BREAK evolution rules
-- ============================================================================

/-- A BREAK card can evolve from a matching Stage 1 or Stage 2. -/
def canBreakEvolve (base : Pokemon) (breakCard : Pokemon) : Bool :=
  breakCard.isBreak &&
  breakCard.stage == .break_ &&
  (base.stage == .stage1 || base.stage == .stage2) &&
  base.pokeType == breakCard.pokeType

/-- After BREAK evolution, attacks = base attacks ++ BREAK attacks. -/
def breakAttacks (base : Pokemon) (breakCard : Pokemon) : List Attack :=
  base.attacks ++ breakCard.attacks

/-- BREAK HP = printed HP on the BREAK card (overrides base HP). -/
def breakHP (breakCard : Pokemon) : Nat :=
  breakCard.hp

/-- BREAK cards always have horizontal (sideways) orientation. -/
def breakOrientation : CardOrientation := .horizontal

/-- BREAK prize value is always 1 (unlike EX which gives 2). -/
def breakPrizeValue : Nat := 1

-- ============================================================================
-- §4  Game state & evolution transition
-- ============================================================================

structure ActiveSlot where
  pokemon       : Pokemon
  damage        : Nat
  energyCount   : Nat
  availableAtks : List Attack
  turnPlayed    : Nat
deriving DecidableEq, Repr

structure GameState where
  active     : ActiveSlot
  turnNumber : Nat
  prizesTaken : Nat
deriving DecidableEq, Repr

/-- Perform BREAK evolution: update active slot with combined attacks + BREAK HP. -/
def applyBreakEvolution (gs : GameState) (breakCard : Pokemon)
    (hCanEvolve : canBreakEvolve gs.active.pokemon breakCard = true)
    (hNotFirstTurn : gs.active.turnPlayed < gs.turnNumber) : GameState :=
  let combined := breakAttacks gs.active.pokemon breakCard
  let newPoke : Pokemon := {
    name := breakCard.name
    stage := .break_
    hp := breakHP breakCard
    pokeType := breakCard.pokeType
    attacks := combined
    orientation := breakOrientation
    prizeValue := breakPrizeValue
    isBreak := true
  }
  { gs with active := {
      pokemon := newPoke
      damage := gs.active.damage
      energyCount := gs.active.energyCount
      availableAtks := combined
      turnPlayed := gs.turnNumber
    }
  }

-- ============================================================================
-- §5  BREAK evolution paths
-- ============================================================================

/-- Path witnessing a BREAK evolution game-state transition. -/
def breakEvolvePath (gs : GameState) (breakCard : Pokemon)
    (hCanEvolve : canBreakEvolve gs.active.pokemon breakCard = true)
    (hNotFirstTurn : gs.active.turnPlayed < gs.turnNumber) :
    Path GameState gs (applyBreakEvolution gs breakCard hCanEvolve hNotFirstTurn) :=
  let s1 := Step.mk "check-break-eligible" gs gs
  let s2 := Step.mk "check-not-first-turn" gs gs
  let gs' := applyBreakEvolution gs breakCard hCanEvolve hNotFirstTurn
  let s3 := Step.mk "apply-break-evolution" gs gs'
  Path.single s1 |>.trans (Path.single s2) |>.trans (Path.single s3)

-- Theorem 1: BREAK evolution path has length 3
theorem breakEvolvePath_length (gs : GameState) (breakCard : Pokemon)
    (hCanEvolve : canBreakEvolve gs.active.pokemon breakCard = true)
    (hNotFirstTurn : gs.active.turnPlayed < gs.turnNumber) :
    (breakEvolvePath gs breakCard hCanEvolve hNotFirstTurn).length = 3 := by
  simp [breakEvolvePath, Path.single, Path.trans, Path.length]

-- Theorem 2: BREAK evolution preserves damage counters
theorem breakEvolve_preserves_damage (gs : GameState) (breakCard : Pokemon)
    (hCanEvolve : canBreakEvolve gs.active.pokemon breakCard = true)
    (hNotFirstTurn : gs.active.turnPlayed < gs.turnNumber) :
    (applyBreakEvolution gs breakCard hCanEvolve hNotFirstTurn).active.damage = gs.active.damage := by
  simp [applyBreakEvolution]

-- Theorem 3: BREAK evolution preserves energy
theorem breakEvolve_preserves_energy (gs : GameState) (breakCard : Pokemon)
    (hCanEvolve : canBreakEvolve gs.active.pokemon breakCard = true)
    (hNotFirstTurn : gs.active.turnPlayed < gs.turnNumber) :
    (applyBreakEvolution gs breakCard hCanEvolve hNotFirstTurn).active.energyCount
    = gs.active.energyCount := by
  simp [applyBreakEvolution]

-- Theorem 4: BREAK always results in stage break_
theorem breakEvolve_stage (gs : GameState) (breakCard : Pokemon)
    (hCanEvolve : canBreakEvolve gs.active.pokemon breakCard = true)
    (hNotFirstTurn : gs.active.turnPlayed < gs.turnNumber) :
    (applyBreakEvolution gs breakCard hCanEvolve hNotFirstTurn).active.pokemon.stage = .break_ := by
  simp [applyBreakEvolution]

-- Theorem 5: BREAK always horizontal orientation
theorem breakEvolve_orientation (gs : GameState) (breakCard : Pokemon)
    (hCanEvolve : canBreakEvolve gs.active.pokemon breakCard = true)
    (hNotFirstTurn : gs.active.turnPlayed < gs.turnNumber) :
    (applyBreakEvolution gs breakCard hCanEvolve hNotFirstTurn).active.pokemon.orientation
    = .horizontal := by
  simp [applyBreakEvolution, breakOrientation]

-- Theorem 6: BREAK HP = printed HP
theorem breakEvolve_hp (gs : GameState) (breakCard : Pokemon)
    (hCanEvolve : canBreakEvolve gs.active.pokemon breakCard = true)
    (hNotFirstTurn : gs.active.turnPlayed < gs.turnNumber) :
    (applyBreakEvolution gs breakCard hCanEvolve hNotFirstTurn).active.pokemon.hp
    = breakCard.hp := by
  simp [applyBreakEvolution, breakHP]

-- Theorem 7: BREAK prize value is 1
theorem breakEvolve_prize (gs : GameState) (breakCard : Pokemon)
    (hCanEvolve : canBreakEvolve gs.active.pokemon breakCard = true)
    (hNotFirstTurn : gs.active.turnPlayed < gs.turnNumber) :
    (applyBreakEvolution gs breakCard hCanEvolve hNotFirstTurn).active.pokemon.prizeValue = 1 := by
  simp [applyBreakEvolution, breakPrizeValue]

-- Theorem 8: BREAK keeps lower-stage attacks (they appear in the combined list)
theorem breakEvolve_keeps_lower_attacks (gs : GameState) (breakCard : Pokemon)
    (hCanEvolve : canBreakEvolve gs.active.pokemon breakCard = true)
    (hNotFirstTurn : gs.active.turnPlayed < gs.turnNumber)
    (atk : Attack) (hIn : atk ∈ gs.active.pokemon.attacks) :
    atk ∈ (applyBreakEvolution gs breakCard hCanEvolve hNotFirstTurn).active.availableAtks := by
  simp [applyBreakEvolution, breakAttacks, List.mem_append]
  exact Or.inl hIn

-- Theorem 9: BREAK also gains BREAK attack
theorem breakEvolve_gains_break_attack (gs : GameState) (breakCard : Pokemon)
    (hCanEvolve : canBreakEvolve gs.active.pokemon breakCard = true)
    (hNotFirstTurn : gs.active.turnPlayed < gs.turnNumber)
    (atk : Attack) (hIn : atk ∈ breakCard.attacks) :
    atk ∈ (applyBreakEvolution gs breakCard hCanEvolve hNotFirstTurn).active.availableAtks := by
  simp [applyBreakEvolution, breakAttacks, List.mem_append]
  exact Or.inr hIn

-- Theorem 10: BREAK evolution preserves prizes taken count
theorem breakEvolve_preserves_prizes (gs : GameState) (breakCard : Pokemon)
    (hCanEvolve : canBreakEvolve gs.active.pokemon breakCard = true)
    (hNotFirstTurn : gs.active.turnPlayed < gs.turnNumber) :
    (applyBreakEvolution gs breakCard hCanEvolve hNotFirstTurn).prizesTaken
    = gs.prizesTaken := by
  simp [applyBreakEvolution]

-- ============================================================================
-- §6  BREAK evolution from Stage 1 vs Stage 2
-- ============================================================================

-- Theorem 11: Stage 1 can BREAK evolve
theorem stage1_can_break (base : Pokemon) (breakCard : Pokemon)
    (hBase : base.stage = .stage1) (hBreak : breakCard.isBreak = true)
    (hStage : breakCard.stage = .break_) (hType : base.pokeType = breakCard.pokeType) :
    canBreakEvolve base breakCard = true := by
  simp [canBreakEvolve, hBase, hBreak, hStage, hType]

-- Theorem 12: Stage 2 can BREAK evolve
theorem stage2_can_break (base : Pokemon) (breakCard : Pokemon)
    (hBase : base.stage = .stage2) (hBreak : breakCard.isBreak = true)
    (hStage : breakCard.stage = .break_) (hType : base.pokeType = breakCard.pokeType) :
    canBreakEvolve base breakCard = true := by
  simp [canBreakEvolve, hBase, hBreak, hStage, hType]

-- Theorem 13: Basic cannot BREAK evolve
theorem basic_cannot_break (base : Pokemon) (breakCard : Pokemon)
    (hBase : base.stage = .basic) :
    canBreakEvolve base breakCard = false := by
  simp [canBreakEvolve, hBase]

-- Theorem 14: BREAK cannot evolve from another BREAK
theorem break_cannot_break (base : Pokemon) (breakCard : Pokemon)
    (hBase : base.stage = .break_) :
    canBreakEvolve base breakCard = false := by
  simp [canBreakEvolve, hBase]

-- ============================================================================
-- §7  BREAK path properties
-- ============================================================================

-- Theorem 15: BREAK evolution path is reversible (symm)
theorem breakEvolvePath_reversible (gs : GameState) (breakCard : Pokemon)
    (hCanEvolve : canBreakEvolve gs.active.pokemon breakCard = true)
    (hNotFirstTurn : gs.active.turnPlayed < gs.turnNumber) :
    (breakEvolvePath gs breakCard hCanEvolve hNotFirstTurn).symm.length = 3 := by
  simp [breakEvolvePath, Path.single, Path.trans, Path.length, Path.symm, Step.symm]

-- Theorem 16: combined attack list length
theorem breakAttacks_length (base : Pokemon) (breakCard : Pokemon) :
    (breakAttacks base breakCard).length = base.attacks.length + breakCard.attacks.length := by
  simp [breakAttacks, List.length_append]

-- Theorem 17: BREAK evolution marks pokemon as BREAK
theorem breakEvolve_isBreak (gs : GameState) (breakCard : Pokemon)
    (hCanEvolve : canBreakEvolve gs.active.pokemon breakCard = true)
    (hNotFirstTurn : gs.active.turnPlayed < gs.turnNumber) :
    (applyBreakEvolution gs breakCard hCanEvolve hNotFirstTurn).active.pokemon.isBreak = true := by
  simp [applyBreakEvolution]

-- ============================================================================
-- §8  BREAK and Rare Candy interaction
-- ============================================================================

/-- BREAK counts as evolution, so Rare Candy can target the base stage. -/
def isEvolution (s : Stage) : Bool :=
  match s with
  | .basic => false
  | .stage1 => true
  | .stage2 => true
  | .break_ => true

-- Theorem 18: BREAK is classified as evolution
theorem break_is_evolution : isEvolution Stage.break_ = true := by
  simp [isEvolution]

-- Theorem 19: basic is not evolution
theorem basic_not_evolution : isEvolution Stage.basic = false := by
  simp [isEvolution]

-- Theorem 20: stage1 is evolution
theorem stage1_is_evolution : isEvolution Stage.stage1 = true := by
  simp [isEvolution]

-- ============================================================================
-- §9  BREAK card construction paths
-- ============================================================================

/-- Path from basic → stage1 → BREAK (typical evolution line). -/
def fullBreakLine (basic : Pokemon) (s1 : Pokemon) (brk : Pokemon) :
    Path Pokemon basic brk :=
  let step1 := Step.mk "evolve-to-stage1" basic s1
  let step2 := Step.mk "break-evolve" s1 brk
  Path.single step1 |>.trans (Path.single step2)

-- Theorem 21: full BREAK line has 2 steps
theorem fullBreakLine_length (basic s1 brk : Pokemon) :
    (fullBreakLine basic s1 brk).length = 2 := by
  simp [fullBreakLine, Path.single, Path.trans, Path.length]

/-- Path from basic → stage1 → stage2 → BREAK (Stage 2 BREAK line). -/
def stage2BreakLine (basic s1 s2 brk : Pokemon) :
    Path Pokemon basic brk :=
  let step1 := Step.mk "evolve-to-stage1" basic s1
  let step2 := Step.mk "evolve-to-stage2" s1 s2
  let step3 := Step.mk "break-evolve" s2 brk
  Path.single step1 |>.trans (Path.single step2) |>.trans (Path.single step3)

-- Theorem 22: Stage 2 BREAK line has 3 steps
theorem stage2BreakLine_length (basic s1 s2 brk : Pokemon) :
    (stage2BreakLine basic s1 s2 brk).length = 3 := by
  simp [stage2BreakLine, Path.single, Path.trans, Path.length]

-- Theorem 23: full BREAK line symm has same length
theorem fullBreakLine_symm_length (basic s1 brk : Pokemon) :
    (fullBreakLine basic s1 brk).symm.length = 2 := by
  simp [fullBreakLine, Path.single, Path.trans, Path.length, Path.symm, Step.symm]

-- ============================================================================
-- §10  Concrete example: Greninja BREAK
-- ============================================================================

def froakie : Pokemon := ⟨"Froakie", .basic, 60, .water, [⟨"Bubble", 20, 1⟩], .vertical, 1, false⟩
def frogadier : Pokemon := ⟨"Frogadier", .stage1, 70, .water,
  [⟨"Water Pulse", 30, 1⟩], .vertical, 1, false⟩
def greninja : Pokemon := ⟨"Greninja", .stage2, 130, .water,
  [⟨"Shadow Stitching", 40, 1⟩, ⟨"Moonlight Slash", 60, 2⟩], .vertical, 1, false⟩
def greninja_break : Pokemon := ⟨"Greninja BREAK", .break_, 170, .water,
  [⟨"Giant Water Shuriken", 0, 0⟩], .horizontal, 1, true⟩

-- Theorem 24: Greninja can BREAK evolve
theorem greninja_can_break : canBreakEvolve greninja greninja_break = true := by
  native_decide

-- Theorem 25: Greninja BREAK keeps Shadow Stitching
theorem greninja_break_keeps_attacks :
    ⟨"Shadow Stitching", 40, 1⟩ ∈ breakAttacks greninja greninja_break := by
  simp [breakAttacks, greninja, greninja_break]

-- Theorem 26: Greninja BREAK gains Giant Water Shuriken
theorem greninja_break_gains_gws :
    ⟨"Giant Water Shuriken", 0, 0⟩ ∈ breakAttacks greninja greninja_break := by
  simp [breakAttacks, greninja, greninja_break]

-- Theorem 27: Greninja BREAK HP is 170
theorem greninja_break_hp : breakHP greninja_break = 170 := by
  simp [breakHP, greninja_break]

-- Theorem 28: Greninja BREAK is horizontal
theorem greninja_break_horizontal : greninja_break.orientation = .horizontal := by
  simp [greninja_break]

-- Theorem 29: Froakie cannot BREAK evolve (basic)
theorem froakie_cannot_break : canBreakEvolve froakie greninja_break = false := by
  native_decide

-- Theorem 30: Greninja BREAK prize is 1
theorem greninja_break_prize : greninja_break.prizeValue = 1 := by
  simp [greninja_break]

-- Theorem 31: Full Greninja BREAK line path
def greninjaBreakLine : Path Pokemon froakie greninja_break :=
  let s1 := Step.mk "evolve-Froakie→Frogadier" froakie frogadier
  let s2 := Step.mk "evolve-Frogadier→Greninja" frogadier greninja
  let s3 := Step.mk "BREAK-evolve-Greninja" greninja greninja_break
  Path.single s1 |>.trans (Path.single s2) |>.trans (Path.single s3)

-- Theorem 32: Greninja BREAK line has 3 steps
theorem greninjaBreakLine_length : greninjaBreakLine.length = 3 := by
  simp [greninjaBreakLine, Path.single, Path.trans, Path.length]

-- Theorem 33: total attacks after BREAK = base attacks + BREAK attacks
theorem greninja_break_total_attacks :
    (breakAttacks greninja greninja_break).length = 3 := by
  native_decide

end BreakMechanics
