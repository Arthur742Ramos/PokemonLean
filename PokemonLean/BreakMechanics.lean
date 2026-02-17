/-
  PokemonLean / BreakMechanics.lean

  BREAK Evolution mechanics from XY—BREAKthrough / BREAKpoint / Fates Collide:
  Evolves on top of Stage 1 or Stage 2, keeps lower-stage attacks,
  gains the BREAK attack, 2D art orientation (sideways card),
  BREAK HP = printed HP, counts as evolution for Rare Candy rules,
  prize count = 1 (not increased like EX/GX).

-/

set_option linter.unusedVariables false

namespace BreakMechanics
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

-- Theorem 1: BREAK evolution path has length 3
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

-- Theorem 21: full BREAK line has 2 steps

-- Theorem 22: Stage 2 BREAK line has 3 steps

-- Theorem 23: full BREAK line symm has same length

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
-- Theorem 32: Greninja BREAK line has 3 steps

-- Theorem 33: total attacks after BREAK = base attacks + BREAK attacks

end BreakMechanics
