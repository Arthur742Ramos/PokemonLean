/-
  PokemonLean / AncientTraits.lean

  Ancient Trait mechanics from XY—Ancient Origins / Primal Clash:
  Ω-Barrier (blocks trainer effects from opponent),
  α-Growth (allows double energy attachment per turn),
  Δ-Evolution (evolve on first turn or turn played),
  θ-Double (doubles attack damage).

  Trait interactions, stacking rules, game state transitions.
-/

namespace AncientTraits
-- ============================================================================
-- §2  Ancient Trait types
-- ============================================================================

/-- The four Ancient Traits from XY era. -/
inductive AncientTrait where
  | omegaBarrier   -- Ω Barrier: prevents all effects of Trainer cards
  | alphaGrowth    -- α Growth: attach 2 energy per turn instead of 1
  | deltaEvolution -- Δ Evolution: can evolve on first turn or turn played
  | thetaDouble    -- θ Double: doubles damage output
deriving DecidableEq, Repr

/-- Pokémon card type. -/
inductive CardType where
  | basic     : CardType
  | stage1    : CardType
  | stage2    : CardType
  | restored  : CardType
deriving DecidableEq, Repr

/-- Energy type (simplified). -/
inductive EType where
  | fire | water | grass | lightning | psychic | fighting
  | darkness | metal | fairy | colorless
deriving DecidableEq, Repr

/-- A Pokémon card with optional Ancient Trait. -/
structure AncientPokemon where
  name          : String
  hp            : Nat
  cardType      : CardType
  ancientTrait  : Option AncientTrait
  attackDamage  : Nat
  energyCost    : List EType
deriving Repr

/-- Trainer card effects that Ω Barrier blocks. -/
inductive TrainerEffect where
  | damage       : Nat → TrainerEffect
  | heal         : Nat → TrainerEffect
  | statusChange : String → TrainerEffect
  | moveToHand   : TrainerEffect
  | discard      : TrainerEffect
deriving Repr

-- ============================================================================
-- §3  Game state
-- ============================================================================

structure TraitGameState where
  activeHP         : Nat
  attachedEnergy   : List EType
  energyAttachedThisTurn : Nat
  turnNumber       : Nat
  justPlayed       : Bool
  justEvolved      : Bool
deriving DecidableEq, Repr

def TraitGameState.initial (hp : Nat) : TraitGameState :=
  { activeHP := hp, attachedEnergy := [], energyAttachedThisTurn := 0,
    turnNumber := 1, justPlayed := true, justEvolved := false }

-- ============================================================================
-- §4  Trait predicates (Prop-based for clean proofs)
-- ============================================================================

def hasOmegaBarrier (p : AncientPokemon) : Prop := p.ancientTrait = some .omegaBarrier
def hasAlphaGrowth (p : AncientPokemon) : Prop := p.ancientTrait = some .alphaGrowth
def hasDeltaEvolution (p : AncientPokemon) : Prop := p.ancientTrait = some .deltaEvolution
def hasThetaDouble (p : AncientPokemon) : Prop := p.ancientTrait = some .thetaDouble

-- ============================================================================
-- §5  Ω Barrier mechanics
-- ============================================================================

/-- Apply a trainer effect; blocked if Ω Barrier. -/
def applyTrainerEffect (gs : TraitGameState) (poke : AncientPokemon)
    (eff : TrainerEffect) : TraitGameState :=
  if poke.ancientTrait = some .omegaBarrier then gs
  else match eff with
    | .damage n => { gs with activeHP := gs.activeHP - n }
    | .heal n   => { gs with activeHP := min (gs.activeHP + n) poke.hp }
    | _         => gs

/-- Theorem 1 – Ω Barrier blocks all trainer effects. -/
theorem omega_barrier_blocks (gs : TraitGameState) (poke : AncientPokemon)
    (eff : TrainerEffect) (h : hasOmegaBarrier poke) :
    applyTrainerEffect gs poke eff = gs := by
  simp [applyTrainerEffect, hasOmegaBarrier] at *
  simp [h]

/-- Theorem 2 – Ω Barrier preserves HP against damage. -/
theorem omega_barrier_preserves_hp (gs : TraitGameState) (poke : AncientPokemon)
    (n : Nat) (h : hasOmegaBarrier poke) :
    (applyTrainerEffect gs poke (.damage n)).activeHP = gs.activeHP := by
  have := omega_barrier_blocks gs poke (.damage n) h
  rw [this]

/-- Theorem 3 – Without Ω Barrier, damage reduces HP. -/
theorem no_barrier_damage_reduces (gs : TraitGameState) (poke : AncientPokemon)
    (n : Nat) (h : ¬hasOmegaBarrier poke) :
    (applyTrainerEffect gs poke (.damage n)).activeHP = gs.activeHP - n := by
  simp [applyTrainerEffect, hasOmegaBarrier] at *
  simp [h]

-- ============================================================================
-- §6  α Growth mechanics
-- ============================================================================

/-- Maximum energy attachments per turn. -/
def maxEnergyPerTurn (poke : AncientPokemon) : Nat :=
  if poke.ancientTrait = some .alphaGrowth then 2 else 1


/-- Theorem 4 – α Growth allows 2 energy per turn. -/
theorem alpha_growth_max (poke : AncientPokemon) (h : hasAlphaGrowth poke) :
    maxEnergyPerTurn poke = 2 := by
  simp [maxEnergyPerTurn, hasAlphaGrowth] at *; simp [h]

/-- Theorem 5 – Normal Pokémon allows 1 energy per turn. -/
theorem normal_max_energy (poke : AncientPokemon) (h : ¬hasAlphaGrowth poke) :
    maxEnergyPerTurn poke = 1 := by
  simp [maxEnergyPerTurn, hasAlphaGrowth] at *; simp [h]


-- ============================================================================
-- §7  Δ Evolution mechanics
-- ============================================================================

/-- Whether evolution is normally legal. -/
def canEvolveNormally (gs : TraitGameState) : Prop :=
  gs.turnNumber > 1 ∧ ¬gs.justPlayed = true

/-- Whether evolution is legal (normal rules OR Δ Evolution). -/
def canEvolve (gs : TraitGameState) (poke : AncientPokemon) : Prop :=
  canEvolveNormally gs ∨ hasDeltaEvolution poke

/-- Theorem 9 – Δ Evolution always allows evolution. -/
theorem delta_always_evolves (gs : TraitGameState) (poke : AncientPokemon)
    (h : hasDeltaEvolution poke) : canEvolve gs poke :=
  Or.inr h

/-- Theorem 10 – On first turn, only Δ Evolution can evolve. -/
theorem first_turn_needs_delta (gs : TraitGameState) (poke : AncientPokemon)
    (hTurn : gs.turnNumber = 1) (_h : canEvolve gs poke) :
    canEvolveNormally gs → False := by
  intro ⟨hgt, _⟩; omega

/-- Theorem 11 – After turn 1, non-just-played can evolve without trait. -/
theorem later_turn_evolve (gs : TraitGameState)
    (hTurn : gs.turnNumber > 1) (hNotJust : gs.justPlayed = false) :
    canEvolveNormally gs := by
  exact ⟨hTurn, by simp [hNotJust]⟩

-- ============================================================================
-- §8  θ Double mechanics
-- ============================================================================

/-- Calculate damage with θ Double trait. -/
def calcDamage (poke : AncientPokemon) : Nat :=
  if poke.ancientTrait = some .thetaDouble then poke.attackDamage * 2
  else poke.attackDamage

/-- Apply damage to opponent. -/
def applyDamage (gs : TraitGameState) (dmg : Nat) : TraitGameState :=
  { gs with activeHP := gs.activeHP - dmg }

/-- Theorem 12 – θ Double doubles damage. -/
theorem theta_doubles (poke : AncientPokemon) (h : hasThetaDouble poke) :
    calcDamage poke = poke.attackDamage * 2 := by
  simp [calcDamage, hasThetaDouble] at *; simp [h]

/-- Theorem 13 – Without θ Double, damage is base. -/
theorem normal_damage (poke : AncientPokemon) (h : ¬hasThetaDouble poke) :
    calcDamage poke = poke.attackDamage := by
  simp [calcDamage, hasThetaDouble] at *; simp [h]

-- ============================================================================
-- §9  Trait exclusivity
-- ============================================================================

/-- Theorem 14 – Traits are mutually exclusive. -/
theorem trait_exclusive (poke : AncientPokemon) (t1 t2 : AncientTrait)
    (h1 : poke.ancientTrait = some t1) (h2 : poke.ancientTrait = some t2) :
    t1 = t2 := by
  rw [h1] at h2; exact Option.some.inj h2

/-- Theorem 15 – Ω Barrier implies not α Growth. -/
theorem omega_not_alpha (poke : AncientPokemon)
    (h : hasOmegaBarrier poke) : ¬hasAlphaGrowth poke := by
  intro ha
  have := trait_exclusive poke _ _ h ha
  cases this

/-- Theorem 16 – θ Double implies not Δ Evolution. -/
theorem theta_not_delta (poke : AncientPokemon)
    (h : hasThetaDouble poke) : ¬hasDeltaEvolution poke := by
  intro hd
  have := trait_exclusive poke _ _ h hd
  cases this

-- ============================================================================
-- §10  Path-based game flow
/-- Theorem 22 – congrArg: Ω Barrier is HP-invariant across a list of effects. -/
theorem omega_invariant_list
    (poke : AncientPokemon) (h : hasOmegaBarrier poke)
    (gs : TraitGameState) (effects : List TrainerEffect) :
    (effects.foldl (fun s e => applyTrainerEffect s poke e) gs).activeHP = gs.activeHP := by
  induction effects generalizing gs with
  | nil => rfl
  | cons eff rest ih =>
    simp [List.foldl]
    have hblock := omega_barrier_blocks gs poke eff h
    rw [hblock]
    exact ih gs

-- ============================================================================
-- §12  Concrete Pokémon
-- ============================================================================

def primalGroudon : AncientPokemon :=
  { name := "Primal Groudon-EX", hp := 240, cardType := .basic,
    ancientTrait := some .omegaBarrier, attackDamage := 100,
    energyCost := [.fighting, .fighting, .fighting, .colorless] }

def primalKyogre : AncientPokemon :=
  { name := "Primal Kyogre-EX", hp := 240, cardType := .basic,
    ancientTrait := some .alphaGrowth, attackDamage := 150,
    energyCost := [.water, .water, .water, .colorless] }

def sceptileAT : AncientPokemon :=
  { name := "Sceptile AT", hp := 130, cardType := .stage2,
    ancientTrait := some .deltaEvolution, attackDamage := 60,
    energyCost := [.grass, .colorless] }

def machampAT : AncientPokemon :=
  { name := "Machamp AT", hp := 150, cardType := .stage2,
    ancientTrait := some .thetaDouble, attackDamage := 80,
    energyCost := [.fighting, .fighting, .colorless] }

/-- Theorem 23 – Primal Groudon has Ω Barrier. -/
theorem groudon_omega : hasOmegaBarrier primalGroudon := rfl

/-- Theorem 24 – Primal Kyogre has α Growth. -/
theorem kyogre_alpha : hasAlphaGrowth primalKyogre := rfl

/-- Theorem 25 – Sceptile has Δ Evolution. -/
theorem sceptile_delta : hasDeltaEvolution sceptileAT := rfl

/-- Theorem 26 – Machamp has θ Double. -/
theorem machamp_theta : hasThetaDouble machampAT := rfl

/-- Theorem 27 – Machamp θ Double: 80 base → 160 actual. -/
theorem machamp_160 : calcDamage machampAT = 160 := by
  simp [calcDamage, machampAT]

/-- Theorem 28 – Groudon blocks any trainer damage. -/
theorem groudon_blocks_damage (gs : TraitGameState) (n : Nat) :
    (applyTrainerEffect gs primalGroudon (.damage n)).activeHP = gs.activeHP :=
  omega_barrier_preserves_hp gs primalGroudon n groudon_omega

/-- Theorem 29 – Kyogre: maxEnergyPerTurn = 2. -/
theorem kyogre_max_2 : maxEnergyPerTurn primalKyogre = 2 :=
  alpha_growth_max primalKyogre kyogre_alpha

/-- Theorem 30 – Sceptile can evolve on any turn. -/
theorem sceptile_evolves_anytime (gs : TraitGameState) :
    canEvolve gs sceptileAT :=
  delta_always_evolves gs sceptileAT sceptile_delta

end AncientTraits
