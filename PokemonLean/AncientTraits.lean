/-
  PokemonLean / AncientTraits.lean

  Ancient Trait mechanics from XY—Ancient Origins / Primal Clash:
  Ω-Barrier (blocks trainer effects from opponent),
  α-Growth (allows double energy attachment per turn),
  Δ-Evolution (evolve on first turn or turn played),
  θ-Double (doubles attack damage).

  Trait interactions, stacking rules, game state transitions.
  Multi-step trans/symm/congrArg computational path chains.
  All proofs are sorry-free. 25+ theorems.
-/

namespace AncientTraits

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

/-- Attach energy to a Pokémon. -/
def attachEnergy (gs : TraitGameState) (e : EType) : TraitGameState :=
  { gs with
    attachedEnergy := e :: gs.attachedEnergy
    energyAttachedThisTurn := gs.energyAttachedThisTurn + 1 }

/-- Theorem 4 – α Growth allows 2 energy per turn. -/
theorem alpha_growth_max (poke : AncientPokemon) (h : hasAlphaGrowth poke) :
    maxEnergyPerTurn poke = 2 := by
  simp [maxEnergyPerTurn, hasAlphaGrowth] at *; simp [h]

/-- Theorem 5 – Normal Pokémon allows 1 energy per turn. -/
theorem normal_max_energy (poke : AncientPokemon) (h : ¬hasAlphaGrowth poke) :
    maxEnergyPerTurn poke = 1 := by
  simp [maxEnergyPerTurn, hasAlphaGrowth] at *; simp [h]

/-- Theorem 6 – Attaching energy increments counter. -/
theorem attach_increments (gs : TraitGameState) (e : EType) :
    (attachEnergy gs e).energyAttachedThisTurn = gs.energyAttachedThisTurn + 1 := by
  rfl

/-- Theorem 7 – Attaching energy adds to the list. -/
theorem attach_adds_energy (gs : TraitGameState) (e : EType) :
    (attachEnergy gs e).attachedEnergy = e :: gs.attachedEnergy := by
  rfl

/-- Theorem 8 – α Growth: after one attach, counter is < 2. -/
theorem alpha_growth_second_ok (gs : TraitGameState) (poke : AncientPokemon)
    (h : hasAlphaGrowth poke) (h0 : gs.energyAttachedThisTurn = 0) (e : EType) :
    (attachEnergy gs e).energyAttachedThisTurn < maxEnergyPerTurn poke := by
  rw [attach_increments, h0, alpha_growth_max poke h]; omega

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
-- ============================================================================

/-- Build α Growth double-attach path. -/
def alphaGrowthPath (gs : TraitGameState) (e1 e2 : EType) :
    Path TraitGameState gs (attachEnergy (attachEnergy gs e1) e2) :=
  let gs1 := attachEnergy gs e1
  let gs2 := attachEnergy gs1 e2
  Path.cons (.mk "attach_1" gs gs1)
    (Path.cons (.mk "attach_2" gs1 gs2) (.nil gs2))

/-- Theorem 17 – α Growth path has length 2. -/
theorem alphaGrowthPath_length (gs : TraitGameState) (e1 e2 : EType) :
    (alphaGrowthPath gs e1 e2).length = 2 := by
  simp [alphaGrowthPath, Path.length]

/-- Full turn path: attach → attack. -/
def fullTurnPath (gs : TraitGameState) (poke : AncientPokemon) (e : EType) :
    Path TraitGameState gs (applyDamage (attachEnergy gs e) (calcDamage poke)) :=
  let gs1 := attachEnergy gs e
  Path.cons (.mk "attach" gs gs1)
    (.single (.mk "attack" gs1 (applyDamage gs1 (calcDamage poke))))

/-- Theorem 18 – Full turn path has length 2. -/
theorem fullTurnPath_length (gs : TraitGameState) (poke : AncientPokemon) (e : EType) :
    (fullTurnPath gs poke e).length = 2 := by
  simp [fullTurnPath, Path.length, Path.single]

/-- Build a symm rewind path. -/
def rewindAttach (gs : TraitGameState) (e : EType) :
    Path TraitGameState (attachEnergy gs e) gs :=
  .single (.mk "undo_attach" (attachEnergy gs e) gs)

/-- Theorem 19 – Round-trip attach+rewind has length 2. -/
theorem roundtrip_length (gs : TraitGameState) (e : EType) :
    ((.single (.mk "attach" gs (attachEnergy gs e)) :
      Path TraitGameState gs (attachEnergy gs e)).trans (rewindAttach gs e)).length = 2 := by
  simp [Path.trans, Path.single, rewindAttach, Path.length]

-- ============================================================================
-- §11  Path algebra
-- ============================================================================

/-- Theorem 20 – trans nil right identity. -/
theorem Path.trans_nil : (p : Path TraitGameState a b) → p.trans (.nil b) = p
  | .nil _ => rfl
  | .cons s p => by simp [Path.trans]; exact Path.trans_nil p

/-- Theorem 21 – trans assoc. -/
theorem Path.trans_assoc_trait (p : Path TraitGameState a b)
    (q : Path TraitGameState b c) (r : Path TraitGameState c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => rfl
  | cons s _ ih => simp [Path.trans]; exact ih q

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
