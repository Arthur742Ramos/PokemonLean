import PokemonLean.Basic

namespace PokemonLean.Evolution

open PokemonLean

-- ============================================================================
-- EVOLUTION STAGES
-- ============================================================================

inductive EvolutionStage
  | basic
  | stage1
  | stage2
  deriving Repr, BEq, DecidableEq

-- Numeric ordering of stages
def EvolutionStage.toNat : EvolutionStage → Nat
  | .basic  => 0
  | .stage1 => 1
  | .stage2 => 2

instance : LT EvolutionStage where
  lt a b := a.toNat < b.toNat

instance : LE EvolutionStage where
  le a b := a.toNat ≤ b.toNat

instance (a b : EvolutionStage) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toNat < b.toNat))

instance (a b : EvolutionStage) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

-- ============================================================================
-- STAGE PROGRESSION THEOREMS
-- ============================================================================

@[simp] theorem stage_basic_toNat : EvolutionStage.basic.toNat = 0 := rfl
@[simp] theorem stage_stage1_toNat : EvolutionStage.stage1.toNat = 1 := rfl
@[simp] theorem stage_stage2_toNat : EvolutionStage.stage2.toNat = 2 := rfl

theorem basic_lt_stage1 : EvolutionStage.basic < EvolutionStage.stage1 := by
  show EvolutionStage.basic.toNat < EvolutionStage.stage1.toNat
  decide

theorem stage1_lt_stage2 : EvolutionStage.stage1 < EvolutionStage.stage2 := by
  show EvolutionStage.stage1.toNat < EvolutionStage.stage2.toNat
  decide

theorem basic_lt_stage2 : EvolutionStage.basic < EvolutionStage.stage2 := by
  show EvolutionStage.basic.toNat < EvolutionStage.stage2.toNat
  decide

theorem basic_le_all (s : EvolutionStage) : EvolutionStage.basic ≤ s := by
  show EvolutionStage.basic.toNat ≤ s.toNat
  cases s <;> decide

theorem all_le_stage2 (s : EvolutionStage) : s ≤ EvolutionStage.stage2 := by
  show s.toNat ≤ EvolutionStage.stage2.toNat
  cases s <;> decide

theorem stage_le_refl (s : EvolutionStage) : s ≤ s := by
  show s.toNat ≤ s.toNat
  exact Nat.le_refl _

theorem stage_lt_irrefl (s : EvolutionStage) : ¬(s < s) := by
  show ¬(s.toNat < s.toNat)
  exact Nat.lt_irrefl _

theorem stage_lt_trans {a b c : EvolutionStage} (h1 : a < b) (h2 : b < c) : a < c := by
  show a.toNat < c.toNat
  exact Nat.lt_trans h1 h2

theorem stage_le_antisymm {a b : EvolutionStage} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  cases a <;> cases b <;> first | rfl | (exfalso; revert h1 h2; decide)

theorem stage_trichotomy (a b : EvolutionStage) : a < b ∨ a = b ∨ b < a := by
  cases a <;> cases b <;> first | exact Or.inl (by decide) | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr (by decide))

-- ============================================================================
-- SPECIAL EVOLUTION CATEGORIES (VSTAR, VMAX)
-- ============================================================================

inductive SpecialEvolution
  | none
  | vstar
  | vmax
  | vunion
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- EVOLUTION CARD — extends the base Card with evolution metadata
-- ============================================================================

structure EvolutionCard where
  card : Card
  stage : EvolutionStage
  evolvesFrom : Option String  -- name of the pre-evolution
  specialEvo : SpecialEvolution := .none
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- POKEMON IN PLAY WITH EVOLUTION TRACKING
-- ============================================================================

structure EvolvedPokemonInPlay where
  pokemon : PokemonInPlay
  evoCard : EvolutionCard
  turnPlayed : Nat           -- the turn number this Pokémon entered play
  lastEvolvedTurn : Nat      -- the turn number it last evolved (or turnPlayed if never evolved)
  previousCards : List Card  -- stack of previous evolution cards underneath
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- EVOLUTION CHAIN
-- ============================================================================

structure EvolutionChain where
  basic : EvolutionCard
  stage1 : Option EvolutionCard
  stage2 : Option EvolutionCard
  deriving Repr, BEq, DecidableEq

-- The chain is well-formed if stages link correctly
def EvolutionChain.wellFormed (chain : EvolutionChain) : Prop :=
  chain.basic.stage = .basic ∧
  (∀ s1, chain.stage1 = some s1 →
    s1.stage = .stage1 ∧ s1.evolvesFrom = some chain.basic.card.name) ∧
  (∀ s2 s1, chain.stage2 = some s2 → chain.stage1 = some s1 →
    s2.stage = .stage2 ∧ s2.evolvesFrom = some s1.card.name)

-- ============================================================================
-- NEXT STAGE FUNCTION
-- ============================================================================

def nextStage : EvolutionStage → Option EvolutionStage
  | .basic  => some .stage1
  | .stage1 => some .stage2
  | .stage2 => none

@[simp] theorem nextStage_basic : nextStage .basic = some .stage1 := rfl
@[simp] theorem nextStage_stage1 : nextStage .stage1 = some .stage2 := rfl
@[simp] theorem nextStage_stage2 : nextStage .stage2 = none := rfl

theorem nextStage_lt (s s' : EvolutionStage) (h : nextStage s = some s') : s < s' := by
  cases s <;> simp [nextStage] at h <;> subst h
  · exact basic_lt_stage1
  · exact stage1_lt_stage2

theorem nextStage_none_iff_stage2 (s : EvolutionStage) : nextStage s = none ↔ s = .stage2 := by
  cases s <;> simp [nextStage]

-- ============================================================================
-- CAN EVOLVE PREDICATE
-- ============================================================================

/-- A Pokémon can evolve if:
    1. The evolution card's stage is the next stage of the current card
    2. The evolution card's evolvesFrom matches the current card's name
    3. The Pokémon was not played this turn (currentTurn > turnPlayed)
    4. The Pokémon was not already evolved this turn (currentTurn > lastEvolvedTurn)
-/
def canEvolve (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (currentTurn : Nat) : Prop :=
  nextStage inPlay.evoCard.stage = some evoTarget.stage ∧
  evoTarget.evolvesFrom = some inPlay.evoCard.card.name ∧
  currentTurn > inPlay.turnPlayed ∧
  currentTurn > inPlay.lastEvolvedTurn

instance (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (currentTurn : Nat) :
    Decidable (canEvolve evoTarget inPlay currentTurn) := by
  unfold canEvolve
  exact inferInstance

-- ============================================================================
-- VSTAR / VMAX EVOLUTION RULES
-- ============================================================================

/-- VSTAR evolution: evolves from a V Pokémon (must be stage basic with specialEvo = none,
    and the target must be vstar and name-match) -/
def canEvolveVStar (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (currentTurn : Nat) : Prop :=
  evoTarget.specialEvo = .vstar ∧
  inPlay.evoCard.stage = .basic ∧
  evoTarget.evolvesFrom = some inPlay.evoCard.card.name ∧
  currentTurn > inPlay.turnPlayed ∧
  currentTurn > inPlay.lastEvolvedTurn

instance (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (currentTurn : Nat) :
    Decidable (canEvolveVStar evoTarget inPlay currentTurn) := by
  unfold canEvolveVStar
  exact inferInstance

/-- VMAX evolution: evolves from a V Pokémon -/
def canEvolveVMax (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (currentTurn : Nat) : Prop :=
  evoTarget.specialEvo = .vmax ∧
  inPlay.evoCard.stage = .basic ∧
  evoTarget.evolvesFrom = some inPlay.evoCard.card.name ∧
  currentTurn > inPlay.turnPlayed ∧
  currentTurn > inPlay.lastEvolvedTurn

instance (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (currentTurn : Nat) :
    Decidable (canEvolveVMax evoTarget inPlay currentTurn) := by
  unfold canEvolveVMax
  exact inferInstance

-- ============================================================================
-- PERFORM EVOLUTION
-- ============================================================================

/-- Evolve a Pokémon: replace the card, reset status, preserve energy and damage,
    record the previous card. -/
def evolve (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (currentTurn : Nat) :
    EvolvedPokemonInPlay :=
  { pokemon := {
      card := evoTarget.card
      damage := inPlay.pokemon.damage
      status := none                        -- evolution resets status conditions
      energy := inPlay.pokemon.energy       -- energy is preserved
    }
    evoCard := evoTarget
    turnPlayed := inPlay.turnPlayed
    lastEvolvedTurn := currentTurn
    previousCards := inPlay.pokemon.card :: inPlay.previousCards
  }

-- ============================================================================
-- EVOLUTION PRESERVES ENERGY ATTACHMENTS
-- ============================================================================

theorem evolve_preserves_energy (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (turn : Nat) :
    (evolve evoTarget inPlay turn).pokemon.energy = inPlay.pokemon.energy := by
  simp [evolve]

theorem evolve_preserves_energy_length (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (turn : Nat) :
    (evolve evoTarget inPlay turn).pokemon.energy.length = inPlay.pokemon.energy.length := by
  simp [evolve]

-- ============================================================================
-- EVOLUTION RESETS STATUS CONDITIONS
-- ============================================================================

theorem evolve_resets_status (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (turn : Nat) :
    (evolve evoTarget inPlay turn).pokemon.status = none := by
  simp [evolve]

theorem evolve_clears_any_status (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (turn : Nat)
    (_condition : StatusCondition) (_hStatus : inPlay.pokemon.status = some _condition) :
    (evolve evoTarget inPlay turn).pokemon.status = none := by
  simp [evolve]

-- ============================================================================
-- EVOLUTION PRESERVES DAMAGE
-- ============================================================================

theorem evolve_preserves_damage (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (turn : Nat) :
    (evolve evoTarget inPlay turn).pokemon.damage = inPlay.pokemon.damage := by
  simp [evolve]

-- ============================================================================
-- EVOLUTION UPDATES CARD
-- ============================================================================

theorem evolve_updates_card (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (turn : Nat) :
    (evolve evoTarget inPlay turn).pokemon.card = evoTarget.card := by
  simp [evolve]

theorem evolve_updates_evoCard (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (turn : Nat) :
    (evolve evoTarget inPlay turn).evoCard = evoTarget := by
  simp [evolve]

-- ============================================================================
-- CANNOT EVOLVE ON THE TURN A POKÉMON WAS PLAYED
-- ============================================================================

theorem cannot_evolve_same_turn_played (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay)
    (hSameTurn : inPlay.turnPlayed = currentTurn) :
    ¬canEvolve evoTarget inPlay currentTurn := by
  intro ⟨_, _, hTurn, _⟩
  omega

theorem cannot_evolve_same_turn_evolved (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay)
    (hSameTurn : inPlay.lastEvolvedTurn = currentTurn) :
    ¬canEvolve evoTarget inPlay currentTurn := by
  intro ⟨_, _, _, hEvo⟩
  omega

-- ============================================================================
-- EVOLUTION RECORDS PREVIOUS CARD
-- ============================================================================

theorem evolve_records_previous (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (turn : Nat) :
    (evolve evoTarget inPlay turn).previousCards = inPlay.pokemon.card :: inPlay.previousCards := by
  simp [evolve]

theorem evolve_previous_length (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (turn : Nat) :
    (evolve evoTarget inPlay turn).previousCards.length = inPlay.previousCards.length + 1 := by
  simp [evolve]

-- ============================================================================
-- EVOLUTION PRESERVES TURN PLAYED
-- ============================================================================

theorem evolve_preserves_turnPlayed (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (turn : Nat) :
    (evolve evoTarget inPlay turn).turnPlayed = inPlay.turnPlayed := by
  simp [evolve]

theorem evolve_sets_lastEvolvedTurn (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (turn : Nat) :
    (evolve evoTarget inPlay turn).lastEvolvedTurn = turn := by
  simp [evolve]

-- ============================================================================
-- STAGE CANNOT DECREASE THROUGH EVOLUTION
-- ============================================================================

theorem canEvolve_stage_increases (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (turn : Nat)
    (h : canEvolve evoTarget inPlay turn) :
    inPlay.evoCard.stage < evoTarget.stage := by
  obtain ⟨hStage, _, _, _⟩ := h
  exact nextStage_lt _ _ hStage

theorem evolve_stage_increases (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (turn : Nat)
    (h : canEvolve evoTarget inPlay turn) :
    inPlay.evoCard.stage < (evolve evoTarget inPlay turn).evoCard.stage := by
  have hInc := canEvolve_stage_increases evoTarget inPlay turn h
  simp [evolve]
  exact hInc

-- ============================================================================
-- CANNOT EVOLVE FROM STAGE 2 (no nextStage)
-- ============================================================================

theorem cannot_evolve_from_stage2 (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay)
    (turn : Nat) (hStage : inPlay.evoCard.stage = .stage2) :
    ¬canEvolve evoTarget inPlay turn := by
  intro ⟨hNext, _, _, _⟩
  simp [hStage, nextStage] at hNext

-- ============================================================================
-- BASIC CAN ONLY EVOLVE TO STAGE 1 (normal evolution)
-- ============================================================================

theorem basic_evolves_to_stage1 (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay)
    (turn : Nat) (hBasic : inPlay.evoCard.stage = .basic)
    (h : canEvolve evoTarget inPlay turn) :
    evoTarget.stage = .stage1 := by
  obtain ⟨hStage, _, _, _⟩ := h
  simp [hBasic, nextStage] at hStage
  exact hStage.symm

theorem stage1_evolves_to_stage2 (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay)
    (turn : Nat) (hStage1 : inPlay.evoCard.stage = .stage1)
    (h : canEvolve evoTarget inPlay turn) :
    evoTarget.stage = .stage2 := by
  obtain ⟨hStage, _, _, _⟩ := h
  simp [hStage1, nextStage] at hStage
  exact hStage.symm

-- ============================================================================
-- DOUBLE EVOLUTION IN ONE TURN IS IMPOSSIBLE
-- ============================================================================

theorem no_double_evolve_same_turn (evo1 evo2 : EvolutionCard) (inPlay : EvolvedPokemonInPlay)
    (turn : Nat) (_h1 : canEvolve evo1 inPlay turn) :
    ¬canEvolve evo2 (evolve evo1 inPlay turn) turn := by
  intro ⟨_, _, _, hEvo⟩
  simp [evolve] at hEvo

-- ============================================================================
-- EVOLUTION CHAIN WELL-FORMEDNESS THEOREMS
-- ============================================================================

theorem wellFormed_basic_is_basic (chain : EvolutionChain) (h : chain.wellFormed) :
    chain.basic.stage = .basic := by
  exact h.1

theorem wellFormed_stage1_links (chain : EvolutionChain) (s1 : EvolutionCard)
    (h : chain.wellFormed) (hS1 : chain.stage1 = some s1) :
    s1.evolvesFrom = some chain.basic.card.name := by
  exact (h.2.1 s1 hS1).2

theorem wellFormed_stage2_links (chain : EvolutionChain) (s1 s2 : EvolutionCard)
    (h : chain.wellFormed) (hS1 : chain.stage1 = some s1) (hS2 : chain.stage2 = some s2) :
    s2.evolvesFrom = some s1.card.name := by
  exact (h.2.2 s2 s1 hS2 hS1).2

-- ============================================================================
-- CHAIN LENGTH
-- ============================================================================

def EvolutionChain.length (chain : EvolutionChain) : Nat :=
  1 + (if chain.stage1.isSome then 1 else 0) + (if chain.stage2.isSome then 1 else 0)

theorem chain_length_ge_one (chain : EvolutionChain) : chain.length ≥ 1 := by
  simp [EvolutionChain.length]
  omega

theorem chain_length_le_three (chain : EvolutionChain) : chain.length ≤ 3 := by
  simp [EvolutionChain.length]
  cases chain.stage1 <;> cases chain.stage2 <;> simp <;> omega

-- ============================================================================
-- MAKING A FRESH BASIC POKÉMON
-- ============================================================================

def mkBasicInPlay (evoCard : EvolutionCard) (turn : Nat) : EvolvedPokemonInPlay :=
  { pokemon := toPokemonInPlay evoCard.card
    evoCard := evoCard
    turnPlayed := turn
    lastEvolvedTurn := turn
    previousCards := []
  }

theorem mkBasicInPlay_no_damage (evoCard : EvolutionCard) (turn : Nat) :
    (mkBasicInPlay evoCard turn).pokemon.damage = 0 := by
  simp [mkBasicInPlay, toPokemonInPlay]

theorem mkBasicInPlay_no_status (evoCard : EvolutionCard) (turn : Nat) :
    (mkBasicInPlay evoCard turn).pokemon.status = none := by
  simp [mkBasicInPlay, toPokemonInPlay]

theorem mkBasicInPlay_no_energy (evoCard : EvolutionCard) (turn : Nat) :
    (mkBasicInPlay evoCard turn).pokemon.energy = [] := by
  simp [mkBasicInPlay, toPokemonInPlay]

theorem mkBasicInPlay_no_previous (evoCard : EvolutionCard) (turn : Nat) :
    (mkBasicInPlay evoCard turn).previousCards = [] := by
  simp [mkBasicInPlay]

theorem mkBasicInPlay_cannot_evolve_same_turn (evoCard : EvolutionCard) (evoTarget : EvolutionCard) (turn : Nat) :
    ¬canEvolve evoTarget (mkBasicInPlay evoCard turn) turn := by
  intro ⟨_, _, hTurn, _⟩
  simp [mkBasicInPlay] at hTurn

-- ============================================================================
-- CANATTACK AFTER EVOLUTION
-- ============================================================================

theorem canAttack_after_evolve (evoTarget : EvolutionCard) (inPlay : EvolvedPokemonInPlay) (turn : Nat) :
    _root_.canAttack (evolve evoTarget inPlay turn).pokemon = true := by
  simp [evolve, _root_.canAttack]

-- ============================================================================
-- EVOLUTION STAGE TOTALITY
-- ============================================================================

theorem stage_cases (s : EvolutionStage) : s = .basic ∨ s = .stage1 ∨ s = .stage2 := by
  cases s <;> simp

theorem specialEvo_cases (s : SpecialEvolution) : s = .none ∨ s = .vstar ∨ s = .vmax ∨ s = .vunion := by
  cases s <;> simp

end PokemonLean.Evolution
