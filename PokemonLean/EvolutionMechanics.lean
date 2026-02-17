/-
  PokemonLean / EvolutionMechanics.lean

  Evolution mechanics for the Pokémon TCG formalised via computational
  paths. Evolution is a state-transition chain tracked by Path/Step/trans/
  symm/congrArg — paths ARE the math.

  Topics:
  1. Evolution stages: Basic → Stage 1 → Stage 2
  2. Evolution as state transition paths
  3. Turn-based restrictions (can't evolve first turn or turn played)
  4. Rare Candy skip (Basic → Stage 2)
  5. BREAK / Mega / VMAX evolution rules
  6. Devolution (Devolving Spray)

-/

namespace EvolutionMechanics

-- ============================================================
-- §1  Core types
-- ============================================================

/-- Evolution stages. -/
inductive Stage where
  | basic | stage1 | stage2
  | mega | break_ | vmax | vstar
deriving DecidableEq, Repr, BEq

/-- A Pokémon card for evolution purposes. -/
structure PokemonCard where
  name     : String
  stage    : Stage
  evolvesFrom : Option String
  hp       : Nat
deriving DecidableEq, Repr

/-- Game phase tracking. -/
structure TurnInfo where
  globalTurn   : Nat      -- 0 = first turn of game
  turnPlayed   : Nat      -- turn this Pokémon entered play
deriving DecidableEq, Repr
-- ============================================================
-- §3  Evolution state
-- ============================================================

/-- State of a Pokémon in play. -/
structure InPlayPokemon where
  card       : PokemonCard
  turnPlayed : Nat
  prevStages : List PokemonCard   -- previous evolution cards beneath
deriving DecidableEq, Repr

/-- The evolution state: current Pokémon + turn info. -/
structure EvoState where
  pokemon   : InPlayPokemon
  turnNow   : Nat
deriving DecidableEq, Repr

-- ============================================================
-- §4  Evolution predicates
-- ============================================================

/-- Can a Pokémon evolve on this turn? Must not be first global turn,
    and must have been in play for at least one full turn. -/
def canEvolveThisTurn (st : EvoState) : Prop :=
  st.turnNow ≥ 1 ∧ st.turnNow > st.pokemon.turnPlayed

/-- Normal evolution: stage must match and name must match evolvesFrom. -/
def isValidEvolution (current : PokemonCard) (evo : PokemonCard) : Prop :=
  (current.stage = Stage.basic ∧ evo.stage = Stage.stage1 ∧ evo.evolvesFrom = some current.name) ∨
  (current.stage = Stage.stage1 ∧ evo.stage = Stage.stage2 ∧ evo.evolvesFrom = some current.name)

/-- Rare Candy: skip Stage 1, evolve Basic directly to Stage 2. -/
def isRareCandyValid (current : PokemonCard) (target : PokemonCard) : Prop :=
  current.stage = Stage.basic ∧ target.stage = Stage.stage2

/-- BREAK evolution: Stage 1 or Stage 2 → BREAK. -/
def isBreakEvolution (current : PokemonCard) (evo : PokemonCard) : Prop :=
  (current.stage = Stage.stage1 ∨ current.stage = Stage.stage2) ∧
  evo.stage = Stage.break_ ∧ evo.evolvesFrom = some current.name

/-- Mega evolution: Basic EX → Mega (ends turn). -/
def isMegaEvolution (current : PokemonCard) (evo : PokemonCard) : Prop :=
  current.stage = Stage.basic ∧ evo.stage = Stage.mega ∧
  evo.evolvesFrom = some current.name

/-- VMAX evolution: V → VMAX. -/
def isVMAXEvolution (current : PokemonCard) (evo : PokemonCard) : Prop :=
  current.stage = Stage.basic ∧ evo.stage = Stage.vmax ∧
  evo.evolvesFrom = some current.name

-- ============================================================
-- §5  Example cards
-- ============================================================

def charmander : PokemonCard := ⟨"Charmander", .basic, none, 70⟩
def charmeleon : PokemonCard := ⟨"Charmeleon", .stage1, some "Charmander", 90⟩
def charizard  : PokemonCard := ⟨"Charizard", .stage2, some "Charmeleon", 170⟩
def charizardBreak : PokemonCard := ⟨"Charizard BREAK", .break_, some "Charizard", 170⟩
def charizardMega : PokemonCard := ⟨"M Charizard EX", .mega, some "Charizard EX", 220⟩
def charizardEX : PokemonCard := ⟨"Charizard EX", .basic, none, 180⟩
def charizardV : PokemonCard := ⟨"Charizard V", .basic, none, 220⟩
def charizardVMAX : PokemonCard := ⟨"Charizard VMAX", .vmax, some "Charizard V", 330⟩
-- ============================================================
-- §7  Evolution chain theorems
-- ============================================================

/-- Theorem 5: Charmander → Charmeleon is valid evolution. -/
theorem charmander_to_charmeleon :
    isValidEvolution charmander charmeleon := by
  left; exact ⟨rfl, rfl, rfl⟩

/-- Theorem 6: Charmeleon → Charizard is valid evolution. -/
theorem charmeleon_to_charizard :
    isValidEvolution charmeleon charizard := by
  right; exact ⟨rfl, rfl, rfl⟩

/-- Theorem 7: Charmander → Charizard is NOT a valid normal evolution
    (skips a stage). -/
theorem charmander_to_charizard_invalid :
    ¬ isValidEvolution charmander charizard := by
  intro h
  cases h with
  | inl h => exact absurd h.2.1 (by decide)
  | inr h => exact absurd h.1 (by decide)

/-- Theorem 8: Rare Candy lets Charmander → Charizard. -/
theorem rare_candy_charmander_charizard :
    isRareCandyValid charmander charizard := by
  exact ⟨rfl, rfl⟩

/-- Theorem 9: Rare Candy doesn't work on Stage 1. -/
theorem rare_candy_stage1_invalid :
    ¬ isRareCandyValid charmeleon charizard := by
  intro ⟨h, _⟩; exact absurd h (by decide)

-- ============================================================
-- §8  Turn restriction theorems
-- ============================================================

def exampleState0 : EvoState := ⟨⟨charmander, 0, []⟩, 0⟩
def exampleState1 : EvoState := ⟨⟨charmander, 0, []⟩, 1⟩
def exampleStateSameTurn : EvoState := ⟨⟨charmander, 2, []⟩, 2⟩

/-- Theorem 10: Can't evolve on first turn of game. -/
theorem no_evolve_first_turn : ¬ canEvolveThisTurn exampleState0 := by
  intro ⟨h, _⟩; simp [exampleState0] at h

/-- Theorem 11: Can evolve on turn 1 if played on turn 0. -/
theorem can_evolve_turn1 : canEvolveThisTurn exampleState1 := by
  simp [canEvolveThisTurn, exampleState1]

/-- Theorem 12: Can't evolve same turn played. -/
theorem no_evolve_same_turn : ¬ canEvolveThisTurn exampleStateSameTurn := by
  intro ⟨_, h⟩; simp [exampleStateSameTurn] at h

/-- Theorem 13: If turnNow > turnPlayed and turnNow ≥ 1, can evolve. -/
theorem evolve_condition (st : EvoState)
    (h1 : st.turnNow ≥ 1) (h2 : st.turnNow > st.pokemon.turnPlayed) :
    canEvolveThisTurn st := ⟨h1, h2⟩

-- ============================================================
-- §9  BREAK / Mega / VMAX evolution theorems
-- ============================================================

/-- Theorem 14: Charizard → Charizard BREAK is valid BREAK evolution. -/
theorem charizard_break_valid :
    isBreakEvolution charizard charizardBreak := by
  exact ⟨Or.inr rfl, rfl, rfl⟩

/-- Theorem 15: Basic can't BREAK evolve. -/
theorem basic_cant_break (evo : PokemonCard)
    (h : isBreakEvolution charmander evo) : False := by
  obtain ⟨h1, _, _⟩ := h
  cases h1 with
  | inl h => exact absurd h (by decide)
  | inr h => exact absurd h (by decide)

/-- Theorem 16: Charizard V → Charizard VMAX is valid VMAX evolution. -/
theorem charizard_vmax_valid :
    isVMAXEvolution charizardV charizardVMAX := by
  exact ⟨rfl, rfl, rfl⟩

/-- Theorem 17: VMAX requires the base to be Basic (V). -/
theorem vmax_requires_basic (current evo : PokemonCard)
    (h : isVMAXEvolution current evo) : current.stage = Stage.basic :=
  h.1

-- ============================================================
-- §10  Evolution chain paths
-- ============================================================


-- ============================================================
-- §11  Devolution (Devolving Spray)
-- ============================================================

/-- Devolution: strip the top evolution card, returning to previous stage. -/
def devolve (p : InPlayPokemon) : Option InPlayPokemon :=
  match p.prevStages with
  | []     => none
  | c :: rest => some ⟨c, p.turnPlayed, rest⟩

def evolvedCharmeleon : InPlayPokemon :=
  ⟨charmeleon, 0, [charmander]⟩

def evolvedCharizard : InPlayPokemon :=
  ⟨charizard, 0, [charmeleon, charmander]⟩

/-- Theorem 21: Devolving Charmeleon returns Charmander. -/
theorem devolve_charmeleon :
    devolve evolvedCharmeleon = some ⟨charmander, 0, []⟩ := rfl

/-- Theorem 22: Devolving Charizard returns Charmeleon (with Charmander beneath). -/
theorem devolve_charizard :
    devolve evolvedCharizard = some ⟨charmeleon, 0, [charmander]⟩ := rfl

/-- Theorem 23: Can't devolve a basic Pokémon (no previous stages). -/
theorem cant_devolve_basic : devolve ⟨charmander, 0, []⟩ = none := rfl

/-- Theorem 24: Double devolution brings Stage 2 back to Basic. -/
theorem double_devolve :
    (devolve evolvedCharizard).bind devolve = some ⟨charmander, 0, []⟩ := rfl

-- ============================================================
-- §12  Devolution as path inversion (symm)
-- ============================================================


-- ============================================================
-- §13  congrArg / transport through evolution
-- ============================================================

/-- HP lookup function. -/
def hpOf : PokemonCard → Nat := PokemonCard.hp

/-- Theorem 26: congrArg preserves HP through equal cards. -/
theorem hp_congr (c1 c2 : PokemonCard) (h : c1 = c2) :
    hpOf c1 = hpOf c2 :=
  congrArg hpOf h

/-- Stage extraction. -/
def stageOf : PokemonCard → Stage := PokemonCard.stage

/-- Theorem 27: congrArg preserves stage through equal cards. -/
theorem stage_congr (c1 c2 : PokemonCard) (h : c1 = c2) :
    stageOf c1 = stageOf c2 :=
  congrArg stageOf h

/-- Theorem 28: Transitivity of stage equality via trans. -/
theorem stage_trans (c1 c2 c3 : PokemonCard)
    (h1 : stageOf c1 = stageOf c2) (h2 : stageOf c2 = stageOf c3) :
    stageOf c1 = stageOf c3 :=
  h1.trans h2

/-- Theorem 29: Symmetry of stage equality. -/
theorem stage_symm (c1 c2 : PokemonCard) (h : stageOf c1 = stageOf c2) :
    stageOf c2 = stageOf c1 :=
  h.symm

/-- Theorem 30: Evolution strictly increases stage ordinal. -/
def stageOrd : Stage → Nat
  | .basic  => 0
  | .stage1 => 1
  | .stage2 => 2
  | .break_ => 3
  | .mega   => 3
  | .vmax   => 3
  | .vstar  => 3

/-- Theorem 30: Normal evolution increases stage ordinal. -/
theorem valid_evo_increases_ord (c e : PokemonCard)
    (h : isValidEvolution c e) : stageOrd c.stage < stageOrd e.stage := by
  cases h with
  | inl h => obtain ⟨hc, he, _⟩ := h; rw [hc, he]; decide
  | inr h => obtain ⟨hc, he, _⟩ := h; rw [hc, he]; decide

end EvolutionMechanics
