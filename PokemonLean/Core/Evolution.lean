/-
  PokemonLean / Core / Evolution.lean

  Pokémon TCG evolution mechanics formalised in Lean 4.
  Self-contained: defines Stage, evolution rules, Rare Candy,
  BREAK Evolution, Mega Evolution, VMAX inline.

  All proofs are sorry-free.  30 theorems.
-/

namespace PokemonLean.Core.Evolution

-- ============================================================
-- §1  Core Types (self-contained)
-- ============================================================

/-- Evolution stage in Pokémon TCG. -/
inductive Stage where
  | basic   : Stage
  | stage1  : Stage
  | stage2  : Stage
  | break_  : Stage   -- BREAK evolution
  | mega    : Stage   -- Mega Evolution (from EX)
  | vmax    : Stage   -- VMAX (from V)
  | vstar   : Stage   -- VSTAR (from V)
  | ex      : Stage   -- Pokémon-EX (basic, but can Mega evolve)
  | v       : Stage   -- Pokémon V (basic, can VMAX/VSTAR)
  deriving DecidableEq, Repr

/-- A Pokémon card with evolution data. -/
structure PokemonCard where
  name        : String
  stage       : Stage
  evolvesFrom : Option String
  hp          : Nat
  deriving DecidableEq, Repr

/-- A Pokémon in play with turn tracking. -/
structure InPlayPokemon where
  card          : PokemonCard
  turnPlayed    : Nat
  evolvedThisTurn : Bool
  turnsInPlay   : Nat
  deriving DecidableEq, Repr

-- ============================================================
-- §2  Sample Cards
-- ============================================================

def charmander   : PokemonCard := ⟨"Charmander",   .basic,  none,                 70⟩
def charmeleon   : PokemonCard := ⟨"Charmeleon",    .stage1, some "Charmander",    90⟩
def charizard    : PokemonCard := ⟨"Charizard",     .stage2, some "Charmeleon",   150⟩
def charizardBrk : PokemonCard := ⟨"Charizard BREAK", .break_, some "Charizard", 170⟩

def ralts        : PokemonCard := ⟨"Ralts",         .basic,  none,                60⟩
def kirlia       : PokemonCard := ⟨"Kirlia",        .stage1, some "Ralts",        80⟩
def gardevoir    : PokemonCard := ⟨"Gardevoir",     .stage2, some "Kirlia",      130⟩

def mewtwoEX     : PokemonCard := ⟨"Mewtwo-EX",    .ex,     none,               170⟩
def megaMewtwo   : PokemonCard := ⟨"M Mewtwo-EX",  .mega,   some "Mewtwo-EX",   210⟩

def eternatusV    : PokemonCard := ⟨"Eternatus V",    .v,    none,               220⟩
def eternatusVMAX : PokemonCard := ⟨"Eternatus VMAX", .vmax, some "Eternatus V", 340⟩

def arceus_V      : PokemonCard := ⟨"Arceus V",       .v,    none,               220⟩
def arceusVSTAR   : PokemonCard := ⟨"Arceus VSTAR",   .vstar, some "Arceus V",   280⟩

-- ============================================================
-- §3  Stage Ordering (Partial Order)
-- ============================================================

/-- Numeric rank for stage ordering (standard evolution track only). -/
def stageRank : Stage → Nat
  | .basic  => 0
  | .stage1 => 1
  | .stage2 => 2
  | .break_ => 3
  | .ex     => 0   -- treated as basic-level for evolution
  | .v      => 0   -- treated as basic-level for evolution
  | .mega   => 1   -- one step above EX
  | .vmax   => 1   -- one step above V
  | .vstar  => 1   -- one step above V

/-- Stage ordering: s₁ ≤ s₂ iff rank s₁ ≤ rank s₂. -/
def stageLe (s₁ s₂ : Stage) : Bool :=
  stageRank s₁ ≤ stageRank s₂

-- ============================================================
-- §4  Evolution Rules
-- ============================================================

/-- Normal evolution legality check.
    Requirements:
    - evolvesFrom matches the in-play card name
    - Not first turn of the game (gameTurn > 1)
    - Pokémon has been in play at least 1 turn
    - Pokémon hasn't already evolved this turn -/
def canEvolve (gameTurn : Nat) (target : InPlayPokemon) (evoCard : PokemonCard) : Prop :=
  gameTurn > 1 ∧
  evoCard.evolvesFrom = some target.card.name ∧
  target.turnsInPlay ≥ 1 ∧
  target.evolvedThisTurn = false

def canEvolveBool (gameTurn : Nat) (target : InPlayPokemon) (evoCard : PokemonCard) : Bool :=
  gameTurn > 1 &&
  evoCard.evolvesFrom == some target.card.name &&
  target.turnsInPlay ≥ 1 &&
  !target.evolvedThisTurn

/-- Apply evolution: replace the card, mark evolved this turn. -/
def evolve (target : InPlayPokemon) (evoCard : PokemonCard) : InPlayPokemon :=
  { target with card := evoCard, evolvedThisTurn := true }

-- ============================================================
-- §5  Rare Candy
-- ============================================================

/-- Rare Candy: skip Stage 1, go Basic → Stage 2.
    Requires: not first turn of game, target is Basic,
    target has been in play ≥ 1 turn, target not evolved this turn,
    the Stage 2 card is indeed a Stage 2. -/
def canRareCandy (gameTurn : Nat) (target : InPlayPokemon) (stage2Card : PokemonCard) : Prop :=
  gameTurn > 1 ∧
  target.card.stage = .basic ∧
  stage2Card.stage = .stage2 ∧
  target.turnsInPlay ≥ 1 ∧
  target.evolvedThisTurn = false

def canRareCandyBool (gameTurn : Nat) (target : InPlayPokemon) (stage2Card : PokemonCard) : Bool :=
  gameTurn > 1 &&
  target.card.stage == .basic &&
  stage2Card.stage == .stage2 &&
  target.turnsInPlay ≥ 1 &&
  !target.evolvedThisTurn

/-- Apply Rare Candy evolution. -/
def applyRareCandy (target : InPlayPokemon) (stage2Card : PokemonCard) : InPlayPokemon :=
  { target with card := stage2Card, evolvedThisTurn := true }

-- ============================================================
-- §6  BREAK Evolution
-- ============================================================

/-- BREAK Evolution: on top of matching Stage 2 Pokémon.
    The BREAK card keeps the previous attacks (modelled by keeping reference). -/
def canBreakEvolve (gameTurn : Nat) (target : InPlayPokemon) (breakCard : PokemonCard) : Prop :=
  gameTurn > 1 ∧
  breakCard.stage = .break_ ∧
  breakCard.evolvesFrom = some target.card.name ∧
  target.turnsInPlay ≥ 1 ∧
  target.evolvedThisTurn = false

/-- BREAK evolution preserves underlying HP (uses BREAK HP, which is higher). -/
def applyBreakEvolution (target : InPlayPokemon) (breakCard : PokemonCard) : InPlayPokemon :=
  { target with card := breakCard, evolvedThisTurn := true }

-- ============================================================
-- §7  Mega Evolution
-- ============================================================

/-- Mega Evolution: from Pokémon-EX, ends your turn (unless Spirit Link attached). -/
structure MegaEvoResult where
  pokemon : InPlayPokemon
  endsTurn : Bool
  deriving DecidableEq, Repr

def canMegaEvolve (gameTurn : Nat) (target : InPlayPokemon) (megaCard : PokemonCard) : Prop :=
  gameTurn > 1 ∧
  target.card.stage = .ex ∧
  megaCard.stage = .mega ∧
  megaCard.evolvesFrom = some target.card.name ∧
  target.turnsInPlay ≥ 1 ∧
  target.evolvedThisTurn = false

def applyMegaEvolution (target : InPlayPokemon) (megaCard : PokemonCard)
    (hasSpiritLink : Bool) : MegaEvoResult :=
  { pokemon := { target with card := megaCard, evolvedThisTurn := true },
    endsTurn := !hasSpiritLink }

-- ============================================================
-- §8  VMAX / VSTAR Evolution
-- ============================================================

def canVMaxEvolve (gameTurn : Nat) (target : InPlayPokemon) (vmaxCard : PokemonCard) : Prop :=
  gameTurn > 1 ∧
  target.card.stage = .v ∧
  vmaxCard.stage = .vmax ∧
  vmaxCard.evolvesFrom = some target.card.name ∧
  target.turnsInPlay ≥ 1 ∧
  target.evolvedThisTurn = false

def canVStarEvolve (gameTurn : Nat) (target : InPlayPokemon) (vstarCard : PokemonCard) : Prop :=
  gameTurn > 1 ∧
  target.card.stage = .v ∧
  vstarCard.stage = .vstar ∧
  vstarCard.evolvesFrom = some target.card.name ∧
  target.turnsInPlay ≥ 1 ∧
  target.evolvedThisTurn = false

-- ============================================================
-- §9  Evolution Step and Path
-- ============================================================

/-- A single evolution step. -/
inductive EvoStep : PokemonCard → PokemonCard → Prop where
  | normal (a b : PokemonCard) : b.evolvesFrom = some a.name → EvoStep a b

/-- Multi-step evolution path. -/
inductive EvoPath : PokemonCard → PokemonCard → Prop where
  | refl  (p : PokemonCard) : EvoPath p p
  | step  {a b c : PokemonCard} : EvoStep a b → EvoPath b c → EvoPath a c

theorem EvoPath.trans {a b c : PokemonCard} : EvoPath a b → EvoPath b c → EvoPath a c := by
  intro p q
  induction p with
  | refl _ => exact q
  | step s _ ih => exact .step s (ih q)

def EvoPath.single {a b : PokemonCard} (h : EvoStep a b) : EvoPath a b :=
  .step h (.refl _)

-- ============================================================
-- §10  Evolution Theorems
-- ============================================================

/-- Theorem 1: Can't evolve on the first turn of the game. -/
theorem no_evolve_first_turn (target : InPlayPokemon) (evoCard : PokemonCard) :
    ¬canEvolve 1 target evoCard := by
  intro ⟨h, _⟩; omega

/-- Theorem 2: Can't evolve if Pokémon was just played (0 turns in play). -/
theorem no_evolve_just_played (gameTurn : Nat) (target : InPlayPokemon) (evoCard : PokemonCard)
    (h : target.turnsInPlay = 0) :
    ¬canEvolve gameTurn target evoCard := by
  intro ⟨_, _, hTurns, _⟩; omega

/-- Theorem 3: Can't evolve if already evolved this turn. -/
theorem no_double_evolve (gameTurn : Nat) (target : InPlayPokemon) (evoCard : PokemonCard)
    (h : target.evolvedThisTurn = true) :
    ¬canEvolve gameTurn target evoCard := by
  intro ⟨_, _, _, hFalse⟩
  rw [h] at hFalse; exact absurd hFalse (by decide)

/-- Theorem 4: Evolution changes the card. -/
theorem evolve_changes_card (target : InPlayPokemon) (evoCard : PokemonCard) :
    (evolve target evoCard).card = evoCard := by
  rfl

/-- Theorem 5: Evolution marks evolved this turn. -/
theorem evolve_marks_evolved (target : InPlayPokemon) (evoCard : PokemonCard) :
    (evolve target evoCard).evolvedThisTurn = true := by
  rfl

/-- Theorem 6: At most one evolution per turn per Pokémon — after evolving,
    canEvolve is false for any further card. -/
theorem one_evolution_per_turn (target : InPlayPokemon) (evo1 evo2 : PokemonCard)
    (gameTurn : Nat) :
    ¬canEvolve gameTurn (evolve target evo1) evo2 := by
  intro ⟨_, _, _, hFalse⟩
  simp [evolve] at hFalse

/-- Theorem 7: Rare Candy requires basic target. -/
theorem rare_candy_needs_basic (gameTurn : Nat) (target : InPlayPokemon) (s2 : PokemonCard)
    (h : target.card.stage ≠ .basic) :
    ¬canRareCandy gameTurn target s2 := by
  intro ⟨_, hBasic, _⟩; exact h hBasic

/-- Theorem 8: Rare Candy requires Stage 2 destination. -/
theorem rare_candy_needs_stage2 (gameTurn : Nat) (target : InPlayPokemon) (s2 : PokemonCard)
    (h : s2.stage ≠ .stage2) :
    ¬canRareCandy gameTurn target s2 := by
  intro ⟨_, _, hS2, _⟩; exact h hS2

/-- Theorem 9: Can't Rare Candy on first turn. -/
theorem no_rare_candy_first_turn (target : InPlayPokemon) (s2 : PokemonCard) :
    ¬canRareCandy 1 target s2 := by
  intro ⟨h, _⟩; omega

/-- Theorem 10: Rare Candy result is Stage 2. -/
theorem rare_candy_result_stage2 (target : InPlayPokemon) (s2 : PokemonCard)
    (h : s2.stage = .stage2) :
    (applyRareCandy target s2).card.stage = .stage2 := by
  simp [applyRareCandy]; exact h

/-- Theorem 11: BREAK requires the base to be the correct Pokémon. -/
theorem break_requires_name_match (gameTurn : Nat) (target : InPlayPokemon) (brk : PokemonCard)
    (h : brk.evolvesFrom ≠ some target.card.name) :
    ¬canBreakEvolve gameTurn target brk := by
  intro ⟨_, _, hMatch, _⟩; exact h hMatch

/-- Theorem 12: BREAK requires a BREAK card. -/
theorem break_requires_break_stage (gameTurn : Nat) (target : InPlayPokemon) (brk : PokemonCard)
    (h : brk.stage ≠ .break_) :
    ¬canBreakEvolve gameTurn target brk := by
  intro ⟨_, hBrk, _⟩; exact h hBrk

/-- Theorem 13: Mega Evolution requires EX base. -/
theorem mega_requires_ex (gameTurn : Nat) (target : InPlayPokemon) (mega : PokemonCard)
    (h : target.card.stage ≠ .ex) :
    ¬canMegaEvolve gameTurn target mega := by
  intro ⟨_, hEx, _⟩; exact h hEx

/-- Theorem 14: Mega Evolution without Spirit Link ends turn. -/
theorem mega_no_spirit_link_ends_turn (target : InPlayPokemon) (mega : PokemonCard) :
    (applyMegaEvolution target mega false).endsTurn = true := by
  rfl

/-- Theorem 15: Mega Evolution with Spirit Link does NOT end turn. -/
theorem mega_spirit_link_continues (target : InPlayPokemon) (mega : PokemonCard) :
    (applyMegaEvolution target mega true).endsTurn = false := by
  rfl

/-- Theorem 16: VMAX requires V base. -/
theorem vmax_requires_v (gameTurn : Nat) (target : InPlayPokemon) (vmax : PokemonCard)
    (h : target.card.stage ≠ .v) :
    ¬canVMaxEvolve gameTurn target vmax := by
  intro ⟨_, hV, _⟩; exact h hV

/-- Theorem 17: VSTAR requires V base. -/
theorem vstar_requires_v (gameTurn : Nat) (target : InPlayPokemon) (vstar : PokemonCard)
    (h : target.card.stage ≠ .v) :
    ¬canVStarEvolve gameTurn target vstar := by
  intro ⟨_, hV, _⟩; exact h hV

-- ============================================================
-- §11  Evolution Path Theorems
-- ============================================================

/-- Theorem 18: Charmander → Charmeleon is one step. -/
theorem charmander_to_charmeleon : EvoStep charmander charmeleon :=
  .normal _ _ rfl

/-- Theorem 19: Charmeleon → Charizard is one step. -/
theorem charmeleon_to_charizard : EvoStep charmeleon charizard :=
  .normal _ _ rfl

/-- Theorem 20: Charmander → Charizard is a 2-step path. -/
theorem charmander_to_charizard_path : EvoPath charmander charizard :=
  .step (.normal charmander charmeleon rfl) (.step (.normal charmeleon charizard rfl) (.refl _))

/-- Theorem 21: Charizard → Charizard BREAK path exists. -/
theorem charizard_break_path : EvoPath charizard charizardBrk :=
  EvoPath.single (.normal _ _ rfl)

/-- Theorem 22: Full Charmander line is a path Basic→Stage1→Stage2→BREAK. -/
theorem charmander_full_line : EvoPath charmander charizardBrk :=
  EvoPath.trans charmander_to_charizard_path charizard_break_path

/-- Theorem 23: Ralts → Kirlia → Gardevoir is a 2-step path. -/
theorem ralts_to_gardevoir_path : EvoPath ralts gardevoir :=
  .step (.normal ralts kirlia rfl) (.step (.normal kirlia gardevoir rfl) (.refl _))

/-- Theorem 24: Mewtwo-EX → M Mewtwo-EX is one step. -/
theorem mewtwo_mega_step : EvoStep mewtwoEX megaMewtwo :=
  .normal _ _ rfl

/-- Theorem 25: Eternatus V → Eternatus VMAX is one step. -/
theorem eternatus_vmax_step : EvoStep eternatusV eternatusVMAX :=
  .normal _ _ rfl

/-- Theorem 26: Arceus V → Arceus VSTAR is one step. -/
theorem arceus_vstar_step : EvoStep arceus_V arceusVSTAR :=
  .normal _ _ rfl

-- ============================================================
-- §12  Stage Ordering Theorems
-- ============================================================

/-- Theorem 27: Basic ≤ Stage1 ≤ Stage2 ≤ BREAK in stage ordering. -/
theorem stage_ordering_chain :
    stageLe .basic .stage1 = true ∧
    stageLe .stage1 .stage2 = true ∧
    stageLe .stage2 .break_ = true := by
  exact ⟨rfl, rfl, rfl⟩

/-- Theorem 28: Stage ordering is reflexive. -/
theorem stage_le_refl (s : Stage) : stageLe s s = true := by
  cases s <;> rfl

/-- Theorem 29: Stage ordering is transitive (for the standard track). -/
theorem stage_le_trans (a b c : Stage)
    (hab : stageLe a b = true) (hbc : stageLe b c = true) :
    stageLe a c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [stageLe, stageRank]
  all_goals omega

/-- Theorem 30: Evolution path refl is left identity for trans. -/
theorem evo_path_refl_left {a b : PokemonCard} (p : EvoPath a b) :
    (EvoPath.refl a).trans p = p := by rfl

end PokemonLean.Core.Evolution
