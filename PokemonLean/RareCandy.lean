/-
  PokemonLean / RareCandy.lean

  Rare Candy deep mechanics formalised in Lean 4.
  Covers: skip Stage 1 evolution, respect evolution lines,
  can't use on first turn, can't use on turn played,
  BREAK evolution from Stage 2, Rare Candy + Devolution Spray combo,
  deck search mechanics.

  All proofs are sorry‑free. Uses computational paths for
  game-state transitions (each rule application = path step).
-/

namespace RareCandy

-- ============================================================
-- §1  Computational Paths
-- ============================================================

inductive Step (α : Type) : α → α → Type where
  | mk : (name : String) → (a b : α) → Step α a b

inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

def Path.trans {α : Type} {a b c : α}
    (p : Path α a b) (q : Path α b c) : Path α a c :=
  match p with
  | .nil _ => q
  | .cons s rest => .cons s (rest.trans q)

def Path.length {α : Type} {a b : α} : Path α a b → Nat
  | .nil _ => 0
  | .cons _ rest => 1 + rest.length

def Step.symm {α : Type} {a b : α} : Step α a b → Step α b a
  | .mk name a b => .mk (name ++ "⁻¹") b a

def Path.symm {α : Type} {a b : α} : Path α a b → Path α b a
  | .nil a => .nil a
  | .cons s rest => rest.symm.trans (.cons s.symm (.nil _))

def Path.single {α : Type} {a b : α} (s : Step α a b) : Path α a b :=
  .cons s (.nil b)

-- ============================================================
-- §2  Pokemon TCG types
-- ============================================================

inductive Stage where
  | basic   : Stage
  | stage1  : Stage
  | stage2  : Stage
  | break_  : Stage
deriving DecidableEq, Repr

structure Pokemon where
  name       : String
  stage      : Stage
  evolvesFrom : Option String
  hp         : Nat
deriving DecidableEq, Repr

structure InPlayPokemon where
  card       : Pokemon
  turnPlayed : Nat
  hasEvolved : Bool
deriving DecidableEq, Repr

structure GameState where
  currentTurn   : Nat
  isFirstTurn   : Bool
  hand          : List Pokemon
  deck          : List Pokemon
  bench         : List InPlayPokemon
  active        : Option InPlayPokemon
  rareCandyUsed : Bool
deriving Repr

-- ============================================================
-- §3  Sample cards
-- ============================================================

def charmander : Pokemon := ⟨"Charmander", .basic, none, 70⟩
def charmeleon : Pokemon := ⟨"Charmeleon", .stage1, some "Charmander", 90⟩
def charizard  : Pokemon := ⟨"Charizard", .stage2, some "Charmeleon", 150⟩
def charizardBreak : Pokemon := ⟨"Charizard BREAK", .break_, some "Charizard", 170⟩

def ralts     : Pokemon := ⟨"Ralts", .basic, none, 60⟩
def kirlia    : Pokemon := ⟨"Kirlia", .stage1, some "Ralts", 80⟩
def gardevoir : Pokemon := ⟨"Gardevoir", .stage2, some "Kirlia", 130⟩

-- ============================================================
-- §4  Evolution line validation
-- ============================================================

def inEvolutionLine (basic : Pokemon) (stage1 : Pokemon) (stage2 : Pokemon) : Bool :=
  basic.stage == .basic &&
  stage1.stage == .stage1 &&
  stage2.stage == .stage2 &&
  stage1.evolvesFrom == some basic.name &&
  stage2.evolvesFrom == some stage1.name

-- ============================================================
-- §5  Rare Candy legality
-- ============================================================

def canUseRareCandy (gs : GameState) (target : InPlayPokemon) (stage2 : Pokemon) : Prop :=
  gs.isFirstTurn = false ∧
  target.card.stage = .basic ∧
  stage2.stage = .stage2 ∧
  stage2 ∈ gs.hand ∧
  target.turnPlayed < gs.currentTurn ∧
  target.hasEvolved = false

def canUseRareCandyBool (gs : GameState) (target : InPlayPokemon) (stage2 : Pokemon) : Bool :=
  !gs.isFirstTurn &&
  target.card.stage == .basic &&
  stage2.stage == .stage2 &&
  stage2 ∈ gs.hand &&
  decide (target.turnPlayed < gs.currentTurn) &&
  !target.hasEvolved

def applyRareCandy (gs : GameState) (target : InPlayPokemon) (stage2 : Pokemon) : GameState :=
  let evolved : InPlayPokemon := ⟨stage2, target.turnPlayed, true⟩
  let newBench := gs.bench.map fun p => if p == target then evolved else p
  let newActive := gs.active.map fun p => if p == target then evolved else p
  { gs with
    hand := gs.hand.erase stage2,
    bench := newBench,
    active := newActive,
    rareCandyUsed := true }

-- ============================================================
-- §6  Game state transition steps
-- ============================================================

inductive GameStep : GameState → GameState → Prop where
  | useRareCandy (gs : GameState) (target : InPlayPokemon) (stage2 : Pokemon)
      (hleg : canUseRareCandy gs target stage2) :
      GameStep gs (applyRareCandy gs target stage2)

inductive GamePath : GameState → GameState → Prop where
  | refl (gs : GameState) : GamePath gs gs
  | step {g₁ g₂ g₃ : GameState} : GameStep g₁ g₂ → GamePath g₂ g₃ → GamePath g₁ g₃

/-- Theorem 1: Transitivity of game paths. -/
theorem GamePath.trans {a b c : GameState}
    (p : GamePath a b) (q : GamePath b c) : GamePath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact .step s (ih q)

-- ============================================================
-- §7  Core Rare Candy theorems
-- ============================================================

/-- Theorem 2: Rare Candy can't be used on the first turn. -/
theorem no_rare_candy_first_turn (gs : GameState) (target : InPlayPokemon) (s2 : Pokemon)
    (hFirst : gs.isFirstTurn = true) :
    ¬canUseRareCandy gs target s2 := by
  intro ⟨h, _⟩
  rw [hFirst] at h
  exact absurd h (by decide)

/-- Theorem 3: Rare Candy can't target a Stage 1. -/
theorem no_rare_candy_on_stage1 (gs : GameState) (target : InPlayPokemon) (s2 : Pokemon)
    (hStage : target.card.stage = .stage1) :
    ¬canUseRareCandy gs target s2 := by
  intro ⟨_, hBasic, _⟩
  rw [hStage] at hBasic
  exact absurd hBasic (by decide)

/-- Theorem 4: Rare Candy can't target a Stage 2. -/
theorem no_rare_candy_on_stage2_target (gs : GameState) (target : InPlayPokemon) (s2 : Pokemon)
    (hStage : target.card.stage = .stage2) :
    ¬canUseRareCandy gs target s2 := by
  intro ⟨_, hBasic, _⟩
  rw [hStage] at hBasic
  exact absurd hBasic (by decide)

/-- Theorem 5: Rare Candy can't evolve to a Stage 1. -/
theorem rare_candy_needs_stage2 (gs : GameState) (target : InPlayPokemon) (s2 : Pokemon)
    (hNotS2 : s2.stage ≠ .stage2) :
    ¬canUseRareCandy gs target s2 := by
  intro ⟨_, _, hS2, _⟩
  exact hNotS2 hS2

/-- Theorem 6: Can't use Rare Candy on a Pokemon played this turn. -/
theorem no_rare_candy_same_turn (gs : GameState) (target : InPlayPokemon) (s2 : Pokemon)
    (hTurn : target.turnPlayed ≥ gs.currentTurn) :
    ¬canUseRareCandy gs target s2 := by
  intro ⟨_, _, _, _, hLt, _⟩
  omega

/-- Theorem 7: Can't use Rare Candy on already-evolved Pokemon. -/
theorem no_rare_candy_already_evolved (gs : GameState) (target : InPlayPokemon) (s2 : Pokemon)
    (hEvolved : target.hasEvolved = true) :
    ¬canUseRareCandy gs target s2 := by
  intro ⟨_, _, _, _, _, hFalse⟩
  rw [hEvolved] at hFalse
  exact absurd hFalse (by decide)

/-- Theorem 8: Rare Candy marks rareCandyUsed. -/
theorem rare_candy_marks_used (gs : GameState) (target : InPlayPokemon) (s2 : Pokemon) :
    (applyRareCandy gs target s2).rareCandyUsed = true := by
  simp [applyRareCandy]

-- ============================================================
-- §8  BREAK evolution rules
-- ============================================================

def canBreakEvolve (gs : GameState) (target : InPlayPokemon) (breakCard : Pokemon) : Prop :=
  gs.isFirstTurn = false ∧
  breakCard.stage = .break_ ∧
  target.card.stage = .stage2 ∧
  breakCard.evolvesFrom = some target.card.name ∧
  breakCard ∈ gs.hand ∧
  target.turnPlayed < gs.currentTurn ∧
  target.hasEvolved = false

/-- Theorem 9: BREAK can't be applied to a Basic. -/
theorem no_break_on_basic (gs : GameState) (target : InPlayPokemon) (b : Pokemon)
    (hBasic : target.card.stage = .basic) :
    ¬canBreakEvolve gs target b := by
  intro ⟨_, _, hS2, _⟩
  rw [hBasic] at hS2
  exact absurd hS2 (by decide)

/-- Theorem 10: BREAK can't be applied to a Stage 1. -/
theorem no_break_on_stage1 (gs : GameState) (target : InPlayPokemon) (b : Pokemon)
    (hStage1 : target.card.stage = .stage1) :
    ¬canBreakEvolve gs target b := by
  intro ⟨_, _, hS2, _⟩
  rw [hStage1] at hS2
  exact absurd hS2 (by decide)

/-- Theorem 11: BREAK requires a BREAK card. -/
theorem break_needs_break_card (gs : GameState) (target : InPlayPokemon) (b : Pokemon)
    (hNotBreak : b.stage ≠ .break_) :
    ¬canBreakEvolve gs target b := by
  intro ⟨_, hBr, _⟩
  exact hNotBreak hBr

-- ============================================================
-- §9  Devolution Spray combo
-- ============================================================

def devolvePokemon (p : InPlayPokemon) (prevCard : Pokemon) : InPlayPokemon :=
  ⟨prevCard, p.turnPlayed, true⟩

/-- Theorem 12: After devolving, the card changes. -/
theorem devolve_changes_card (p : InPlayPokemon) (prev : Pokemon)
    (hDiff : p.card ≠ prev) :
    (devolvePokemon p prev).card ≠ p.card := by
  simp [devolvePokemon]
  exact fun h => hDiff h.symm

/-- Theorem 13: Devolution preserves turn-played. -/
theorem devolve_preserves_turn (target : InPlayPokemon) (prev : Pokemon) :
    (devolvePokemon target prev).turnPlayed = target.turnPlayed := by
  simp [devolvePokemon]

/-- Theorem 14: Rare Candy + Devolution combo preserves turn. -/
theorem rare_candy_devolve_preserves_turn (target : InPlayPokemon) (s2 basic : Pokemon) :
    let evolved := InPlayPokemon.mk s2 target.turnPlayed true
    (devolvePokemon evolved basic).turnPlayed = target.turnPlayed := by
  simp [devolvePokemon]

-- ============================================================
-- §10  Deck search mechanics
-- ============================================================

def searchDeck (deck : List Pokemon) (name : String) : Option Pokemon :=
  deck.find? (·.name == name)

/-- Theorem 15: Searching empty deck finds nothing. -/
theorem search_empty_deck (name : String) : searchDeck [] name = none := rfl

/-- Theorem 16: If card matches, search finds it. -/
theorem search_finds_head (p : Pokemon) (rest : List Pokemon) (name : String)
    (hName : (p.name == name) = true) :
    searchDeck (p :: rest) name = some p := by
  simp [searchDeck, List.find?, hName]

-- ============================================================
-- §11  Evolution line paths
-- ============================================================

inductive EvoStep : Pokemon → Pokemon → Prop where
  | evolve (a b : Pokemon) : b.evolvesFrom = some a.name → EvoStep a b

inductive EvoPath : Pokemon → Pokemon → Prop where
  | refl (p : Pokemon) : EvoPath p p
  | step {a b c : Pokemon} : EvoStep a b → EvoPath b c → EvoPath a c

/-- Theorem 17: Transitivity of evolution paths. -/
theorem EvoPath.trans {a b c : Pokemon}
    (p : EvoPath a b) (q : EvoPath b c) : EvoPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact .step s (ih q)

/-- Theorem 18: Charmander → Charmeleon is one step. -/
theorem charmander_to_charmeleon : EvoStep charmander charmeleon :=
  .evolve _ _ rfl

/-- Theorem 19: Charmeleon → Charizard is one step. -/
theorem charmeleon_to_charizard : EvoStep charmeleon charizard :=
  .evolve _ _ rfl

/-- Theorem 20: Charmander → Charizard is a 2-step path. -/
theorem charmander_to_charizard_path : EvoPath charmander charizard :=
  .step charmander_to_charmeleon (.step charmeleon_to_charizard (.refl _))

/-- Theorem 21: Charizard → Charizard BREAK extends the path. -/
theorem charizard_to_break : EvoStep charizard charizardBreak :=
  .evolve _ _ rfl

/-- Theorem 22: Full path Charmander → Charizard BREAK (3 steps via trans). -/
theorem charmander_to_charizard_break : EvoPath charmander charizardBreak :=
  EvoPath.trans charmander_to_charizard_path (.step charizard_to_break (.refl _))

/-- Theorem 23: Ralts → Kirlia step. -/
theorem ralts_to_kirlia : EvoStep ralts kirlia :=
  .evolve _ _ rfl

/-- Theorem 24: Kirlia → Gardevoir step. -/
theorem kirlia_to_gardevoir : EvoStep kirlia gardevoir :=
  .evolve _ _ rfl

/-- Theorem 25: Ralts → Gardevoir is a 2-step path. -/
theorem ralts_to_gardevoir : EvoPath ralts gardevoir :=
  .step ralts_to_kirlia (.step kirlia_to_gardevoir (.refl _))

/-- Theorem 26: Path length for Charmander line. -/
theorem evo_path_length_charmander :
    let p := @Path.cons Pokemon _ _ _
      (.mk "evolve" charmander charmeleon)
      (.cons (.mk "evolve" charmeleon charizard) (.nil charizard))
    p.length = 2 := rfl

-- ============================================================
-- §12  Additional properties
-- ============================================================

/-- Theorem 27: Charmander is valid Rare Candy base for Charizard. -/
theorem charmander_valid_for_charizard :
    inEvolutionLine charmander charmeleon charizard = true := by native_decide

/-- Theorem 28: Ralts is valid Rare Candy base for Gardevoir. -/
theorem ralts_valid_for_gardevoir :
    inEvolutionLine ralts kirlia gardevoir = true := by native_decide

/-- Theorem 29: Can't use Rare Candy if stage2 not in hand. -/
theorem rare_candy_needs_in_hand (gs : GameState) (target : InPlayPokemon) (s2 : Pokemon)
    (hNotInHand : s2 ∉ gs.hand) :
    ¬canUseRareCandy gs target s2 := by
  intro ⟨_, _, _, hIn, _⟩
  exact hNotInHand hIn

/-- Theorem 30: After Rare Candy, evolved Pokemon's stage matches the Stage 2 card. -/
theorem rare_candy_evolves_stage (s2 : Pokemon) (target : InPlayPokemon)
    (hS2 : s2.stage = .stage2) :
    let evolved := InPlayPokemon.mk s2 target.turnPlayed true
    evolved.card.stage = .stage2 := by
  simp
  exact hS2

end RareCandy
