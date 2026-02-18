/-
  PokemonLean / Core / TurnLoop.lean

  Pokémon TCG full turn structure formalised in Lean 4.
  Self-contained: defines turn phases, main-phase actions,
  resource tracking, phase transitions, and the turn loop.

  Turn structure:
    DRAW PHASE: Draw 1 card (mandatory). If deck empty = lose.
    MAIN PHASE: Play Basics, evolve, attach energy (1×), play Trainers
                (Supporter 1×, Items ∞, Stadium replaces), abilities, retreat (1×).
    ATTACK PHASE: Declare attack, resolve, check KO, take prizes.
    BETWEEN TURNS: Poison, burn, sleep check, paralysis cure.

  All proofs are sorry-free.  36 theorems.
-/

namespace PokemonLean.Core.TurnLoop

-- ============================================================
-- §1  Core Types
-- ============================================================

/-- Coin flip. -/
inductive Coin where
  | heads | tails
  deriving DecidableEq, Repr

/-- Card kinds relevant to turn actions. -/
inductive CardKind where
  | basicPokemon
  | evolutionPokemon
  | supporter
  | item
  | stadium
  | tool
  | energy
  deriving DecidableEq, Repr

/-- A card. -/
structure Card where
  id   : Nat
  kind : CardKind
  deriving DecidableEq, Repr

-- ============================================================
-- §2  Turn Phases
-- ============================================================

/-- The four phases of a Pokémon TCG turn, in strict order. -/
inductive Phase where
  | draw          -- mandatory draw
  | main          -- play cards, abilities, retreat
  | attack        -- declare and resolve attack
  | betweenTurns  -- process conditions
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Numeric ordering of phases. -/
def Phase.ord : Phase → Nat
  | .draw         => 0
  | .main         => 1
  | .attack       => 2
  | .betweenTurns => 3

/-- Phase ordering: p1 comes before p2. -/
def Phase.lt (p1 p2 : Phase) : Bool :=
  p1.ord < p2.ord

/-- Phase ordering: p1 comes at or before p2. -/
def Phase.le (p1 p2 : Phase) : Bool :=
  p1.ord ≤ p2.ord

-- ============================================================
-- §3  Resource Tracking
-- ============================================================

/-- Per-turn resource tracking for the current player. -/
structure TurnResources where
  supporterPlayed : Bool
  energyAttached  : Bool
  retreated       : Bool
  gxUsed          : Bool
  vstarUsed       : Bool
  normalSummon    : Bool   -- whether a Pokémon was played to bench this turn
  deriving DecidableEq, Repr

/-- Fresh resources at the start of a turn. -/
def TurnResources.fresh : TurnResources where
  supporterPlayed := false
  energyAttached  := false
  retreated       := false
  gxUsed          := false
  vstarUsed       := false
  normalSummon    := false

-- ============================================================
-- §4  Player State (simplified for turn mechanics)
-- ============================================================

/-- Simplified player state for turn-phase modelling. -/
structure PlayerState where
  hand        : List Card
  deckSize    : Nat
  benchCount  : Nat
  hasActive   : Bool
  prizes      : Nat
  resources   : TurnResources
  deriving DecidableEq, Repr

-- ============================================================
-- §5  Turn State
-- ============================================================

/-- Full turn state: tracks who is playing, what phase, turn number, etc. -/
structure TurnState where
  currentPlayer : Nat     -- 0 or 1
  turnNumber    : Nat
  phase         : Phase
  isFirstTurn   : Bool    -- first turn of the game for going-first player
  resources     : TurnResources
  deriving DecidableEq, Repr

/-- Initial turn state for the very first turn. -/
def TurnState.initial (goingFirst : Nat) : TurnState where
  currentPlayer := goingFirst
  turnNumber := 1
  phase := .draw
  isFirstTurn := true
  resources := TurnResources.fresh

-- ============================================================
-- §6  Draw Phase
-- ============================================================

/-- Result of the draw phase. -/
inductive DrawResult where
  | success (drawnCard : Card) (remainingDeck : Nat)
  | deckout   -- cannot draw, player loses
  deriving DecidableEq, Repr

/-- Execute draw phase: draw 1 card from deck. -/
def executeDraw (deckSize : Nat) (topCard : Option Card) : DrawResult :=
  match deckSize, topCard with
  | 0, _          => .deckout
  | _ + 1, none   => .deckout
  | n + 1, some c => .success c n

/-- Whether draw is mandatory (always true). -/
def drawIsMandatory : Bool := true

-- ============================================================
-- §7  Main Phase Actions
-- ============================================================

/-- Actions available during the main phase. -/
inductive MainAction where
  | playBasicToBench
  | evolvePokemon
  | attachEnergy
  | playSupporter
  | playItem
  | playStadium
  | playTool
  | useAbility
  | retreat
  | endMainPhase
  deriving DecidableEq, Repr

/-- Check if a main action is currently legal given resources. -/
def MainAction.isLegal (action : MainAction) (res : TurnResources)
    (isFirstTurn : Bool) (benchCount : Nat) : Bool :=
  match action with
  | .playBasicToBench   => benchCount < 5
  | .evolvePokemon      => !isFirstTurn   -- can't evolve on first turn going first
  | .attachEnergy       => !res.energyAttached
  | .playSupporter      => !res.supporterPlayed
  | .playItem           => true   -- unlimited
  | .playStadium        => true
  | .playTool           => true
  | .useAbility         => true
  | .retreat            => !res.retreated
  | .endMainPhase       => true   -- always can end main phase

/-- Update resources after performing an action. -/
def MainAction.updateResources (action : MainAction) (res : TurnResources) : TurnResources :=
  match action with
  | .attachEnergy    => { res with energyAttached := true }
  | .playSupporter   => { res with supporterPlayed := true }
  | .retreat         => { res with retreated := true }
  | .playBasicToBench => { res with normalSummon := true }
  | _                => res

-- ============================================================
-- §8  Attack Phase
-- ============================================================

/-- Whether the current player can attack. -/
def canAttack (isFirstTurn : Bool) (hasActive : Bool) : Bool :=
  hasActive && !isFirstTurn

/-- Attack declaration. -/
structure AttackDeclaration where
  attackIndex : Nat     -- which attack on the active Pokémon
  deriving DecidableEq, Repr

-- ============================================================
-- §9  Between-Turns Processing
-- ============================================================

/-- Special condition effects to process between turns. -/
structure BetweenTurnsInput where
  isPoisoned  : Bool
  isBurned    : Bool
  isAsleep    : Bool
  isParalyzed : Bool
  burnFlip    : Coin
  sleepFlip   : Coin
  deriving DecidableEq, Repr

/-- Result of between-turns processing. -/
structure BetweenTurnsResult where
  poisonDamage   : Nat    -- 10 per poison
  burnDamage     : Nat    -- 20 on tails
  wokeUp         : Bool   -- sleep heads
  curedParalysis : Bool   -- auto-cure
  deriving DecidableEq, Repr

/-- Process between-turns effects. -/
def processBetweenTurns (input : BetweenTurnsInput) : BetweenTurnsResult where
  poisonDamage := if input.isPoisoned then 10 else 0
  burnDamage := if input.isBurned then
    match input.burnFlip with
    | .tails => 20
    | .heads => 0
    else 0
  wokeUp := if input.isAsleep then
    match input.sleepFlip with
    | .heads => true
    | .tails => false
    else false
  curedParalysis := input.isParalyzed

-- ============================================================
-- §10  Phase Transitions
-- ============================================================

/-- Advance to the next phase. -/
def Phase.next : Phase → Phase
  | .draw         => .main
  | .main         => .attack
  | .attack       => .betweenTurns
  | .betweenTurns => .draw   -- loops to next turn's draw

/-- Whether a phase is the last in a turn (betweenTurns). -/
def Phase.isLast : Phase → Bool
  | .betweenTurns => true
  | _             => false

/-- Advance the turn state to the next phase. -/
def TurnState.advancePhase (ts : TurnState) : TurnState :=
  if ts.phase.isLast then
    -- Moving to next turn
    { ts with
      currentPlayer := 1 - ts.currentPlayer
      turnNumber := ts.turnNumber + 1
      phase := .draw
      isFirstTurn := false
      resources := TurnResources.fresh }
  else
    { ts with phase := ts.phase.next }

/-- Skip attack (optional — go directly to betweenTurns). -/
def TurnState.skipAttack (ts : TurnState) (_ : ts.phase = .attack) : TurnState :=
  { ts with phase := .betweenTurns }

-- ============================================================
-- §11  Full Turn Execution (Step by Step)
-- ============================================================

/-- Execute one complete turn. Returns updated turn state. -/
def executeTurn (ts : TurnState) : TurnState :=
  -- Draw phase → Main phase → Attack phase → Between turns → next turn
  let afterDraw := { ts with phase := .main }
  let afterMain := { afterDraw with phase := .attack }
  let afterAttack := { afterMain with phase := .betweenTurns }
  { afterAttack with
    currentPlayer := 1 - afterAttack.currentPlayer
    turnNumber := afterAttack.turnNumber + 1
    phase := .draw
    isFirstTurn := false
    resources := TurnResources.fresh }

-- ============================================================
-- §12  Game Termination
-- ============================================================

/-- Reasons the game can end. -/
inductive GameEndReason where
  | deckout (player : Nat)
  | allPrizesTaken (player : Nat)
  | noPokemonInPlay (player : Nat)
  deriving DecidableEq, Repr

/-- Game result. -/
inductive GameResult where
  | ongoing
  | winner (player : Nat) (reason : GameEndReason)
  deriving DecidableEq, Repr

-- ============================================================
-- §13  Theorems — Phase Ordering
-- ============================================================

/-- Theorem 1: Draw phase comes first (ord = 0). -/
theorem draw_is_first : Phase.draw.ord = 0 := by rfl

/-- Theorem 2: Main phase comes after draw. -/
theorem main_after_draw : Phase.draw.lt .main = true := by rfl

/-- Theorem 3: Attack comes after main. -/
theorem attack_after_main : Phase.main.lt .attack = true := by rfl

/-- Theorem 4: Between-turns comes after attack. -/
theorem between_after_attack : Phase.attack.lt .betweenTurns = true := by rfl

/-- Theorem 5: Phase ordering is linear (total). -/
theorem phase_order_total (p1 p2 : Phase) :
    p1.le p2 = true ∨ p2.le p1 = true := by
  cases p1 <;> cases p2 <;> simp [Phase.le, Phase.ord]

/-- Theorem 6: Phase ordering is transitive. -/
theorem phase_order_trans (a b c : Phase)
    (hab : a.lt b = true) (hbc : b.lt c = true) : a.lt c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [Phase.lt, Phase.ord]

/-- Theorem 7: Phase.next advances the phase ordering (except betweenTurns → draw). -/
theorem next_advances_or_wraps (p : Phase) :
    p.lt p.next = true ∨ p = .betweenTurns := by
  cases p <;> simp [Phase.next, Phase.lt, Phase.ord]

-- ============================================================
-- §14  Theorems — Draw Phase
-- ============================================================

/-- Theorem 8: Drawing is always mandatory. -/
theorem draw_mandatory : drawIsMandatory = true := by rfl

/-- Theorem 9: Can't draw from empty deck → deckout. -/
theorem empty_deck_deckout (c : Option Card) :
    executeDraw 0 c = .deckout := by
  cases c <;> rfl

/-- Theorem 10: Drawing from non-empty deck with a card succeeds. -/
theorem draw_succeeds (n : Nat) (c : Card) :
    executeDraw (n + 1) (some c) = .success c n := by rfl

/-- Theorem 11: Draw decreases deck size by 1. -/
theorem draw_decreases_deck (n : Nat) (c : Card) :
    match executeDraw (n + 1) (some c) with
    | .success _ remaining => remaining = n
    | .deckout => False := by
  simp [executeDraw]

-- ============================================================
-- §15  Theorems — Resource Tracking
-- ============================================================

/-- Theorem 12: Fresh resources have nothing used. -/
theorem fresh_no_supporter : TurnResources.fresh.supporterPlayed = false := by rfl
theorem fresh_no_energy : TurnResources.fresh.energyAttached = false := by rfl
theorem fresh_no_retreat : TurnResources.fresh.retreated = false := by rfl

/-- Theorem 13: One supporter per turn — after playing, can't play another. -/
theorem supporter_once (res : TurnResources) :
    (MainAction.updateResources .playSupporter res).supporterPlayed = true := by rfl

/-- Theorem 14: After playing supporter, supporter is not legal. -/
theorem no_second_supporter (res : TurnResources) (ft : Bool) (bench : Nat) :
    MainAction.isLegal .playSupporter
      (MainAction.updateResources .playSupporter res) ft bench = false := by
  simp [MainAction.isLegal, MainAction.updateResources]

/-- Theorem 15: One energy per turn — after attaching, can't attach another. -/
theorem energy_once (res : TurnResources) :
    (MainAction.updateResources .attachEnergy res).energyAttached = true := by rfl

/-- Theorem 16: After attaching energy, energy attach is not legal. -/
theorem no_second_energy (res : TurnResources) (ft : Bool) (bench : Nat) :
    MainAction.isLegal .attachEnergy
      (MainAction.updateResources .attachEnergy res) ft bench = false := by
  simp [MainAction.isLegal, MainAction.updateResources]

/-- Theorem 17: One retreat per turn. -/
theorem retreat_once (res : TurnResources) :
    (MainAction.updateResources .retreat res).retreated = true := by rfl

/-- Theorem 18: After retreating, retreat is not legal. -/
theorem no_second_retreat (res : TurnResources) (ft : Bool) (bench : Nat) :
    MainAction.isLegal .retreat
      (MainAction.updateResources .retreat res) ft bench = false := by
  simp [MainAction.isLegal, MainAction.updateResources]

/-- Theorem 19: Items are always legal (unlimited). -/
theorem items_unlimited (res : TurnResources) (ft : Bool) (bench : Nat) :
    MainAction.isLegal .playItem res ft bench = true := by rfl

/-- Theorem 20: End main phase is always legal. -/
theorem can_always_end_main (res : TurnResources) (ft : Bool) (bench : Nat) :
    MainAction.isLegal .endMainPhase res ft bench = true := by rfl

-- ============================================================
-- §16  Theorems — Attack Phase
-- ============================================================

/-- Theorem 21: Can't attack on first turn (going-first player). -/
theorem no_attack_first_turn :
    canAttack true true = false := by rfl

/-- Theorem 22: Can attack on non-first turn with active Pokémon. -/
theorem can_attack_normal :
    canAttack false true = true := by rfl

/-- Theorem 23: Can't attack without active Pokémon. -/
theorem no_attack_no_active (ft : Bool) :
    canAttack ft false = false := by
  simp [canAttack]

/-- Theorem 24: Evolution not allowed on first turn going first. -/
theorem no_evolve_first_turn (res : TurnResources) (bench : Nat) :
    MainAction.isLegal .evolvePokemon res true bench = false := by rfl

/-- Theorem 25: Evolution allowed on subsequent turns. -/
theorem evolve_allowed_later (res : TurnResources) (bench : Nat) :
    MainAction.isLegal .evolvePokemon res false bench = true := by rfl

-- ============================================================
-- §17  Theorems — Phase Transitions
-- ============================================================

/-- Theorem 26: After draw, phase is main. -/
theorem draw_to_main : Phase.draw.next = .main := by rfl

/-- Theorem 27: After main, phase is attack. -/
theorem main_to_attack : Phase.main.next = .attack := by rfl

/-- Theorem 28: After attack, phase is betweenTurns. -/
theorem attack_to_between : Phase.attack.next = .betweenTurns := by rfl

/-- Theorem 29: After betweenTurns, phase wraps to draw. -/
theorem between_to_draw : Phase.betweenTurns.next = .draw := by rfl

/-- Theorem 30: Advancing from betweenTurns switches player. -/
theorem advance_switches_player (ts : TurnState) (h : ts.phase = .betweenTurns) :
    (ts.advancePhase).currentPlayer = 1 - ts.currentPlayer := by
  simp [TurnState.advancePhase, Phase.isLast, h]

/-- Theorem 31: Advancing from betweenTurns increments turn number. -/
theorem advance_increments_turn (ts : TurnState) (h : ts.phase = .betweenTurns) :
    (ts.advancePhase).turnNumber = ts.turnNumber + 1 := by
  simp [TurnState.advancePhase, Phase.isLast, h]

/-- Theorem 32: Advancing from betweenTurns resets resources. -/
theorem advance_resets_resources (ts : TurnState) (h : ts.phase = .betweenTurns) :
    (ts.advancePhase).resources = TurnResources.fresh := by
  simp [TurnState.advancePhase, Phase.isLast, h]

-- ============================================================
-- §18  Theorems — Between-Turns Processing
-- ============================================================

/-- Theorem 33: Poison does 10 damage. -/
theorem poison_damage_10 (input : BetweenTurnsInput) (h : input.isPoisoned = true) :
    (processBetweenTurns input).poisonDamage = 10 := by
  simp [processBetweenTurns, h]

/-- Theorem 34: No poison means 0 poison damage. -/
theorem no_poison_no_damage (input : BetweenTurnsInput) (h : input.isPoisoned = false) :
    (processBetweenTurns input).poisonDamage = 0 := by
  simp [processBetweenTurns, h]

/-- Theorem 35: Burn on tails does 20 damage. -/
theorem burn_tails_20 (input : BetweenTurnsInput)
    (hb : input.isBurned = true) (hf : input.burnFlip = .tails) :
    (processBetweenTurns input).burnDamage = 20 := by
  simp [processBetweenTurns, hb, hf]

/-- Theorem 36: Paralysis always auto-cures between turns. -/
theorem paralysis_auto_cures (input : BetweenTurnsInput) (h : input.isParalyzed = true) :
    (processBetweenTurns input).curedParalysis = true := by
  simp [processBetweenTurns, h]

end PokemonLean.Core.TurnLoop