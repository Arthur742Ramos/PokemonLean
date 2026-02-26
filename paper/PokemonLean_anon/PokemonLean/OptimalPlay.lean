import PokemonLean.Semantics
import PokemonLean.SemanticsDeep
import PokemonLean.Core.Types
import Std.Tactic

namespace PokemonLean.OptimalPlay

abbrev MicroPlayerId := PokemonLean.Core.Types.PlayerId

/-- Single active Basic Pokémon for one player in the micro format. -/
structure MicroPokemon where
  hp : Nat
  attackDamage : Nat
  energyAttached : Nat
  deriving Repr, DecidableEq

/-- Micro-format game state: exactly one active Pokémon per player, no bench. -/
structure MicroState where
  player1 : MicroPokemon
  player2 : MicroPokemon
  currentPlayer : MicroPlayerId
  turn : Nat
  deriving Repr, DecidableEq

/-- Micro-format rule constants. -/
def oneAttackPerTurn : Nat := 1
def trainersEnabled : Bool := false
def coinFlipsEnabled : Bool := false
def benchSize : Nat := 0

inductive MicroAction where
  | attack
  deriving Repr, DecidableEq

abbrev Strategy := MicroState → MicroAction

def legalActions (_ : MicroState) : List MicroAction := [.attack]

def otherPlayer : MicroPlayerId → MicroPlayerId
  | .player1 => .player2
  | .player2 => .player1

def currentPokemon (s : MicroState) : MicroPokemon :=
  match s.currentPlayer with
  | .player1 => s.player1
  | .player2 => s.player2

def opposingPokemon (s : MicroState) : MicroPokemon :=
  match s.currentPlayer with
  | .player1 => s.player2
  | .player2 => s.player1

/-- One micro turn: active player attacks once, then turn passes. -/
def microStep (s : MicroState) : MicroState :=
  match s.currentPlayer with
  | .player1 =>
      let p2' : MicroPokemon := { s.player2 with hp := s.player2.hp - s.player1.attackDamage }
      { s with player2 := p2', currentPlayer := .player2, turn := s.turn + 1 }
  | .player2 =>
      let p1' : MicroPokemon := { s.player1 with hp := s.player1.hp - s.player2.attackDamage }
      { s with player1 := p1', currentPlayer := .player1, turn := s.turn + 1 }

/-- Ceiling division, with 0 when divisor is 0. -/
def ceilDiv (a b : Nat) : Nat :=
  if b = 0 then 0 else (a + b - 1) / b

/-- Number of attacks of size `damage` needed to KO `hp`. -/
def hitsToKO (hp damage : Nat) : Nat :=
  ceilDiv hp damage

def currentSurvivalHits (s : MicroState) : Nat :=
  hitsToKO (currentPokemon s).hp (opposingPokemon s).attackDamage

def opponentSurvivalHits (s : MicroState) : Nat :=
  hitsToKO (opposingPokemon s).hp (currentPokemon s).attackDamage

def terminalScore (s : MicroState) : Int :=
  Int.ofNat (currentSurvivalHits s) - Int.ofNat (opponentSurvivalHits s)

def maxList : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl max x

def minList : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl min x

def actionScore (s : MicroState) (_ : MicroAction) : Int :=
  terminalScore s

/-- Minimax value of the position for the current player. -/
def Value (s : MicroState) : Int :=
  maxList ((legalActions s).map (fun a =>
    minList ((legalActions (microStep s)).map (fun _ => actionScore s a))))

def currentPlayerWins (s : MicroState) : Prop :=
  Value s > 0

def strategyValue (σ : Strategy) (s : MicroState) : Int :=
  minList ((legalActions (microStep s)).map (fun _ => actionScore s (σ s)))

def AchievesValue (σ : Strategy) (s : MicroState) : Prop :=
  σ s ∈ legalActions s ∧ strategyValue σ s = Value s

def attackStrategy : Strategy := fun _ => .attack

@[simp] theorem maxList_singleton (x : Int) : maxList [x] = x := by
  simp [maxList]

@[simp] theorem minList_singleton (x : Int) : minList [x] = x := by
  simp [minList]

@[simp] theorem value_eq_terminalScore (s : MicroState) : Value s = terminalScore s := by
  simp [Value, legalActions, actionScore]

theorem zero_sum (s : MicroState) :
    Value { s with currentPlayer := .player1 } +
      Value { s with currentPlayer := .player2 } = 0 := by
  simp [terminalScore, currentSurvivalHits, opponentSurvivalHits, currentPokemon, opposingPokemon]
  omega

theorem optimal_strategy_exists (s : MicroState) :
    ∃ σ : Strategy, AchievesValue σ s := by
  refine ⟨attackStrategy, ?_⟩
  simp [AchievesValue, strategyValue, attackStrategy, Value, legalActions, actionScore]

theorem int_ofNat_sub_pos_iff (a b : Nat) :
    (Int.ofNat a - Int.ofNat b > 0) ↔ a > b := by
  constructor
  · intro h
    have h' : Int.ofNat a - Int.ofNat b + Int.ofNat b > 0 + Int.ofNat b :=
      Int.add_lt_add_right h (Int.ofNat b)
    have h'' : Int.ofNat a > Int.ofNat b := by
      simpa [Int.sub_add_cancel] using h'
    exact (Int.ofNat_lt).1 h''
  · intro h
    have h' : Int.ofNat a > Int.ofNat b := (Int.ofNat_lt).2 h
    have h'' : Int.ofNat a - Int.ofNat b + Int.ofNat b > 0 + Int.ofNat b := by
      simpa [Int.sub_add_cancel] using h'
    exact (Int.add_lt_add_iff_right (Int.ofNat b)).1 h''

theorem currentPlayerWins_iff_survivesMore (s : MicroState) :
    currentPlayerWins s ↔ currentSurvivalHits s > opponentSurvivalHits s := by
  unfold currentPlayerWins
  rw [value_eq_terminalScore]
  unfold terminalScore
  exact int_ofNat_sub_pos_iff (currentSurvivalHits s) (opponentSurvivalHits s)

/-- First-player criterion in the micro format: strictly more survivable hits wins. -/
theorem first_player_wins_iff (p1 p2 : MicroPokemon) :
    currentPlayerWins { player1 := p1, player2 := p2, currentPlayer := .player1, turn := 0 } ↔
      hitsToKO p1.hp p2.attackDamage > hitsToKO p2.hp p1.attackDamage := by
  simpa [currentSurvivalHits, opponentSurvivalHits, currentPokemon, opposingPokemon, hitsToKO] using
    (currentPlayerWins_iff_survivesMore
      { player1 := p1, player2 := p2, currentPlayer := .player1, turn := 0 })

def charizard : MicroPokemon := { hp := 180, attackDamage := 120, energyAttached := 3 }
def pikachu : MicroPokemon := { hp := 60, attackDamage := 30, energyAttached := 1 }

theorem charizard_wins_in_one_turn :
    hitsToKO pikachu.hp charizard.attackDamage = 1 := by
  decide

theorem pikachu_needs_six_turns :
    hitsToKO charizard.hp pikachu.attackDamage = 6 := by
  decide

theorem charizard_vs_pikachu_first_player_win :
    currentPlayerWins { player1 := charizard, player2 := pikachu, currentPlayer := .player1, turn := 0 } := by
  rw [first_player_wins_iff]
  decide

def stateAB (a b : MicroPokemon) (starter : MicroPlayerId) : MicroState :=
  { player1 := a, player2 := b, currentPlayer := starter, turn := 0 }

theorem ohko_dominance
    (a b : MicroPokemon)
    (hOhko : hitsToKO b.hp a.attackDamage = 1)
    (hNotReciprocal : hitsToKO a.hp b.attackDamage > 1) :
    currentPlayerWins (stateAB a b .player1) ∧
      ¬ currentPlayerWins (stateAB a b .player2) := by
  have hFirst :
      currentPlayerWins (stateAB a b .player1) ↔
        hitsToKO a.hp b.attackDamage > hitsToKO b.hp a.attackDamage := by
    simpa [stateAB] using (first_player_wins_iff a b)
  constructor
  · rw [hFirst]
    omega
  · intro hP2
    have hP2' :
        hitsToKO b.hp a.attackDamage > hitsToKO a.hp b.attackDamage := by
      simpa [stateAB, currentSurvivalHits, opponentSurvivalHits, currentPokemon, opposingPokemon, hitsToKO] using
        (currentPlayerWins_iff_survivesMore (stateAB a b .player2)).1 hP2
    omega

end PokemonLean.OptimalPlay
