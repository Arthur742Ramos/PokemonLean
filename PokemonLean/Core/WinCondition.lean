/-
  PokemonLean / Core / WinCondition.lean

  Pokémon TCG win conditions formalised in Lean 4.
  Self-contained: defines game state, prize tracking, win conditions.

  Three win conditions:
  1. Take all prize cards
  2. Opponent can't draw (deckout)
  3. Opponent has no Pokémon in play

  All proofs are sorry-free.  32 theorems.
-/

namespace PokemonLean.Core.WinCondition

-- ============================================================
-- §1  Core Types (self-contained)
-- ============================================================

/-- Pokémon card classification for prize values. -/
inductive PokemonKind where
  | basic       -- 1 prize
  | ex          -- 2 prizes (Pokémon-ex)
  | gx          -- 2 prizes
  | v           -- 2 prizes
  | vstar       -- 2 prizes
  | vmax        -- 3 prizes
  | tagTeam     -- 3 prizes
  deriving DecidableEq, Repr

/-- Prize value: how many prizes the opponent takes for KOing this Pokémon. -/
def prizeValue : PokemonKind → Nat
  | .basic   => 1
  | .ex      => 2
  | .gx      => 2
  | .v       => 2
  | .vstar   => 2
  | .vmax    => 3
  | .tagTeam => 3

/-- A Pokémon in play (simplified). -/
structure Pokemon where
  name : String
  kind : PokemonKind
  hp   : Nat
  deriving DecidableEq, Repr

/-- Player state. -/
structure PlayerState where
  prizesRemaining : Nat       -- start at 6, take on KO
  deckSize        : Nat       -- cards remaining in deck
  active          : Option Pokemon
  bench           : List Pokemon
  deriving DecidableEq, Repr

/-- Does the player have any Pokémon in play? -/
def PlayerState.hasPokemonInPlay (ps : PlayerState) : Bool :=
  ps.active.isSome || !ps.bench.isEmpty

/-- Total Pokémon count in play. -/
def PlayerState.pokemonCount (ps : PlayerState) : Nat :=
  (if ps.active.isSome then 1 else 0) + ps.bench.length

-- ============================================================
-- §2  Win Condition Definitions
-- ============================================================

/-- Win by taking all prizes. -/
def winByPrizes (ps : PlayerState) : Bool :=
  ps.prizesRemaining == 0

/-- Win by deckout (opponent can't draw at start of turn). -/
def winByDeckout (opponentDeck : Nat) : Bool :=
  opponentDeck == 0

/-- Win by no Pokémon (opponent has no Pokémon in play). -/
def winByNoPokemon (opponent : PlayerState) : Bool :=
  !opponent.hasPokemonInPlay

/-- Any win condition satisfied? -/
def hasWon (me : PlayerState) (opponent : PlayerState) : Bool :=
  winByPrizes me || winByDeckout opponent.deckSize || winByNoPokemon opponent

-- ============================================================
-- §3  Prize Taking Mechanics
-- ============================================================

/-- Take prizes for KOing a Pokémon. Returns updated prize count. -/
def takePrizes (currentPrizes : Nat) (ko : PokemonKind) : Nat :=
  let taken := prizeValue ko
  if currentPrizes ≥ taken then currentPrizes - taken else 0

/-- How many KOs of a given kind needed to take all 6 prizes? -/
def kosNeeded (kind : PokemonKind) : Nat :=
  let pv := prizeValue kind
  (6 + pv - 1) / pv   -- ceiling division

/-- Minimum turns to win by prizes (1 KO per turn, starting from 6 prizes). -/
def minTurnsForPrizeWin (kind : PokemonKind) : Nat :=
  kosNeeded kind

-- ============================================================
-- §4  Game Termination State
-- ============================================================

/-- Game result. -/
inductive GameResult where
  | ongoing
  | player1Wins
  | player2Wins
  | draw         -- simultaneous loss (extremely rare)
  deriving DecidableEq, Repr

/-- Evaluate game result for player 1 attacking. -/
def evaluateGameResult (p1 p2 : PlayerState) : GameResult :=
  if winByPrizes p1 then .player1Wins
  else if winByDeckout p2.deckSize then .player1Wins
  else if winByNoPokemon p2 then .player1Wins
  else if winByPrizes p2 then .player2Wins
  else if winByDeckout p1.deckSize then .player2Wins
  else if winByNoPokemon p1 then .player2Wins
  else .ongoing

/-- Sudden death: when both players start with only 1 prize. -/
def isSuddenDeath (p1 p2 : PlayerState) : Bool :=
  p1.prizesRemaining == 1 && p2.prizesRemaining == 1

-- ============================================================
-- §5  Prize Value Theorems
-- ============================================================

/-- Theorem 1: Basic Pokémon are worth 1 prize. -/
theorem basic_one_prize : prizeValue .basic = 1 := rfl

/-- Theorem 2: EX/GX/V/VSTAR are worth 2 prizes. -/
theorem ex_two_prizes : prizeValue .ex = 2 := rfl
theorem gx_two_prizes : prizeValue .gx = 2 := rfl
theorem v_two_prizes : prizeValue .v = 2 := rfl
theorem vstar_two_prizes : prizeValue .vstar = 2 := rfl

/-- Theorem 3: VMAX and Tag Team are worth 3 prizes. -/
theorem vmax_three_prizes : prizeValue .vmax = 3 := rfl
theorem tag_team_three_prizes : prizeValue .tagTeam = 3 := rfl

/-- Theorem 4: Prize value is always positive. -/
theorem prize_value_pos (k : PokemonKind) : prizeValue k ≥ 1 := by
  cases k <;> simp [prizeValue]

/-- Theorem 5: Prize value is at most 3. -/
theorem prize_value_le_3 (k : PokemonKind) : prizeValue k ≤ 3 := by
  cases k <;> simp [prizeValue]

-- ============================================================
-- §6  KO Count Theorems (Fastest Win)
-- ============================================================

/-- Theorem 6: Need 6 basic KOs to win. -/
theorem basic_kos_needed : kosNeeded .basic = 6 := by native_decide

/-- Theorem 7: Need 3 EX KOs to win. -/
theorem ex_kos_needed : kosNeeded .ex = 3 := by native_decide

/-- Theorem 8: Need 3 GX KOs to win. -/
theorem gx_kos_needed : kosNeeded .gx = 3 := by native_decide

/-- Theorem 9: Need 3 V KOs to win. -/
theorem v_kos_needed : kosNeeded .v = 3 := by native_decide

/-- Theorem 10: Need 2 VMAX KOs to win. -/
theorem vmax_kos_needed : kosNeeded .vmax = 2 := by native_decide

/-- Theorem 11: Need 2 Tag Team KOs to win. -/
theorem tag_team_kos_needed : kosNeeded .tagTeam = 2 := by native_decide

/-- Theorem 12: VMAX is the fastest prize-based win (2 KOs). -/
theorem vmax_fastest_win :
    kosNeeded .vmax ≤ kosNeeded .basic ∧
    kosNeeded .vmax ≤ kosNeeded .ex ∧
    kosNeeded .vmax ≤ kosNeeded .v ∧
    kosNeeded .vmax ≤ kosNeeded .tagTeam := by
  native_decide

-- ============================================================
-- §7  Prize Taking Monotonicity Theorems
-- ============================================================

/-- Theorem 13: Taking prizes decreases or maintains prize count. -/
theorem prize_taking_decreases (current : Nat) (k : PokemonKind) :
    takePrizes current k ≤ current := by
  simp [takePrizes]
  split <;> omega

/-- Theorem 14: Taking prizes from 6 with basic leaves 5. -/
theorem take_one_basic : takePrizes 6 .basic = 5 := by native_decide

/-- Theorem 15: Taking prizes from 6 with VMAX leaves 3. -/
theorem take_one_vmax : takePrizes 6 .vmax = 3 := by native_decide

/-- Theorem 16: Taking 2 VMAX KOs from 6 reaches 0. -/
theorem two_vmax_wins : takePrizes (takePrizes 6 .vmax) .vmax = 0 := by native_decide

/-- Theorem 17: Taking 3 EX KOs from 6 reaches 0. -/
theorem three_ex_wins : takePrizes (takePrizes (takePrizes 6 .ex) .ex) .ex = 0 := by
  native_decide

/-- Theorem 18: Taking 6 basic KOs from 6 reaches 0. -/
theorem six_basic_wins :
    takePrizes (takePrizes (takePrizes (takePrizes (takePrizes (takePrizes 6
      .basic) .basic) .basic) .basic) .basic) .basic = 0 := by
  native_decide

-- ============================================================
-- §8  Win Condition Theorems
-- ============================================================

/-- Theorem 19: Zero prizes remaining means win by prizes. -/
theorem zero_prizes_wins :
    winByPrizes { prizesRemaining := 0, deckSize := 30,
                  active := some ⟨"Pikachu", .basic, 60⟩, bench := [] } = true := by
  rfl

/-- Theorem 20: Empty deck means deckout win. -/
theorem empty_deck_deckout : winByDeckout 0 = true := by rfl

/-- Theorem 21: Non-empty deck is not deckout. -/
theorem nonempty_deck_no_deckout (n : Nat) (h : n > 0) : winByDeckout n = false := by
  simp [winByDeckout]
  omega

/-- Theorem 22: No Pokémon in play means opponent wins. -/
theorem no_pokemon_loses :
    winByNoPokemon { prizesRemaining := 6, deckSize := 30,
                     active := none, bench := [] } = true := by
  rfl

/-- Theorem 23: Having an active Pokémon means you don't lose by no-Pokémon. -/
theorem active_pokemon_safe (ps : PlayerState) (p : Pokemon)
    (h : ps.active = some p) :
    winByNoPokemon ps = false := by
  simp [winByNoPokemon, PlayerState.hasPokemonInPlay, h]

-- ============================================================
-- §9  Game Termination Theorems
-- ============================================================

/-- Theorem 24: Game with finite deck must eventually deckout
    (deck strictly decreases each turn draw).
    Modelled: if you draw 1 card per turn, after n turns deck has n fewer cards. -/
def deckAfterTurns (initialDeck : Nat) (turns : Nat) : Nat :=
  if initialDeck ≥ turns then initialDeck - turns else 0

theorem deckout_inevitable (initialDeck : Nat) :
    deckAfterTurns initialDeck (initialDeck + 1) = 0 := by
  simp [deckAfterTurns]; omega

/-- Theorem 25: Prize count never increases from KOs. -/
theorem prizes_nonincreasing (p : Nat) (k : PokemonKind) :
    takePrizes p k ≤ p := by
  simp [takePrizes]; split <;> omega

/-- Theorem 26: If prizes are already 0, taking more doesn't change. -/
theorem prizes_floor_zero (k : PokemonKind) :
    takePrizes 0 k = 0 := by
  cases k <;> rfl

/-- Theorem 27: Evaluating game with 0 prizes = player 1 wins. -/
theorem zero_prizes_p1_wins (p2 : PlayerState) :
    evaluateGameResult
      { prizesRemaining := 0, deckSize := 20,
        active := some ⟨"Charizard", .basic, 150⟩, bench := [] }
      p2 = .player1Wins := by
  rfl

/-- Theorem 28: Sudden death has both players at 1 prize. -/
theorem sudden_death_check :
    isSuddenDeath
      { prizesRemaining := 1, deckSize := 10, active := some ⟨"A", .basic, 60⟩, bench := [] }
      { prizesRemaining := 1, deckSize := 10, active := some ⟨"B", .basic, 60⟩, bench := [] }
    = true := by
  rfl

-- ============================================================
-- §10  Mixed Win Condition Theorems
-- ============================================================

/-- Theorem 29: KOing opponent's last Pokémon + taking last prizes
    both trigger hasWon. -/
theorem double_win_condition :
    hasWon
      { prizesRemaining := 0, deckSize := 10,
        active := some ⟨"Winner", .basic, 100⟩, bench := [] }
      { prizesRemaining := 6, deckSize := 0,
        active := none, bench := [] } = true := by
  rfl

/-- Theorem 30: Game is ongoing when no win condition is met. -/
theorem game_ongoing :
    hasWon
      { prizesRemaining := 4, deckSize := 20,
        active := some ⟨"Pikachu", .basic, 60⟩, bench := [] }
      { prizesRemaining := 5, deckSize := 25,
        active := some ⟨"Geodude", .basic, 70⟩, bench := [] } = false := by
  rfl

/-- Theorem 31: KO count needed is always at least 1. -/
theorem kos_needed_pos (k : PokemonKind) : kosNeeded k ≥ 1 := by
  cases k <;> simp [kosNeeded, prizeValue]

/-- Theorem 32: Min turns for prize win equals KOs needed. -/
theorem min_turns_eq_kos (k : PokemonKind) :
    minTurnsForPrizeWin k = kosNeeded k := by
  rfl

end PokemonLean.Core.WinCondition
