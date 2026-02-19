/-
  PokemonLean/RealMetagame.lean — Real competitive Pokémon TCG metagame analysis

  Data: Trainer Hill (trainerhill.com), 2026-01-29 to 2026-02-19, 50+ player tournaments

  Decks (indices 0–5):
    0 = Dragapult Dusknoir
    1 = Gholdengo Lunatone
    2 = Grimmsnarl Froslass
    3 = Mega Absol Box
    4 = Gardevoir
    5 = Charizard Noctowl

  Win-rate matrix (row plays against column, out of 1000):
                  Drag.Dusk  Ghol.Luna  Grimm.Fros  M.Absol  Gardevoir  Char.Noct
    Drag.Dusk         494        436         386        382       343        641
    Ghol.Luna         521        488         476        443       441        483
    Grimm.Fros        572        467         485        344       566        558
    M.Absol           576        512         621        494       558        475
    Gardevoir         627        493         374        402       480        394
    Char.Noct         324        480         397        471       558        487

  Minimax equilibrium (exact rationals):
    Row strategy:    Dragapult Dusknoir = 19/278, Mega Absol Box = 259/278
    Column strategy: Mega Absol Box = 83/139, Charizard Noctowl = 56/139
-/
import PokemonLean.NashEquilibrium

namespace PokemonLean.RealMetagame

open PokemonLean.NashEquilibrium

-- ============================================================================
-- DECK ENUMERATION
-- ============================================================================

/-- The six top competitive decks in the sampled Trainer Hill metagame. -/
inductive CompDeck where
  | dragapult_dusknoir   -- Index 0
  | gholdengo_lunatone   -- Index 1
  | grimmsnarl_froslass  -- Index 2
  | mega_absol_box       -- Index 3
  | gardevoir            -- Index 4
  | charizard_noctowl    -- Index 5
  deriving DecidableEq, BEq, Repr

/-- Number of decks in the metagame. -/
def numDecks : Nat := 6

-- ============================================================================
-- PAYOFF MATRIX (win rates out of 1000)
-- Data: Trainer Hill (trainerhill.com), 2026-01-29 to 2026-02-19, 50+ player tournaments
-- ============================================================================

/-- The 6×6 matchup matrix.
    Entry M[i][j] is row deck i's empirical win rate vs column deck j, out of 1000. -/
def realMatchupMatrix : Fin 6 → Fin 6 → Rat
  -- Row 0: Dragapult Dusknoir
  | ⟨0, _⟩, ⟨0, _⟩ => (494 : Rat)
  | ⟨0, _⟩, ⟨1, _⟩ => (436 : Rat)
  | ⟨0, _⟩, ⟨2, _⟩ => (386 : Rat)
  | ⟨0, _⟩, ⟨3, _⟩ => (382 : Rat)
  | ⟨0, _⟩, ⟨4, _⟩ => (343 : Rat)
  | ⟨0, _⟩, ⟨5, _⟩ => (641 : Rat)
  -- Row 1: Gholdengo Lunatone
  | ⟨1, _⟩, ⟨0, _⟩ => (521 : Rat)
  | ⟨1, _⟩, ⟨1, _⟩ => (488 : Rat)
  | ⟨1, _⟩, ⟨2, _⟩ => (476 : Rat)
  | ⟨1, _⟩, ⟨3, _⟩ => (443 : Rat)
  | ⟨1, _⟩, ⟨4, _⟩ => (441 : Rat)
  | ⟨1, _⟩, ⟨5, _⟩ => (483 : Rat)
  -- Row 2: Grimmsnarl Froslass
  | ⟨2, _⟩, ⟨0, _⟩ => (572 : Rat)
  | ⟨2, _⟩, ⟨1, _⟩ => (467 : Rat)
  | ⟨2, _⟩, ⟨2, _⟩ => (485 : Rat)
  | ⟨2, _⟩, ⟨3, _⟩ => (344 : Rat)
  | ⟨2, _⟩, ⟨4, _⟩ => (566 : Rat)
  | ⟨2, _⟩, ⟨5, _⟩ => (558 : Rat)
  -- Row 3: Mega Absol Box
  | ⟨3, _⟩, ⟨0, _⟩ => (576 : Rat)
  | ⟨3, _⟩, ⟨1, _⟩ => (512 : Rat)
  | ⟨3, _⟩, ⟨2, _⟩ => (621 : Rat)
  | ⟨3, _⟩, ⟨3, _⟩ => (494 : Rat)
  | ⟨3, _⟩, ⟨4, _⟩ => (558 : Rat)
  | ⟨3, _⟩, ⟨5, _⟩ => (475 : Rat)
  -- Row 4: Gardevoir
  | ⟨4, _⟩, ⟨0, _⟩ => (627 : Rat)
  | ⟨4, _⟩, ⟨1, _⟩ => (493 : Rat)
  | ⟨4, _⟩, ⟨2, _⟩ => (374 : Rat)
  | ⟨4, _⟩, ⟨3, _⟩ => (402 : Rat)
  | ⟨4, _⟩, ⟨4, _⟩ => (480 : Rat)
  | ⟨4, _⟩, ⟨5, _⟩ => (394 : Rat)
  -- Row 5: Charizard Noctowl
  | ⟨5, _⟩, ⟨0, _⟩ => (324 : Rat)
  | ⟨5, _⟩, ⟨1, _⟩ => (480 : Rat)
  | ⟨5, _⟩, ⟨2, _⟩ => (397 : Rat)
  | ⟨5, _⟩, ⟨3, _⟩ => (471 : Rat)
  | ⟨5, _⟩, ⟨4, _⟩ => (558 : Rat)
  | ⟨5, _⟩, ⟨5, _⟩ => (487 : Rat)

/-- The metagame formalized as a finite two-player zero-sum game on six strategies. -/
def realMetaGame : FiniteGame :=
  { n := 2
    m := 6
    payoff := fun _ _ => 0
    matrix := realMatchupMatrix }

-- ============================================================================
-- BASIC MATRIX FACTS
-- ============================================================================

/-- Empirical matrix entries are not perfectly antisymmetric because they come from sampled data. -/
theorem matchup_not_antisymmetric :
    realMatchupMatrix ⟨0, by decide⟩ ⟨1, by decide⟩ ≠
      -(realMatchupMatrix ⟨1, by decide⟩ ⟨0, by decide⟩) := by
  native_decide

/-- Mirror-match empirical rates from the dataset. -/
theorem mirror_match_rates :
    realMatchupMatrix ⟨0, by decide⟩ ⟨0, by decide⟩ = 494 ∧
    realMatchupMatrix ⟨1, by decide⟩ ⟨1, by decide⟩ = 488 ∧
    realMatchupMatrix ⟨2, by decide⟩ ⟨2, by decide⟩ = 485 ∧
    realMatchupMatrix ⟨3, by decide⟩ ⟨3, by decide⟩ = 494 ∧
    realMatchupMatrix ⟨4, by decide⟩ ⟨4, by decide⟩ = 480 ∧
    realMatchupMatrix ⟨5, by decide⟩ ⟨5, by decide⟩ = 487 := by
  native_decide

-- ============================================================================
-- NASH EQUILIBRIUM STRATEGIES
-- ============================================================================

/-- Row-player minimax strategy for the Trainer Hill matrix. -/
def nashRowStrategy : MixedStrategy 6
  | ⟨0, _⟩ => (19 : Rat) / (278 : Rat)    -- Dragapult Dusknoir
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => (259 : Rat) / (278 : Rat)   -- Mega Absol Box
  | ⟨4, _⟩ => 0
  | ⟨5, _⟩ => 0

/-- Column-player minimax strategy for the Trainer Hill matrix. -/
def nashColStrategy : MixedStrategy 6
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => (83 : Rat) / (139 : Rat)    -- Mega Absol Box
  | ⟨4, _⟩ => 0
  | ⟨5, _⟩ => (56 : Rat) / (139 : Rat)    -- Charizard Noctowl

/-- Backwards-compatible alias for the row equilibrium strategy. -/
def nashStrategy : MixedStrategy 6 := nashRowStrategy

/-- The row Nash strategy is a valid mixed strategy. -/
theorem nash_strategy_valid : IsMixedStrategy 6 nashRowStrategy := by
  native_decide

/-- The column Nash strategy is a valid mixed strategy. -/
theorem nash_counter_strategy_valid : IsMixedStrategy 6 nashColStrategy := by
  native_decide

-- ============================================================================
-- NASH EQUILIBRIUM PROOF
-- ============================================================================

/-- The computed row/column pair is a Nash equilibrium for the real metagame. -/
theorem nash_equilibrium_real_meta :
    NashEquilibrium realMetaGame nashRowStrategy nashColStrategy := by
  native_decide

/-- Existence of a Nash equilibrium follows from the explicit witness above. -/
theorem nash_equilibrium_exists :
    ∃ s1 s2 : MixedStrategy 6, NashEquilibrium realMetaGame s1 s2 := by
  exact ⟨nashRowStrategy, nashColStrategy, nash_equilibrium_real_meta⟩

-- ============================================================================
-- GAME VALUE
-- ============================================================================

/-- The expected payoff at equilibrium is exactly 67602/139 (out of 1000-scale payoffs). -/
theorem game_value_exact :
    expectedPayoff realMetaGame nashRowStrategy nashColStrategy =
      (67602 : Rat) / (139 : Rat) := by
  native_decide

-- ============================================================================
-- SUPPORT ANALYSIS
-- ============================================================================

/-- Mega Absol Box is the largest component of the row-player Nash support. -/
theorem mega_absol_highest_nash_row_share :
    nashRowStrategy ⟨3, by decide⟩ > nashRowStrategy ⟨0, by decide⟩ ∧
    nashRowStrategy ⟨3, by decide⟩ > nashRowStrategy ⟨1, by decide⟩ ∧
    nashRowStrategy ⟨3, by decide⟩ > nashRowStrategy ⟨2, by decide⟩ ∧
    nashRowStrategy ⟨3, by decide⟩ > nashRowStrategy ⟨4, by decide⟩ ∧
    nashRowStrategy ⟨3, by decide⟩ > nashRowStrategy ⟨5, by decide⟩ := by
  native_decide

/-- Mega Absol Box row share is exactly 259/278. -/
theorem mega_absol_share_exact :
    nashRowStrategy ⟨3, by decide⟩ = (259 : Rat) / (278 : Rat) := by
  native_decide

/-- Dragapult Dusknoir row share is exactly 19/278. -/
theorem dragapult_share_exact :
    nashRowStrategy ⟨0, by decide⟩ = (19 : Rat) / (278 : Rat) := by
  native_decide

/-- The remaining four decks are outside the row-player equilibrium support. -/
theorem row_unsupported_decks_zero :
    nashRowStrategy ⟨1, by decide⟩ = 0 ∧
    nashRowStrategy ⟨2, by decide⟩ = 0 ∧
    nashRowStrategy ⟨4, by decide⟩ = 0 ∧
    nashRowStrategy ⟨5, by decide⟩ = 0 := by
  native_decide

-- ============================================================================
-- PURE STRATEGY PAYOFFS AT EQUILIBRIUM
-- ============================================================================

/-- Row support strategies achieve exactly the game value against the column equilibrium mix. -/
theorem row_support_payoffs_equal_value :
    rowPurePayoff realMetaGame ⟨0, by decide⟩ nashColStrategy = (67602 : Rat) / (139 : Rat) ∧
    rowPurePayoff realMetaGame ⟨3, by decide⟩ nashColStrategy = (67602 : Rat) / (139 : Rat) := by
  native_decide

/-- Row non-support strategies are strictly below value against the column equilibrium mix. -/
theorem row_nonsupport_payoffs_below_value :
    rowPurePayoff realMetaGame ⟨1, by decide⟩ nashColStrategy < (67602 : Rat) / (139 : Rat) ∧
    rowPurePayoff realMetaGame ⟨2, by decide⟩ nashColStrategy < (67602 : Rat) / (139 : Rat) ∧
    rowPurePayoff realMetaGame ⟨4, by decide⟩ nashColStrategy < (67602 : Rat) / (139 : Rat) ∧
    rowPurePayoff realMetaGame ⟨5, by decide⟩ nashColStrategy < (67602 : Rat) / (139 : Rat) := by
  native_decide

/-- Column support strategies achieve exactly the game value against the row equilibrium mix. -/
theorem col_support_payoffs_equal_value :
    colPurePayoff realMetaGame nashRowStrategy ⟨3, by decide⟩ = (67602 : Rat) / (139 : Rat) ∧
    colPurePayoff realMetaGame nashRowStrategy ⟨5, by decide⟩ = (67602 : Rat) / (139 : Rat) := by
  native_decide

/-- Column non-support strategies are strictly above value against the row equilibrium mix. -/
theorem col_nonsupport_payoffs_above_value :
    (67602 : Rat) / (139 : Rat) < colPurePayoff realMetaGame nashRowStrategy ⟨0, by decide⟩ ∧
    (67602 : Rat) / (139 : Rat) < colPurePayoff realMetaGame nashRowStrategy ⟨1, by decide⟩ ∧
    (67602 : Rat) / (139 : Rat) < colPurePayoff realMetaGame nashRowStrategy ⟨2, by decide⟩ ∧
    (67602 : Rat) / (139 : Rat) < colPurePayoff realMetaGame nashRowStrategy ⟨4, by decide⟩ := by
  native_decide

-- ============================================================================
-- CHARIZARD NOCTOWL — POLARIZED META CALL
-- ============================================================================

/-- Charizard Noctowl is polarized: very strong into Gardevoir but very weak into Dragapult. -/
theorem charizard_noctowl_polarized :
    realMatchupMatrix ⟨5, by decide⟩ ⟨4, by decide⟩ > 500 ∧
    realMatchupMatrix ⟨5, by decide⟩ ⟨0, by decide⟩ < 500 ∧
    realMatchupMatrix ⟨0, by decide⟩ ⟨5, by decide⟩ > 500 := by
  native_decide

/-- Global empirical extremes: best cell is Dragapult→Charizard (641), worst is Charizard→Dragapult (324). -/
theorem global_matchup_extremes :
    (∀ i j : Fin 6, realMatchupMatrix i j ≤ realMatchupMatrix ⟨0, by decide⟩ ⟨5, by decide⟩) ∧
    (∀ i j : Fin 6, realMatchupMatrix ⟨5, by decide⟩ ⟨0, by decide⟩ ≤ realMatchupMatrix i j) := by
  native_decide

-- ============================================================================
-- MEGA ABSOL BOX DOMINANCE — strongest aggregate spread
-- ============================================================================

/-- Mega Absol Box has the largest row-sum matchup total across the six decks. -/
theorem mega_absol_best_total_spread :
    let dragapultSum := sumFin 6 (fun j => realMatchupMatrix ⟨0, by decide⟩ j)
    let gholdengoSum := sumFin 6 (fun j => realMatchupMatrix ⟨1, by decide⟩ j)
    let grimmsnarlSum := sumFin 6 (fun j => realMatchupMatrix ⟨2, by decide⟩ j)
    let megaAbsolSum := sumFin 6 (fun j => realMatchupMatrix ⟨3, by decide⟩ j)
    let gardevoirSum := sumFin 6 (fun j => realMatchupMatrix ⟨4, by decide⟩ j)
    let charizardSum := sumFin 6 (fun j => realMatchupMatrix ⟨5, by decide⟩ j)
    megaAbsolSum > dragapultSum ∧ megaAbsolSum > gholdengoSum ∧ megaAbsolSum > grimmsnarlSum ∧
    megaAbsolSum > gardevoirSum ∧ megaAbsolSum > charizardSum := by
  native_decide

/-- Mega Absol Box is favorable into four non-mirror decks and only unfavorable into Charizard Noctowl. -/
theorem mega_absol_most_favorable_matchups :
    realMatchupMatrix ⟨3, by decide⟩ ⟨0, by decide⟩ > 500 ∧
    realMatchupMatrix ⟨3, by decide⟩ ⟨1, by decide⟩ > 500 ∧
    realMatchupMatrix ⟨3, by decide⟩ ⟨2, by decide⟩ > 500 ∧
    realMatchupMatrix ⟨3, by decide⟩ ⟨4, by decide⟩ > 500 ∧
    realMatchupMatrix ⟨3, by decide⟩ ⟨5, by decide⟩ < 500 := by
  native_decide

-- ============================================================================
-- OBSERVED vs EQUILIBRIUM META SHARES
-- ============================================================================

/-- Observed top-6 metagame shares from Trainer Hill (fractional shares of full field). 
    Data: Trainer Hill (trainerhill.com), 2026-01-29 to 2026-02-19, 50+ player tournaments -/
def observedShares : MixedStrategy 6
  | ⟨0, _⟩ => (155 : Rat) / (1000 : Rat)  -- Dragapult Dusknoir: 15.5%
  | ⟨1, _⟩ => (99  : Rat) / (1000 : Rat)  -- Gholdengo Lunatone: 9.9%
  | ⟨2, _⟩ => (51  : Rat) / (1000 : Rat)  -- Grimmsnarl Froslass: 5.1%
  | ⟨3, _⟩ => (50  : Rat) / (1000 : Rat)  -- Mega Absol Box: 5.0%
  | ⟨4, _⟩ => (46  : Rat) / (1000 : Rat)  -- Gardevoir: 4.6%
  | ⟨5, _⟩ => (43  : Rat) / (1000 : Rat)  -- Charizard Noctowl: 4.3%

/-- The observed shares do not form a Nash equilibrium. -/
theorem observed_not_nash :
    ¬ NashEquilibrium realMetaGame observedShares observedShares := by
  native_decide

/-- The observed top-6 shares are not a normalized mixed strategy over this restricted 6-deck game. -/
theorem observed_not_mixed :
    ¬ IsMixedStrategy 6 observedShares := by
  native_decide

/-- The observed field assigns positive share to all four row-nonsupport decks. -/
theorem observed_overplays_row_unsupported_decks :
    nashRowStrategy ⟨1, by decide⟩ = 0 ∧
    nashRowStrategy ⟨2, by decide⟩ = 0 ∧
    nashRowStrategy ⟨4, by decide⟩ = 0 ∧
    nashRowStrategy ⟨5, by decide⟩ = 0 ∧
    observedShares ⟨1, by decide⟩ > 0 ∧
    observedShares ⟨2, by decide⟩ > 0 ∧
    observedShares ⟨4, by decide⟩ > 0 ∧
    observedShares ⟨5, by decide⟩ > 0 := by
  native_decide

/-- Observed #1 (Dragapult) differs from row-equilibrium #1 (Mega Absol Box). -/
theorem observed_disagrees_with_nash_top :
    nashRowStrategy ⟨3, by decide⟩ > nashRowStrategy ⟨0, by decide⟩ ∧
    observedShares ⟨0, by decide⟩ > observedShares ⟨3, by decide⟩ := by
  native_decide

/-- Mega Absol Box is heavily underplayed relative to its row-equilibrium share. -/
theorem mega_absol_underplayed :
    observedShares ⟨3, by decide⟩ < nashRowStrategy ⟨3, by decide⟩ := by
  native_decide

/-- Charizard Noctowl is overplayed on the row side relative to equilibrium support. -/
theorem charizard_noctowl_overplayed_rowwise :
    nashRowStrategy ⟨5, by decide⟩ = 0 ∧ observedShares ⟨5, by decide⟩ > 0 := by
  native_decide

-- ============================================================================
-- MATCHUP CLASSIFICATION
-- ============================================================================

/-- Classify a matchup as favorable (>500), even (=500), or unfavorable (<500). -/
def classifyMatchupValue (v : Rat) : String :=
  if v > 500 then "favorable"
  else if v < 500 then "unfavorable"
  else "even"

/-- Every deck has at least one favorable and one unfavorable matchup (>500 and <500). -/
theorem no_dominant_deck :
    ∀ i : Fin 6, (∃ j : Fin 6, realMatchupMatrix i j > 500) ∧
                  (∃ j : Fin 6, realMatchupMatrix i j < 500) := by
  native_decide

-- ============================================================================
-- SUMMARY STATISTICS
-- ============================================================================

/-- The row equilibrium support has exactly two decks: Dragapult and Mega Absol. -/
theorem nash_row_core_is_two_decks :
    nashRowStrategy ⟨0, by decide⟩ > 0 ∧
    nashRowStrategy ⟨3, by decide⟩ > 0 ∧
    nashRowStrategy ⟨1, by decide⟩ = 0 ∧
    nashRowStrategy ⟨2, by decide⟩ = 0 ∧
    nashRowStrategy ⟨4, by decide⟩ = 0 ∧
    nashRowStrategy ⟨5, by decide⟩ = 0 := by
  native_decide

/-- The column equilibrium support has exactly two decks: Mega Absol and Charizard. -/
theorem nash_col_core_is_two_decks :
    nashColStrategy ⟨3, by decide⟩ > 0 ∧
    nashColStrategy ⟨5, by decide⟩ > 0 ∧
    nashColStrategy ⟨0, by decide⟩ = 0 ∧
    nashColStrategy ⟨1, by decide⟩ = 0 ∧
    nashColStrategy ⟨2, by decide⟩ = 0 ∧
    nashColStrategy ⟨4, by decide⟩ = 0 := by
  native_decide

/-- Support asymmetry: Dragapult is row-only support, Charizard is column-only support. -/
theorem nash_support_asymmetry :
    nashRowStrategy ⟨0, by decide⟩ > 0 ∧
    nashColStrategy ⟨0, by decide⟩ = 0 ∧
    nashRowStrategy ⟨5, by decide⟩ = 0 ∧
    nashColStrategy ⟨5, by decide⟩ > 0 := by
  native_decide

end PokemonLean.RealMetagame
