/-
  PokemonLean/FullReplicator.lean — Full 14-deck replicator dynamics

  Proves which decks grow and which shrink under one replicator step
  using the COMPLETE 14×14 matchup matrix and observed meta shares
  from Trainer Hill (Jan–Feb 2026).

  Key results:
  - Dragapult Dusknoir's fitness is BELOW average → share should decline
  - Grimmsnarl Froslass's fitness is ABOVE average → share should grow
  - Alakazam has the WORST fitness of all 14 decks → strongest extinction pressure
  - Full classification: 5 growers, 9 shrinkers
-/
import PokemonLean.EvolutionaryDynamics

namespace PokemonLean.FullReplicator

open PokemonLean.NashEquilibrium
open PokemonLean.RealMetagame
open PokemonLean.EvolutionaryDynamics

-- ============================================================================
-- NORMALIZED META SHARES (sum to 1)
-- ============================================================================

/-- Normalized meta shares: each deck's share divided by 695 (the top-14 total).
    This gives a proper probability distribution over the 14 decks. -/
def normalizedShares : MetaShare 14 := fun i =>
  ((metaShare (Deck.ofFin i) : Int) : Rat) / (695 : Rat)

/-- The normalized shares form a valid meta share (sum to 1). -/
theorem normalizedShares_valid : IsMetaShare 14 normalizedShares := by
  native_decide

-- ============================================================================
-- PAYOFF MATRIX (win rates as rationals)
-- ============================================================================

/-- The 14×14 payoff matrix with win rates scaled to [0,1] rationals.
    Entry (i,j) = matchupWR(i,j) / 1000. -/
def fullPayoff : PayoffMatrix 14 := fun i j =>
  ((matchupWR (Deck.ofFin i) (Deck.ofFin j) : Int) : Rat) / (1000 : Rat)

-- ============================================================================
-- FITNESS COMPUTATIONS
-- ============================================================================

/-- Fitness of deck i against the normalized observed field. -/
abbrev deckFitness (i : Fin 14) : Rat :=
  fitness 14 fullPayoff normalizedShares i

/-- Average fitness across the observed metagame. -/
abbrev metaAvgFitness : Rat :=
  avgFitness 14 fullPayoff normalizedShares

-- ============================================================================
-- DECK INDICES
-- ============================================================================

def ixDragapult     : Fin 14 := ⟨0,  by omega⟩
def ixGholdengo     : Fin 14 := ⟨1,  by omega⟩
def ixGrimmsnarl    : Fin 14 := ⟨2,  by omega⟩
def ixMegaAbsol     : Fin 14 := ⟨3,  by omega⟩
def ixGardevoir     : Fin 14 := ⟨4,  by omega⟩
def ixCharNoctowl   : Fin 14 := ⟨5,  by omega⟩
def ixGardJellicent : Fin 14 := ⟨6,  by omega⟩
def ixCharPidgeot   : Fin 14 := ⟨7,  by omega⟩
def ixDragChar      : Fin 14 := ⟨8,  by omega⟩
def ixRagingBolt    : Fin 14 := ⟨9,  by omega⟩
def ixNsZoroark     : Fin 14 := ⟨10, by omega⟩
def ixAlakazam      : Fin 14 := ⟨11, by omega⟩
def ixKangaskhan    : Fin 14 := ⟨12, by omega⟩
def ixCeruledge     : Fin 14 := ⟨13, by omega⟩

-- ============================================================================
-- CORE REPLICATOR PREDICTIONS
-- ============================================================================

/-- **Dragapult decline**: Dragapult Dusknoir's fitness is below the population average.
    Despite being the most popular deck (15.5%), it has too many losing matchups.
    Under replicator dynamics, its share should decrease. -/
theorem full_replicator_dragapult_decline :
    deckFitness ixDragapult < metaAvgFitness := by
  native_decide

/-- **Grimmsnarl growth**: Grimmsnarl Froslass's fitness is above the population average.
    It has strong matchups across the board (best non-mirror average).
    Under replicator dynamics, its share should increase. -/
theorem full_replicator_grimmsnarl_growth :
    deckFitness ixGrimmsnarl > metaAvgFitness := by
  native_decide

/-- **Alakazam worst**: Alakazam Dudunsparce has the lowest fitness of all 14 decks.
    It faces the strongest extinction pressure under replicator dynamics. -/
theorem full_replicator_alakazam_worst :
    ∀ i : Fin 14, deckFitness ixAlakazam ≤ deckFitness i := by
  native_decide

-- ============================================================================
-- FULL FITNESS RANKING
-- ============================================================================

/-- **Grimmsnarl is the fittest**: Grimmsnarl Froslass has the highest fitness
    of all 14 decks against the observed metagame. -/
theorem full_replicator_grimmsnarl_fittest :
    ∀ i : Fin 14, deckFitness i ≤ deckFitness ixGrimmsnarl := by
  native_decide

/-- **Mega Absol above average**: Mega Absol Box fitness exceeds average. -/
theorem full_replicator_mega_absol_growth :
    deckFitness ixMegaAbsol > metaAvgFitness := by
  native_decide

/-- **Gardevoir above average**: Gardevoir fitness exceeds average. -/
theorem full_replicator_gardevoir_growth :
    deckFitness ixGardevoir > metaAvgFitness := by
  native_decide

/-- **Kangaskhan above average**: KangaskhanBouffalant fitness exceeds average. -/
theorem full_replicator_kangaskhan_growth :
    deckFitness ixKangaskhan > metaAvgFitness := by
  native_decide

/-- **DragapultCharizard above average**: DragapultCharizard fitness exceeds average. -/
theorem full_replicator_dragchar_growth :
    deckFitness ixDragChar > metaAvgFitness := by
  native_decide

-- ============================================================================
-- REPLICATOR STEP VERIFICATION
-- ============================================================================

/-- After one replicator step with dt=1/10, shares still sum to 1. -/
theorem full_replicator_step_conservation :
    sumFin 14 (replicatorStep 14 fullPayoff normalizedShares (1/10)) = 1 := by
  native_decide

/-- Grimmsnarl's share increases after one replicator step. -/
theorem grimmsnarl_share_increases :
    replicatorStep 14 fullPayoff normalizedShares (1/10) ixGrimmsnarl
    > normalizedShares ixGrimmsnarl := by
  native_decide

/-- Dragapult's share decreases after one replicator step. -/
theorem dragapult_share_decreases :
    replicatorStep 14 fullPayoff normalizedShares (1/10) ixDragapult
    < normalizedShares ixDragapult := by
  native_decide

/-- Ceruledge's share decreases after one replicator step. -/
theorem ceruledge_share_decreases :
    replicatorStep 14 fullPayoff normalizedShares (1/10) ixCeruledge
    < normalizedShares ixCeruledge := by
  native_decide

-- ============================================================================
-- GROWERS vs SHRINKERS CLASSIFICATION
-- ============================================================================

/-- Complete classification: the 5 decks that GROW under replicator dynamics
    (fitness above average). -/
theorem growers_above_average :
    deckFitness ixGrimmsnarl > metaAvgFitness ∧
    deckFitness ixMegaAbsol  > metaAvgFitness ∧
    deckFitness ixGardevoir  > metaAvgFitness ∧
    deckFitness ixDragChar   > metaAvgFitness ∧
    deckFitness ixKangaskhan > metaAvgFitness := by
  native_decide

/-- Complete classification: the 9 decks that SHRINK under replicator dynamics
    (fitness below average). -/
theorem shrinkers_below_average :
    deckFitness ixDragapult   < metaAvgFitness ∧
    deckFitness ixGholdengo   < metaAvgFitness ∧
    deckFitness ixCharNoctowl < metaAvgFitness ∧
    deckFitness ixGardJellicent < metaAvgFitness ∧
    deckFitness ixCharPidgeot < metaAvgFitness ∧
    deckFitness ixRagingBolt  < metaAvgFitness ∧
    deckFitness ixNsZoroark   < metaAvgFitness ∧
    deckFitness ixAlakazam    < metaAvgFitness ∧
    deckFitness ixCeruledge   < metaAvgFitness := by
  native_decide

end PokemonLean.FullReplicator
