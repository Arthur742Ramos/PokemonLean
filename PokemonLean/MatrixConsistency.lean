/-
  PokemonLean/MatrixConsistency.lean — Cross-consistency of matchup representations

  Proves that the Array-based matchup matrix in NashEquilibrium.lean
  (`realMatchupData` / `realMatchupMatrix14`) is consistent with the
  function-based `matchupWR` in RealMetagame.lean.

  This ensures that the Nash equilibrium computation and the metagame
  analysis are working from identical data.
-/
import PokemonLean.NashEquilibrium
import PokemonLean.RealMetagame

namespace PokemonLean.MatrixConsistency

open PokemonLean.NashEquilibrium
open PokemonLean.RealMetagame

/-- The Array-based matchup matrix used for Nash equilibrium computation
    (`realMatchupMatrix14`) agrees entry-by-entry with the canonical
    function-based `matchupWR` from RealMetagame.lean. -/
theorem matrix_consistency :
    ∀ i j : Fin 14, realMatchupMatrix14 i j =
      ((matchupWR (Deck.ofFin i) (Deck.ofFin j) : Int) : Rat) := by
  native_decide

/-- The two FiniteGame definitions (realMetaGame14 from NashEquilibrium and
    realMetaGame from RealMetagame) use the same matrix values. -/
theorem game_matrix_consistency :
    ∀ i j : Fin 14, realMetaGame14.matrix i j = realMetaGame.matrix i j := by
  native_decide

end PokemonLean.MatrixConsistency
