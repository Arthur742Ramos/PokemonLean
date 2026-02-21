/-
  PokemonLean/DragapultDominated.lean — Dragapult is excluded from all Nash equilibria

  Proves that Dragapult Dusknoir (index 0) receives zero weight in:
  1. The asymmetric Nash row strategy
  2. The asymmetric Nash column strategy
  3. The symmetric Nash equilibrium

  Additionally proves Dragapult is strictly suboptimal against the Nash
  column mix, meaning it cannot appear in ANY best-response support.
-/
import PokemonLean.NashEquilibrium
import PokemonLean.SymmetricNash

namespace PokemonLean.DragapultDominated

open PokemonLean.NashEquilibrium
open PokemonLean.SymmetricNash

/-- Dragapult has zero weight in the row player's Nash strategy. -/
theorem dragapult_zero_row : realNashRow ⟨0, by omega⟩ = 0 := by native_decide

/-- Dragapult has zero weight in the column player's Nash strategy. -/
theorem dragapult_zero_col : realNashCol ⟨0, by omega⟩ = 0 := by native_decide

/-- Dragapult has zero weight in the symmetric Nash equilibrium. -/
theorem dragapult_zero_symmetric : symNashStrategy ⟨0, by omega⟩ = 0 := by native_decide

/-- Dragapult is strictly suboptimal as a best response to the Nash column strategy.
    Its payoff is strictly less than the game value, so it can never be in any
    best-response support. -/
private def dragapultIdx : Fin realMetaGame14.m := ⟨0, by native_decide⟩

theorem dragapult_strictly_suboptimal :
    rowPurePayoff realMetaGame14 dragapultIdx realNashCol < realNashValue := by
  native_decide

/-- Combined: Dragapult gets zero weight in all verified equilibria AND is strictly
    suboptimal against the Nash column mix, meaning it cannot appear in any
    Nash equilibrium that uses this column strategy as a best response. -/
theorem dragapult_excluded_from_equilibrium :
    realNashRow ⟨0, by omega⟩ = 0 ∧
    realNashCol ⟨0, by omega⟩ = 0 ∧
    symNashStrategy ⟨0, by omega⟩ = 0 ∧
    rowPurePayoff realMetaGame14 dragapultIdx realNashCol < realNashValue := by
  constructor; · native_decide
  constructor; · native_decide
  constructor; · native_decide
  · native_decide

end PokemonLean.DragapultDominated
