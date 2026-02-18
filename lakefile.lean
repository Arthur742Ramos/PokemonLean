import Lake
open Lake DSL

package «PokemonLean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «PokemonLean» where
  roots := #[`PokemonLean, `Core.Types, `Core.BenchLimits, `Core.BenchProtection, `Core.BoardPositioning]
