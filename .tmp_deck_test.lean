import PokemonLean.DeckConsistency
import Mathlib

open PokemonLean.DeckConsistency

example : choose 5 2 = 10 := by
  decide

example : choose 5 2 = 10 := by
  norm_num [choose]

example : choose 60 7 = 386206920 := by
  decide
