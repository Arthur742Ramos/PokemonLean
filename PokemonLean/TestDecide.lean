import PokemonLean.NashEquilibrium

-- The blockers for `decide`:
-- 1. sumFin uses Fin.foldl which is not kernel-reducible
-- 2. Mix3.toStrategy uses a match on Fin values  
-- 3. NashEquilibrium unfolds into nested sumFin calls
-- 
-- Can we at least get `decide` to work on a manually-expanded version?

open PokemonLean.NashEquilibrium in
theorem test_rat_sum_manual :
    (1 : Lean.Rat) / 3 + (1 : Lean.Rat) / 3 + (1 : Lean.Rat) / 3 = 1 := by
  decide

-- Now try the Nash condition with manually expanded payoffs
open PokemonLean.NashEquilibrium in
theorem test_nash_condition_manual :
    -- RPS uniform Nash: each row pure payoff = 0
    (1 : Lean.Rat) / 3 * 0 + (1 : Lean.Rat) / 3 * (-1) + (1 : Lean.Rat) / 3 * 1 = 0 := by
  decide

