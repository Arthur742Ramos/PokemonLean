import PokemonLean.Basic

namespace PokemonLean.MixedStrategy

open PokemonLean

structure PureStrategy where
  action : Action
  payoff : Nat
  deriving Repr, DecidableEq

/-- A mixed strategy is just a finite support of pure strategies.
We measure its "totalWeight" as the size of the support. -/
structure MixedStrategy where
  support : List PureStrategy
  deriving Repr

def totalWeight (s : MixedStrategy) : Nat :=
  s.support.length

def weight (s : MixedStrategy) (strategy : PureStrategy) : Nat :=
  if strategy ∈ s.support then 1 else 0

def expectedPayoff (s : MixedStrategy) : Nat :=
  s.support.foldl (fun acc strat => acc + strat.payoff * weight s strat) 0

theorem expectedPayoff_nil :
    expectedPayoff { support := [] } = 0 := by
  rfl

theorem expectedPayoff_nonneg (s : MixedStrategy) :
    0 ≤ expectedPayoff s := by
  simp [expectedPayoff]

def normalize (s : MixedStrategy) : MixedStrategy :=
  if totalWeight s = 0 then s else s

def strategyDominates (s1 s2 : PureStrategy) : Prop :=
  s2.payoff ≤ s1.payoff

theorem strategyDominates_refl (s : PureStrategy) : strategyDominates s s := by
  simp [strategyDominates]

theorem strategyDominates_trans (s1 s2 s3 : PureStrategy) :
    strategyDominates s1 s2 → strategyDominates s2 s3 → strategyDominates s1 s3 := by
  intro h12 h23
  exact Nat.le_trans h23 h12

def mixedBestResponse (s : MixedStrategy) (best : PureStrategy) : Prop :=
  ∀ strat ∈ s.support, strat.payoff ≤ best.payoff

def pureBestResponse : List PureStrategy → Option PureStrategy
  | [] => none
  | strat :: rest =>
      match pureBestResponse rest with
      | none => some strat
      | some b => if strat.payoff > b.payoff then some strat else some b

def pureBestResponseOf (s : MixedStrategy) : Option PureStrategy :=
  pureBestResponse s.support

theorem pureBestResponse_mem (s : MixedStrategy) (best : PureStrategy)
    (h : pureBestResponseOf s = some best) :
    best ∈ s.support := by
  cases s with
  | mk support =>
    unfold pureBestResponseOf at h
    -- now `h : pureBestResponse support = some best`
    induction support generalizing best with
    | nil =>
        have : False := by
          simp [pureBestResponse] at h
        contradiction
    | cons strat rest ih =>
        cases hRest : pureBestResponse rest with
        | none =>
            have hEq : strat = best := by
              have : some strat = some best := by
                simpa [pureBestResponse, hRest] using h
              exact Option.some.inj this
            subst hEq
            simp
        | some b =>
            by_cases hgt : strat.payoff > b.payoff
            · have hEq : strat = best := by
                have : some strat = some best := by
                  simpa [pureBestResponse, hRest, hgt] using h
                exact Option.some.inj this
              subst hEq
              simp
            · have hEq : b = best := by
                have : some b = some best := by
                  simpa [pureBestResponse, hRest, hgt] using h
                exact Option.some.inj this
              subst hEq
              have hbMem : b ∈ rest := ih (best := b) (by simpa using hRest)
              simp [hbMem]

def mixedStrategyValue (s : MixedStrategy) : Nat :=
  if totalWeight s = 0 then 0 else expectedPayoff s / totalWeight s

theorem mixedStrategyValue_zero (s : MixedStrategy) (h : totalWeight s = 0) :
    mixedStrategyValue s = 0 := by
  simp [mixedStrategyValue, h]

def supportNonempty (s : MixedStrategy) : Prop :=
  s.support ≠ []

theorem supportNonempty_of_positive_weight (s : MixedStrategy) (h : totalWeight s > 0) :
    supportNonempty s := by
  intro hNil
  -- if the support were empty, the length would be 0
  have hEq : totalWeight s = 0 := by
    simp [totalWeight, hNil]
  exact (Nat.ne_of_gt h) hEq

structure Game where
  strategiesA : List PureStrategy
  strategiesB : List PureStrategy
  payoffA : PureStrategy → PureStrategy → Nat
  payoffB : PureStrategy → PureStrategy → Nat

def mixedPayoff (sA sB : MixedStrategy) (payoff : PureStrategy → PureStrategy → Nat) : Nat :=
  sA.support.foldl (fun acc a =>
    sB.support.foldl (fun acc2 b => acc2 + payoff a b * weight sA a * weight sB b) acc) 0

theorem mixedPayoff_nonneg (sA sB : MixedStrategy) (payoff : PureStrategy → PureStrategy → Nat) :
    0 ≤ mixedPayoff sA sB payoff := by
  simp [mixedPayoff]

def isBestResponse (sA sB : MixedStrategy) (payoff : PureStrategy → PureStrategy → Nat) : Prop :=
  ∀ a ∈ sA.support, ∀ a' ∈ sA.support,
    mixedPayoff { support := [a] } sB payoff ≤
      mixedPayoff { support := [a'] } sB payoff

def mixedNash (sA sB : MixedStrategy) (game : Game) : Prop :=
  isBestResponse sA sB game.payoffA ∧ isBestResponse sB sA game.payoffB

def Game.swap (game : Game) : Game :=
  { strategiesA := game.strategiesB
    strategiesB := game.strategiesA
    payoffA := game.payoffB
    payoffB := game.payoffA }

theorem mixedNash_swap (sA sB : MixedStrategy) (game : Game) :
    mixedNash sA sB game → mixedNash sB sA game.swap := by
  intro h
  exact ⟨h.2, h.1⟩

end PokemonLean.MixedStrategy
