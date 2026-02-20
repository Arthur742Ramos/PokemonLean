import Lean.Data.Rat
import PokemonLean.Core.Types

namespace PokemonLean.NashEquilibrium

abbrev Rat := Lean.Rat

instance decidableForallFin {n : Nat} {P : Fin n → Prop} [∀ i, Decidable (P i)] :
    Decidable (∀ i, P i) := by
  induction n with
  | zero =>
      refine isTrue ?_
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      refine (decidable_of_iff (P 0 ∧ ∀ i : Fin n, P i.succ) Fin.forall_fin_succ.symm)

instance decidableExistsFin {n : Nat} {P : Fin n → Prop} [∀ i, Decidable (P i)] :
    Decidable (∃ i, P i) := by
  induction n with
  | zero =>
      refine isFalse ?_
      intro h
      rcases h with ⟨i, _⟩
      exact Fin.elim0 i
  | succ n ih =>
      refine (decidable_of_iff (P 0 ∨ ∃ i : Fin n, P i.succ) Fin.exists_fin_succ.symm)

/-- Finite game with `n` players, `m` pure strategies each, and a payoff matrix. -/
structure FiniteGame where
  n : Nat
  m : Nat
  payoff : Fin n → Fin m → Rat
  matrix : Fin m → Fin m → Rat

abbrev MixedStrategy (m : Nat) := Fin m → Rat

def sumFin (m : Nat) (f : Fin m → Rat) : Rat :=
  Fin.foldl m (fun acc i => acc + f i) 0

def IsMixedStrategy (m : Nat) (s : MixedStrategy m) : Prop :=
  (∀ i : Fin m, 0 ≤ s i) ∧ sumFin m s = 1

instance (m : Nat) (s : MixedStrategy m) : Decidable (IsMixedStrategy m s) := by
  unfold IsMixedStrategy
  infer_instance

def rowPurePayoff (g : FiniteGame) (row : Fin g.m) (s2 : MixedStrategy g.m) : Rat :=
  sumFin g.m (fun j => s2 j * g.matrix row j)

def colPurePayoff (g : FiniteGame) (s1 : MixedStrategy g.m) (col : Fin g.m) : Rat :=
  sumFin g.m (fun i => s1 i * g.matrix i col)

def expectedPayoff (g : FiniteGame) (s1 s2 : MixedStrategy g.m) : Rat :=
  sumFin g.m (fun i => s1 i * rowPurePayoff g i s2)

/-- Zero-sum Nash condition: row player cannot improve upward, column cannot lower row payoff. -/
def NashEquilibrium (g : FiniteGame) (s1 s2 : MixedStrategy g.m) : Prop :=
  IsMixedStrategy g.m s1 ∧ IsMixedStrategy g.m s2 ∧
    (∀ i : Fin g.m, rowPurePayoff g i s2 ≤ expectedPayoff g s1 s2) ∧
    (∀ j : Fin g.m, expectedPayoff g s1 s2 ≤ colPurePayoff g s1 j)

instance (g : FiniteGame) (s1 s2 : MixedStrategy g.m) : Decidable (NashEquilibrium g s1 s2) := by
  unfold NashEquilibrium
  infer_instance

/-- Recursive argmax over the finite set `Fin (n+1)`. -/
def argmaxFinSucc : ∀ {n : Nat}, (Fin (n + 1) → Rat) → Fin (n + 1)
  | 0, _ => 0
  | n + 1, f =>
      let tail : Fin (n + 1) → Rat := fun i => f i.succ
      let bestTail : Fin (n + 1) := argmaxFinSucc tail
      if f 0 ≤ f bestTail.succ then bestTail.succ else 0

def argmaxFin {m : Nat} (h : 0 < m) (f : Fin m → Rat) : Fin m := by
  cases m with
  | zero =>
      cases Nat.not_lt_zero 0 h
  | succ n =>
      exact argmaxFinSucc f

def BestResponse (g : FiniteGame) (opp : MixedStrategy g.m) (br : Fin g.m) : Prop :=
  ∃ h : 0 < g.m, br = argmaxFin h (fun i => rowPurePayoff g i opp)

theorem bestResponse_exists (g : FiniteGame) (h : 0 < g.m) (opp : MixedStrategy g.m) :
    ∃ br : Fin g.m, BestResponse g opp br := by
  refine ⟨argmaxFin h (fun i => rowPurePayoff g i opp), ?_⟩
  exact ⟨h, rfl⟩

def ratMin (a b : Rat) : Rat := if a ≤ b then a else b

def ratMax (a b : Rat) : Rat := if a ≤ b then b else a

def maximin2x2 (a00 a01 a10 a11 : Rat) : Rat :=
  ratMax (ratMin a00 a01) (ratMin a10 a11)

def minimax2x2 (a00 a01 a10 a11 : Rat) : Rat :=
  ratMin (ratMax a00 a10) (ratMax a01 a11)

theorem minimax_theorem_2x2_concrete :
    minimax2x2 (2 : Rat) (1 : Rat) (3 : Rat) (0 : Rat) =
    maximin2x2 (2 : Rat) (1 : Rat) (3 : Rat) (0 : Rat) := by
  decide

def mix3 (a c k : Rat) : MixedStrategy 3
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => c
  | _ => k

structure Mix3 where
  aggro : Rat
  control : Rat
  combo : Rat
  deriving Repr, DecidableEq

def Mix3.toStrategy (w : Mix3) : MixedStrategy 3 :=
  mix3 w.aggro w.control w.combo

def natFrac (n d : Nat) : Rat :=
  if d = 0 then 0 else (Int.ofNat n : Rat) / (Int.ofNat d : Rat)

def gridMix3 (denom : Nat) : List Mix3 :=
  (List.range (denom + 1)).flatMap (fun a =>
    (List.range (denom + 1)).flatMap (fun c =>
      (List.range (denom + 1)).foldr (fun k acc =>
        if a + c + k = denom then
          { aggro := natFrac a denom, control := natFrac c denom, combo := natFrac k denom } :: acc
        else
          acc) []))

def uniformMix3 : Mix3 :=
  { aggro := (1 : Rat) / (3 : Rat)
    control := (1 : Rat) / (3 : Rat)
    combo := (1 : Rat) / (3 : Rat) }

def uniform3 : MixedStrategy 3 := uniformMix3.toStrategy

def symmetricRpsMatrix : Fin 3 → Fin 3 → Rat
  | ⟨0, _⟩, ⟨0, _⟩ => 0
  | ⟨0, _⟩, ⟨1, _⟩ => 1
  | ⟨0, _⟩, _ => -1
  | ⟨1, _⟩, ⟨0, _⟩ => -1
  | ⟨1, _⟩, ⟨1, _⟩ => 0
  | ⟨1, _⟩, _ => 1
  | _, ⟨0, _⟩ => 1
  | _, ⟨1, _⟩ => -1
  | _, _ => 0

def symmetricRpsGame : FiniteGame :=
  { n := 2
    m := 3
    payoff := fun _ _ => 0
    matrix := symmetricRpsMatrix }

theorem uniform3_is_mixed : IsMixedStrategy 3 uniform3 := by
  decide

theorem symmetric_rps_uniform_is_nash :
    NashEquilibrium symmetricRpsGame uniform3 uniform3 := by
  decide

def symmetricNashOnThirds : List Mix3 :=
  (gridMix3 3).filter (fun w => decide (NashEquilibrium symmetricRpsGame w.toStrategy w.toStrategy))

theorem symmetric_rps_unique_uniform_on_thirds_grid :
    symmetricNashOnThirds = [uniformMix3] := by
  decide

theorem symmetric_rps_unique_uniform
    (w : Mix3)
    (hMem : w ∈ gridMix3 3)
    (hNash : NashEquilibrium symmetricRpsGame w.toStrategy w.toStrategy) :
    w = uniformMix3 := by
  have hIn : w ∈ symmetricNashOnThirds := by
    unfold symmetricNashOnThirds
    simp [hMem, hNash]
  rw [symmetric_rps_unique_uniform_on_thirds_grid] at hIn
  simpa using hIn

def asymmetricMatrix : Fin 3 → Fin 3 → Rat
  | ⟨0, _⟩, ⟨1, _⟩ => (1 : Rat) / (10 : Rat)
  | ⟨1, _⟩, ⟨0, _⟩ => -((1 : Rat) / (10 : Rat))
  | ⟨1, _⟩, ⟨2, _⟩ => (1 : Rat) / (5 : Rat)
  | ⟨2, _⟩, ⟨1, _⟩ => -((1 : Rat) / (5 : Rat))
  | ⟨2, _⟩, ⟨0, _⟩ => (1 : Rat) / (20 : Rat)
  | ⟨0, _⟩, ⟨2, _⟩ => -((1 : Rat) / (20 : Rat))
  | _, _ => 0

def asymmetricGame : FiniteGame :=
  { n := 2
    m := 3
    payoff := fun _ _ => 0
    matrix := asymmetricMatrix }

def asymmetricWeights : Mix3 :=
  { aggro := (4 : Rat) / (7 : Rat)
    control := (1 : Rat) / (7 : Rat)
    combo := (2 : Rat) / (7 : Rat) }

def aggroIx : Fin 3 := ⟨0, by decide⟩
def controlIx : Fin 3 := ⟨1, by decide⟩
def comboIx : Fin 3 := ⟨2, by decide⟩

theorem asymmetric_weights_is_mixed : IsMixedStrategy 3 asymmetricWeights.toStrategy := by
  decide

theorem asymmetric_weights_balance_pure_payoffs :
    rowPurePayoff asymmetricGame aggroIx asymmetricWeights.toStrategy = 0 ∧
    rowPurePayoff asymmetricGame controlIx asymmetricWeights.toStrategy = 0 ∧
    rowPurePayoff asymmetricGame comboIx asymmetricWeights.toStrategy = 0 := by
  decide

theorem asymmetric_weights_form_nash :
    NashEquilibrium asymmetricGame asymmetricWeights.toStrategy asymmetricWeights.toStrategy := by
  decide

def asymmetricNashOnSevenths : List Mix3 :=
  (gridMix3 7).filter (fun w => decide (NashEquilibrium asymmetricGame w.toStrategy w.toStrategy))

theorem asymmetric_unique_on_sevenths_grid :
    asymmetricNashOnSevenths = [asymmetricWeights] := by
  decide

theorem asymmetric_unique_weights
    (w : Mix3)
    (hMem : w ∈ gridMix3 7)
    (hNash : NashEquilibrium asymmetricGame w.toStrategy w.toStrategy) :
    w = asymmetricWeights := by
  have hIn : w ∈ asymmetricNashOnSevenths := by
    unfold asymmetricNashOnSevenths
    simp [hMem, hNash]
  rw [asymmetric_unique_on_sevenths_grid] at hIn
  simpa using hIn

end PokemonLean.NashEquilibrium
