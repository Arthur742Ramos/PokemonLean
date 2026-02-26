/-
  PokemonLean/StepSizeGeneral.lean — General symbolic step-size invariance

  For discrete replicator dynamics  x'_i = x_i + x_i · dt · (f_i − f̄),
  the sign of the change  x'_i − x_i = x_i · dt · (f_i − f̄)  depends
  only on the sign of  f_i − f̄,  not on the step size dt, provided
  x_i > 0 and dt > 0.

  Unlike StepSizeInvariance.lean which verifies this concretely for each of
  the 14 decks at several dt values via `native_decide`, here we prove the
  property once and for all over the integers by elementary sign reasoning.

  **Int↔Rat bridge (v10):**  The replicator dynamics use `Lean.Rat`.
  Section II proves step-size sign invariance directly over `Lean.Rat`
  by showing `sign(xi * dt * gap) = sign(gap)` when `xi, dt > 0`.
  The proof decomposes `Lean.Rat.mul` into `Int.tdiv` on numerators
  (GCD-scaled) and uses the fact that `tdiv` by a positive divisor
  preserves sign.  The only `native_decide` is for `(0 : Rat).num = 0`.
-/
import Lean.Data.Rat

namespace PokemonLean.StepSizeGeneral

/-! ## Auxiliary sign-extraction lemmas -/

/-- If a > 0, b > 0, and a * b * c > 0, then c > 0. -/
theorem pos_of_mul_pos_of_pos_pos (a b c : Int)
    (ha : 0 < a) (hb : 0 < b) (habc : 0 < a * b * c) : 0 < c :=
  Decidable.byContradiction fun hc =>
    have hc' : c ≤ 0 := Int.not_lt.mp hc
    have h1 := Int.mul_nonpos_of_nonneg_of_nonpos
                 (Int.le_of_lt (Int.mul_pos ha hb)) hc'
    Int.not_lt.mpr h1 habc

/-- If a > 0, b > 0, and a * b * c < 0, then c < 0. -/
theorem neg_of_mul_neg_of_pos_pos (a b c : Int)
    (ha : 0 < a) (hb : 0 < b) (habc : a * b * c < 0) : c < 0 :=
  Decidable.byContradiction fun hc =>
    have hc' : 0 ≤ c := Int.not_lt.mp hc
    have h1 := Int.mul_nonneg (Int.le_of_lt (Int.mul_pos ha hb)) hc'
    Int.not_lt.mpr h1 habc

/-- If a > 0, b > 0, and c < 0, then a * b * c < 0. -/
theorem mul_neg_of_pos_pos_neg (a b c : Int)
    (ha : 0 < a) (hb : 0 < b) (hc : c < 0) : a * b * c < 0 :=
  Decidable.byContradiction fun hn =>
    have h1 : 0 ≤ a * b * c := Int.not_lt.mp hn
    have h2 : a * b * c ≤ 0 :=
      Int.mul_nonpos_of_nonneg_of_nonpos
        (Int.le_of_lt (Int.mul_pos ha hb)) (Int.le_of_lt hc)
    have h3 : a * b * c = 0 := Int.le_antisymm h2 h1
    have hab : a * b ≠ 0 := Int.ne_of_gt (Int.mul_pos ha hb)
    have hc0 : c = 0 := by
      rcases Int.mul_eq_zero.mp h3 with h | h
      · exact absurd h hab
      · exact h
    Int.lt_irrefl 0 (hc0 ▸ hc)

/-! ## Core definitions and theorems -/

/-- The replicator step change δ_i = x_i · dt · (f_i − f̄).
    We work over `Int` for clean sign reasoning;
    rational dynamics are recovered by clearing denominators. -/
def replicatorDelta (xi dt fiMinusFbar : Int) : Int :=
  xi * dt * fiMinusFbar

/-- **Step-size invariance (growth direction).**
    If x_i > 0 and dt > 0, the positivity of the replicator delta
    depends only on (f_i − f̄), not on the magnitude of dt. -/
theorem replicator_sign_independent_of_dt
    (xi dt₁ dt₂ fiMinusFbar : Int)
    (hxi : 0 < xi) (hdt₁ : 0 < dt₁) (hdt₂ : 0 < dt₂) :
    (0 < replicatorDelta xi dt₁ fiMinusFbar) ↔
    (0 < replicatorDelta xi dt₂ fiMinusFbar) := by
  unfold replicatorDelta
  constructor
  · intro h
    exact Int.mul_pos (Int.mul_pos hxi hdt₂)
      (pos_of_mul_pos_of_pos_pos xi dt₁ fiMinusFbar hxi hdt₁ h)
  · intro h
    exact Int.mul_pos (Int.mul_pos hxi hdt₁)
      (pos_of_mul_pos_of_pos_pos xi dt₂ fiMinusFbar hxi hdt₂ h)

/-- **Step-size invariance (decline direction).**
    Symmetric to the growth case: negativity of the delta is also
    independent of the step size. -/
theorem replicator_decline_independent_of_dt
    (xi dt₁ dt₂ fiMinusFbar : Int)
    (hxi : 0 < xi) (hdt₁ : 0 < dt₁) (hdt₂ : 0 < dt₂) :
    (replicatorDelta xi dt₁ fiMinusFbar < 0) ↔
    (replicatorDelta xi dt₂ fiMinusFbar < 0) := by
  unfold replicatorDelta
  constructor
  · intro h
    exact mul_neg_of_pos_pos_neg xi dt₂ fiMinusFbar hxi hdt₂
      (neg_of_mul_neg_of_pos_pos xi dt₁ fiMinusFbar hxi hdt₁ h)
  · intro h
    exact mul_neg_of_pos_pos_neg xi dt₁ fiMinusFbar hxi hdt₁
      (neg_of_mul_neg_of_pos_pos xi dt₂ fiMinusFbar hxi hdt₂ h)

end PokemonLean.StepSizeGeneral

/-! ## Part II — Int↔Rat Bridge

The theorems in Part I work over `Int`. The concrete replicator dynamics in
`FullReplicator.lean` and `EvolutionaryDynamics.lean` use `Lean.Rat`
(abbrev'd to `Rat` via `NashEquilibrium.lean`).

We now prove step-size sign invariance directly for `Lean.Rat`:

> For `xi, dt, gap : Lean.Rat` with `xi > 0` and `dt > 0`,
> `0 < xi * dt * gap  ↔  0 < gap`   (growth direction)
> `xi * dt * gap < 0  ↔  gap < 0`   (decline direction)

The proof works by decomposing `Lean.Rat.mul` into `Int.tdiv` operations
on numerators (scaled by GCD factors) and showing that `tdiv` by a positive
divisor preserves the sign of the dividend. This means the paper can
truthfully state that the **general symbolic proof covers the concrete
`Rat` dynamics** — no `native_decide` is needed except for the single
fact `(0 : Lean.Rat).num = 0`.
-/

namespace PokemonLean.StepSizeRat

abbrev Rat := Lean.Rat

/-! ### Auxiliary: Nat division, Int case analysis, Int.tdiv sign -/

private theorem nat_div_pos_of_dvd {m d : Nat}
    (hm : 0 < m) (hd : 0 < d) (hdvd : d ∣ m) : 0 < m / d := by
  obtain ⟨k, rfl⟩ := hdvd; rw [Nat.mul_div_cancel_left k hd]
  cases k with | zero => simp at hm | succ n => exact Nat.succ_pos n

private theorem int_ofNat_of_pos {n : Int} (h : 0 < n) :
    ∃ m : Nat, n = Int.ofNat (m + 1) := by
  cases n with
  | ofNat m => cases m with
    | zero => exact absurd h (Int.lt_irrefl 0)
    | succ k => exact ⟨k, rfl⟩
  | negSucc m =>
    exact absurd h (Int.not_lt.mpr (Int.le_of_lt (Int.negSucc_lt_zero m)))

private theorem int_negSucc_of_neg {n : Int} (h : n < 0) :
    ∃ m : Nat, n = Int.negSucc m := by
  cases n with
  | ofNat m =>
    exact absurd h (Int.not_lt.mpr (Int.ofNat_le.mpr (Nat.zero_le m)))
  | negSucc m => exact ⟨m, rfl⟩

/-- Truncated division of a positive integer by a positive divisor that
    divides the absolute value yields a positive result. -/
private theorem int_tdiv_pos_of_pos {n : Int} {d : Nat}
    (hn : 0 < n) (hd : 0 < d) (hdvd : d ∣ n.natAbs) :
    0 < n.tdiv (↑d) := by
  obtain ⟨m, rfl⟩ := int_ofNat_of_pos hn
  exact Int.ofNat_lt.mpr (nat_div_pos_of_dvd (Nat.succ_pos m) hd hdvd)

/-- Truncated division of a negative integer by a positive divisor that
    divides the absolute value yields a negative result. -/
private theorem int_tdiv_neg_of_neg {n : Int} {d : Nat}
    (hn : n < 0) (hd : 0 < d) (hdvd : d ∣ n.natAbs) :
    n.tdiv (↑d) < 0 := by
  obtain ⟨m, rfl⟩ := int_negSucc_of_neg hn
  show -(Int.ofNat (Nat.succ m / d)) < 0
  change -(((Nat.succ m / d : Nat) : Int)) < 0
  have := nat_div_pos_of_dvd (Nat.succ_pos m) hd hdvd; omega

/-! ### Rat numerator sign under multiplication

`Lean.Rat.mul` computes:
  `(r * s).num = r.num.tdiv ↑g₂ * s.num.tdiv ↑g₁`
where `g₁ = gcd(r.den, |s.num|)` and `g₂ = gcd(|r.num|, s.den)`.

Since `g₂ ∣ |r.num|` and `g₁ ∣ |s.num|` (by properties of GCD),
`tdiv` is exact division and preserves sign. -/

/-- Product of two positive-numerator rationals has positive numerator. -/
theorem rat_mul_num_pos {r s : Rat} (hr : 0 < r.num) (hs : 0 < s.num) :
    0 < (r * s).num := by
  simp only [HMul.hMul, Mul.mul, Lean.Rat.mul]
  exact Int.mul_pos
    (int_tdiv_pos_of_pos hr
      (Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left (by omega)))
      (Nat.gcd_dvd_left ..))
    (int_tdiv_pos_of_pos hs
      (Nat.pos_of_ne_zero (Nat.gcd_ne_zero_right (by omega)))
      (Nat.gcd_dvd_right ..))

/-- Positive numerator times negative numerator gives negative numerator. -/
theorem rat_mul_num_neg_of_pos_neg {r s : Rat}
    (hr : 0 < r.num) (hs : s.num < 0) : (r * s).num < 0 := by
  simp only [HMul.hMul, Mul.mul, Lean.Rat.mul]
  exact Int.mul_neg_of_pos_of_neg
    (int_tdiv_pos_of_pos hr
      (Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left (by omega)))
      (Nat.gcd_dvd_left ..))
    (int_tdiv_neg_of_neg hs
      (Nat.pos_of_ne_zero (Nat.gcd_ne_zero_right (by omega)))
      (Nat.gcd_dvd_right ..))

/-- Multiplying by a zero-numerator rational gives zero numerator. -/
theorem rat_mul_num_zero_right {r s : Rat} (hs : s.num = 0) :
    (r * s).num = 0 := by
  simp only [HMul.hMul, Mul.mul, Lean.Rat.mul]
  have : s.num.natAbs = 0 := by omega
  simp only [this, Nat.gcd_zero_right]; rw [hs]; simp [Int.tdiv, Int.mul_zero]

private theorem rat_mul_num_nonpos_of_pos_nonpos {r s : Rat}
    (hr : 0 < r.num) (hs : s.num ≤ 0) : (r * s).num ≤ 0 :=
  Decidable.byCases (p := s.num = 0)
    (fun heq => (rat_mul_num_zero_right heq) ▸ Int.le_refl 0)
    (fun hne => Int.le_of_lt (rat_mul_num_neg_of_pos_neg hr
      (Decidable.byContradiction fun h =>
        hne (Int.le_antisymm hs (Int.not_lt.mp h)))))

private theorem rat_mul_num_nonneg_of_pos_nonneg {r s : Rat}
    (hr : 0 < r.num) (hs : 0 ≤ s.num) : 0 ≤ (r * s).num :=
  Decidable.byCases (p := s.num = 0)
    (fun heq => (rat_mul_num_zero_right heq) ▸ Int.le_refl 0)
    (fun hne => Int.le_of_lt (rat_mul_num_pos hr
      (Decidable.byContradiction fun h =>
        hne (Int.le_antisymm (Int.not_lt.mp h) hs))))

/-! ### Rat positivity ↔ numerator positivity -/

/-- The only `native_decide` in the bridge: `(0 : Lean.Rat).num = 0`. -/
private theorem lean_rat_zero_num : (0 : Rat).num = 0 := by native_decide

/-- A `Lean.Rat` is positive iff its numerator is positive. -/
theorem rat_pos_iff (r : Rat) : (0 : Rat) < r ↔ 0 < r.num := by
  show Lean.Rat.lt 0 r = true ↔ 0 < r.num
  simp only [Lean.Rat.lt, lean_rat_zero_num]; simp (config := { decide := true })

/-- A `Lean.Rat` is negative iff its numerator is negative. -/
theorem rat_neg_iff (r : Rat) : r < (0 : Rat) ↔ r.num < 0 := by
  show Lean.Rat.lt r 0 = true ↔ r.num < 0
  simp only [Lean.Rat.lt, lean_rat_zero_num]
  simp (config := { decide := true }); omega

/-! ### Main bridge theorems -/

/-- Multiplication preserves strict positivity for `Lean.Rat`. -/
theorem rat_mul_pos {r s : Rat}
    (hr : (0 : Rat) < r) (hs : (0 : Rat) < s) : (0 : Rat) < r * s :=
  (rat_pos_iff _).mpr
    (rat_mul_num_pos ((rat_pos_iff r).mp hr) ((rat_pos_iff s).mp hs))

/-- **Step-size sign invariance for `Lean.Rat` (growth direction).**
    If `xi > 0` and `dt > 0`, then `xi * dt * gap > 0 ↔ gap > 0`. -/
theorem rat_replicator_sign_pos (xi dt gap : Rat)
    (hxi : (0 : Rat) < xi) (hdt : (0 : Rat) < dt) :
    ((0 : Rat) < xi * dt * gap) ↔ ((0 : Rat) < gap) := by
  constructor
  · intro h
    rw [rat_pos_iff] at h hxi hdt ⊢
    exact Decidable.byContradiction fun hc =>
      Int.not_lt.mpr
        (rat_mul_num_nonpos_of_pos_nonpos
          (rat_mul_num_pos hxi hdt) (Int.not_lt.mp hc)) h
  · intro h; exact rat_mul_pos (rat_mul_pos hxi hdt) h

/-- **Step-size sign invariance for `Lean.Rat` (decline direction).**
    If `xi > 0` and `dt > 0`, then `xi * dt * gap < 0 ↔ gap < 0`. -/
theorem rat_replicator_sign_neg (xi dt gap : Rat)
    (hxi : (0 : Rat) < xi) (hdt : (0 : Rat) < dt) :
    (xi * dt * gap < (0 : Rat)) ↔ (gap < (0 : Rat)) := by
  constructor
  · intro h
    rw [rat_neg_iff] at h ⊢; rw [rat_pos_iff] at hxi hdt
    exact Decidable.byContradiction fun hc =>
      Int.not_lt.mpr
        (rat_mul_num_nonneg_of_pos_nonneg
          (rat_mul_num_pos hxi hdt) (Int.not_lt.mp hc)) h
  · intro h
    rw [rat_neg_iff] at h ⊢; rw [rat_pos_iff] at hxi hdt
    exact rat_mul_num_neg_of_pos_neg (rat_mul_num_pos hxi hdt) h

/-- **Step-size invariance for `Lean.Rat` (dt-independence).**
    Changing the step size `dt` (keeping it positive) does not change
    whether the replicator delta is positive.  Direct `Rat` analogue
    of `replicator_sign_independent_of_dt`. -/
theorem rat_replicator_sign_independent_of_dt
    (xi dt₁ dt₂ gap : Rat)
    (hxi : (0 : Rat) < xi) (hdt₁ : (0 : Rat) < dt₁) (hdt₂ : (0 : Rat) < dt₂) :
    ((0 : Rat) < xi * dt₁ * gap) ↔ ((0 : Rat) < xi * dt₂ * gap) :=
  (rat_replicator_sign_pos xi dt₁ gap hxi hdt₁).trans
    (rat_replicator_sign_pos xi dt₂ gap hxi hdt₂).symm

end PokemonLean.StepSizeRat
