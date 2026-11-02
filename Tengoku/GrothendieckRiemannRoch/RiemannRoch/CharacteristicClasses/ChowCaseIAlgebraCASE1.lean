/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.RingTheory.PowerSeries.Derivative
import Tengoku.Seed.RingTheory.PowerSeries.Exp
import Tengoku.Seed.RingTheory.PowerSeries.Inverse
import Tengoku.Seed.RingTheory.PowerSeries.Trunc
import Tengoku.Seed.Algebra.Polynomial.AlgebraMap
import Tengoku.Seed.RingTheory.Binomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Route CASE1 (algebra core): `∫ e^{mH} · td(H)^{n+1} = binom(n+m, n)` on `ℙⁿ`

Pure algebra, no geometry.  Let `T = X / (1 - e^{-X}) ∈ ℚ⟦X⟧` (Todd series of a line bundle
with `c₁ = X`).  Then

* `coeff_n (T^{n+1}) = 1`                                     (`coeff_tdSer_pow_self`)
* `coeff_n (e^{mX} · T^{n+1}) = binom(n+m, n)` for `m : ℕ`     (`coeff_exp_mul_tdSer_pow`)

(Pascal recursion `F(m+1,n+1) = F(m,n+1) + F(m+1,n)` from `e^{(m+1)X} - e^{mX} = e^{(m+1)X} (1-e^{-X})`,
and the base `F(0,n) = 1` from the ODE `X T' = T + X T - T²` by an induction with no residues.)

Operator form: for any `ℚ`-module `M`, endomorphism `H` (the operator `c₁(O(1)) ∩ -`), vector `v`
(the class `[ℙⁿ]`) with `H^{n+1} v = 0`, and functional `Φ` (`deg ∘ π_*`) with `Φ(H^p v) = [p = n]`
for `p ≤ n`, we have `Φ(ch_n(O(m)) (td_n)^{n+1} v) = binom(n+m, n)`, where `ch_n`, `td_n` are the
truncations at order `n` (exact on `v` since `H^{n+1} v = 0`).
-/

set_option autoImplicit false
noncomputable section
open PowerSeries

namespace AlgebraicGeometry.Chow.M7.CASE1

/-- `(1 - e^{-X}) / X`.-/
def eSer : ℚ⟦X⟧ := PowerSeries.mk fun j => (-1 : ℚ) ^ j / ((j + 1).factorial : ℚ)

/-- The Todd series `X / (1 - e^{-X}) = td(c₁ = X)` of a line bundle.-/
def tdSer : ℚ⟦X⟧ := eSer⁻¹

theorem constantCoeff_eSer : constantCoeff eSer = 1 := by
  simp [eSer, ← coeff_zero_eq_constantCoeff_apply]

theorem constantCoeff_tdSer : constantCoeff tdSer = 1 := by
  simp [tdSer, constantCoeff_inv, constantCoeff_eSer]

theorem eSer_mul_tdSer : eSer * tdSer = 1 :=
  PowerSeries.mul_inv_cancel _ (by simp [constantCoeff_eSer])

/-- `X · e = 1 - e^{-X}`.-/
theorem X_mul_eSer : (X : ℚ⟦X⟧) * eSer = 1 - rescale (-1 : ℚ) (exp ℚ) := by
  ext j
  rcases j with _ | j
  · have h : constantCoeff (rescale (-1 : ℚ) (exp ℚ)) = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale]
      simp [coeff_exp]
    simp [h]
  · rw [coeff_succ_X_mul, map_sub, coeff_one, coeff_rescale, coeff_exp]
    simp only [eSer, coeff_mk, Nat.succ_ne_zero, ite_false, zero_sub, eq_ratCast, one_div]
    rw [pow_succ]
    simp only [Nat.factorial_succ]
    push_cast
    ring

/-- `X · e' = 1 - e - X e`.-/
theorem X_mul_derivative_eSer :
    (X : ℚ⟦X⟧) * d⁄dX ℚ eSer = 1 - eSer - X * eSer := by
  ext j
  rcases j with _ | j
  · simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_eSer]
  · rw [coeff_succ_X_mul, coeff_derivative, map_sub, map_sub, coeff_one, coeff_succ_X_mul]
    simp only [eSer, coeff_mk, Nat.succ_ne_zero, ite_false, zero_sub]
    simp only [pow_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem X_mul_derivative_tdSer :
    (X : ℚ⟦X⟧) * d⁄dX ℚ tdSer = tdSer + X * tdSer - tdSer ^ 2 := by
  have h1 := eSer_mul_tdSer
  have h2 := X_mul_derivative_eSer
  have h3 : d⁄dX ℚ tdSer = -tdSer ^ 2 * d⁄dX ℚ eSer := by
    rw [tdSer, derivative_inv']
  rw [h3]
  linear_combination (-tdSer ^ 2) * h2 + (tdSer + X * tdSer) * h1

/-- `[X^n] T^{n+1} = 1`: the `m = 0` case (`χ(ℙⁿ, O) = 1`).-/
theorem coeff_tdSer_pow_self (n : ℕ) : coeff n (tdSer ^ (n + 1)) = 1 := by
  induction n with
  | zero => simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_tdSer]
  | succ n ih =>
    set T := tdSer with hTdef
    have hT : (X : ℚ⟦X⟧) * d⁄dX ℚ T = T + X * T - T ^ 2 := X_mul_derivative_tdSer
    have hdG : d⁄dX ℚ (T ^ (n + 1)) = C ((n : ℚ) + 1) * T ^ n * d⁄dX ℚ T := by
      rw [derivative_pow]
      simp only [Nat.add_sub_cancel]
      congr 2
      rw [← map_natCast (C (R := ℚ))]
      push_cast
      rfl
    have key : C ((n : ℚ) + 1) * T ^ (n + 2) =
        C ((n : ℚ) + 1) * T ^ (n + 1) + X * (C ((n : ℚ) + 1) * T ^ (n + 1)) -
          X * d⁄dX ℚ (T ^ (n + 1)) := by
      rw [hdG]
      linear_combination (C ((n : ℚ) + 1) * T ^ n) * hT
    have hc := congrArg (coeff (n + 1)) key
    rw [coeff_C_mul, map_sub, map_add, coeff_C_mul, coeff_succ_X_mul, coeff_C_mul,
      coeff_succ_X_mul, coeff_derivative, ih] at hc
    have hne : ((n : ℚ) + 1) ≠ 0 := by positivity
    have : ((n : ℚ) + 1) * coeff (n + 1) (T ^ (n + 1 + 1)) = ((n : ℚ) + 1) * 1 := by
      rw [hc]; ring
    exact mul_left_cancel₀ hne this

/-- `F(m, n) = [X^n] (e^{mX} T^{n+1})`, the integral `∫_{ℙⁿ} ch(O(m)) td(O(1))^{n+1}`.-/
def hrrNum (m : ℚ) (n : ℕ) : ℚ := coeff n (rescale m (exp ℚ) * tdSer ^ (n + 1))

theorem hrrNum_zero_right (m : ℚ) : hrrNum m 0 = 1 := by
  simp [hrrNum, coeff_zero_eq_constantCoeff_apply, constantCoeff_tdSer]
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale]
  simp [coeff_exp]

theorem hrrNum_zero_left (n : ℕ) : hrrNum 0 n = 1 := by
  have h : rescale (0 : ℚ) (exp ℚ) = 1 := by
    rw [rescale_zero_apply]
    simp [← coeff_zero_eq_constantCoeff_apply, coeff_exp]
  simpa [hrrNum, h] using coeff_tdSer_pow_self n

/-- Pascal recursion: `e^{(m+1)X} - e^{mX} = e^{(m+1)X} · X · e` and `e · T = 1`.-/
theorem hrrNum_succ_succ (m : ℚ) (n : ℕ) :
    hrrNum (m + 1) (n + 1) = hrrNum m (n + 1) + hrrNum (m + 1) n := by
  have hexp : rescale (m + 1) (exp ℚ) - rescale m (exp ℚ) =
      rescale (m + 1) (exp ℚ) * (X * eSer) := by
    rw [X_mul_eSer, mul_sub, mul_one, exp_mul_exp_eq_exp_add]
    ring_nf
  have h1 := eSer_mul_tdSer
  have hdiff : rescale (m + 1) (exp ℚ) * tdSer ^ (n + 1 + 1) - rescale m (exp ℚ) * tdSer ^ (n + 1 + 1)
      = X * (rescale (m + 1) (exp ℚ) * tdSer ^ (n + 1)) := by
    have : (rescale (m + 1) (exp ℚ) - rescale m (exp ℚ)) * tdSer ^ (n + 1 + 1) =
        X * (rescale (m + 1) (exp ℚ) * tdSer ^ (n + 1)) := by
      rw [hexp]
      linear_combination (X * rescale (m + 1) (exp ℚ) * tdSer ^ (n + 1)) * h1
    linear_combination this
  have := congrArg (coeff (n + 1)) hdiff
  rw [map_sub, coeff_succ_X_mul] at this
  unfold hrrNum
  linarith

/-- `∫_{ℙⁿ} e^{mH} td(O(1))^{n+1} = binom(n+m, n)` for `m : ℕ`.-/
theorem hrrNum_nat (m n : ℕ) : hrrNum (m : ℚ) n = ((n + m).choose n : ℚ) := by
  induction m generalizing n with
  | zero => simp [hrrNum_zero_left]
  | succ m ih =>
    induction n with
    | zero => simp [hrrNum_zero_right]
    | succ n ihn =>
      push_cast at ihn ⊢
      rw [hrrNum_succ_succ, ih (n + 1), ihn]
      rw [show n + 1 + (m + 1) = (n + m + 1) + 1 by ring, Nat.choose_succ_succ,
        show n + (m + 1) = n + m + 1 by ring, show n + 1 + m = n + m + 1 by ring]
      push_cast
      ring

/-- `hrrNum m n` agrees with the generalised binomial `binom(m+n, n)`.-/
def HrrBinom (n : ℕ) (m : ℚ) : Prop := hrrNum m n = Ring.choose (m + n) n

theorem hrrBinom_up (n : ℕ) (m : ℚ) (h1 : HrrBinom (n + 1) m) (h2 : HrrBinom n (m + 1)) :
    HrrBinom (n + 1) (m + 1) := by
  unfold HrrBinom at *
  have hP := Ring.choose_succ_succ (m + n + 1) n
  have e1 : m + 1 + ((n + 1 : ℕ) : ℚ) = (m + n + 1) + 1 := by push_cast; ring
  have e2 : m + ((n + 1 : ℕ) : ℚ) = m + n + 1 := by push_cast; ring
  have e3 : m + 1 + (n : ℚ) = m + n + 1 := by ring
  rw [e2] at h1
  rw [e3] at h2
  rw [hrrNum_succ_succ, e1, hP, h1, h2]
  ring

theorem hrrBinom_down (n : ℕ) (m : ℚ) (h1 : HrrBinom (n + 1) (m + 1)) (h2 : HrrBinom n (m + 1)) :
    HrrBinom (n + 1) m := by
  unfold HrrBinom at *
  have hP := Ring.choose_succ_succ (m + n + 1) n
  have e1 : m + 1 + ((n + 1 : ℕ) : ℚ) = (m + n + 1) + 1 := by push_cast; ring
  have e2 : m + ((n + 1 : ℕ) : ℚ) = m + n + 1 := by push_cast; ring
  have e3 : m + 1 + (n : ℚ) = m + n + 1 := by ring
  rw [e1, hP] at h1
  rw [e3] at h2
  rw [e2]
  have := hrrNum_succ_succ m n
  rw [h1, h2] at this
  linarith

/-- Integer twists: `∫_{ℙⁿ} e^{mH} td(O(1))^{n+1} = binom(m+n, n)` (generalised binomial in `ℚ`),
valid for every `m : ℤ` (the Hilbert polynomial; `0` for `-n ≤ m < 0`).-/
theorem hrrNum_int (n : ℕ) (m : ℤ) : hrrNum (m : ℚ) n = Ring.choose ((m : ℚ) + n) n := by
  suffices H : ∀ n : ℕ, ∀ m : ℤ, HrrBinom n (m : ℚ) from H n m
  intro n
  induction n with
  | zero => intro m; simp [HrrBinom, hrrNum_zero_right]
  | succ n ih =>
    intro m
    induction m using Int.induction_on with
    | zero =>
      unfold HrrBinom
      have : (((0 : ℤ) : ℚ) + ((n + 1 : ℕ) : ℚ)) = ((n + 1 : ℕ) : ℚ) := by push_cast; ring
      rw [this, Ring.choose_natCast]
      simp [hrrNum_zero_left]
    | succ i hi =>
      have := hrrBinom_up n (i : ℚ) (by exact_mod_cast hi) (by exact_mod_cast ih ((i : ℤ) + 1))
      exact_mod_cast this
    | pred i hi =>
      have := hrrBinom_down n ((-(i : ℤ) - 1 : ℤ) : ℚ) (by push_cast at hi ⊢; ring_nf at hi ⊢; exact hi)
        (by push_cast; ring_nf; have := ih (-(i : ℤ)); push_cast at this; ring_nf at this; exact this)
      exact this

section Eval

variable {M : Type*} [AddCommGroup M] [Module ℚ M]

/-- Order-`n` truncation of a power series, evaluated at the operator `H`:
`Σ_{i ≤ n} f_i Hⁱ`.  (`ch_op`, `td_op` of a line bundle with `H = c₁(L) ∩ -`.)-/
def evTrunc (n : ℕ) (H : Module.End ℚ M) (f : ℚ⟦X⟧) : Module.End ℚ M :=
  Polynomial.aeval H (f.trunc (n + 1))

theorem aeval_apply_eq_of_dvd (n : ℕ) (H : Module.End ℚ M) (v : M) (hv : (H ^ (n + 1)) v = 0)
    {p q : Polynomial ℚ} (h : (Polynomial.X : Polynomial ℚ) ^ (n + 1) ∣ p - q) :
    Polynomial.aeval H p v = Polynomial.aeval H q v := by
  obtain ⟨r, hr⟩ := h
  have hp : p = q + r * (Polynomial.X : Polynomial ℚ) ^ (n + 1) := by
    linear_combination hr
  rw [hp, map_add, map_mul, map_pow, Polynomial.aeval_X, LinearMap.add_apply, Module.End.mul_apply,
    hv, map_zero, add_zero]

theorem evTrunc_mul_apply (n : ℕ) (H : Module.End ℚ M) (v : M) (hv : (H ^ (n + 1)) v = 0)
    (f g : ℚ⟦X⟧) :
    evTrunc n H (f * g) v = evTrunc n H f (evTrunc n H g v) := by
  have h1 : (f * g).trunc (n + 1) =
      ((f.trunc (n + 1) * g.trunc (n + 1) : Polynomial ℚ) : ℚ⟦X⟧).trunc (n + 1) := by
    rw [← trunc_trunc_mul_trunc]
    simp
  have hc : ∀ d < n + 1, coeff d (f * g) = (f.trunc (n + 1) * g.trunc (n + 1)).coeff d := by
    intro d hd
    have e : coeff d (f * g) = ((f * g).trunc (n + 1)).coeff d := by
      rw [coeff_trunc, ite_eq_left hd]
    rw [e, h1, coeff_trunc, ite_eq_left hd, Polynomial.coeff_coe]
  unfold evTrunc
  rw [h1, ← Module.End.mul_apply, ← map_mul (Polynomial.aeval H)]
  apply aeval_apply_eq_of_dvd n H v hv
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  simp [coeff_trunc, hd, hc d hd]

theorem evTrunc_one (n : ℕ) (H : Module.End ℚ M) : evTrunc n H 1 = 1 := by
  simp [evTrunc, trunc_one]

theorem evTrunc_pow_apply (n : ℕ) (H : Module.End ℚ M) (v : M) (hv : (H ^ (n + 1)) v = 0)
    (f : ℚ⟦X⟧) (k : ℕ) : ((evTrunc n H f) ^ k) v = evTrunc n H (f ^ k) v := by
  induction k with
  | zero => simp [evTrunc_one]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', evTrunc_mul_apply n H v hv]

theorem functional_evTrunc {N : Type*} [AddCommGroup N] [Module ℚ N] (n : ℕ)
    (H : Module.End ℚ M) (v : M) (Ψ : M →ₗ[ℚ] N) (w : N)
    (hΨ : ∀ p ≤ n, Ψ ((H ^ p) v) = if p = n then w else 0) (f : ℚ⟦X⟧) :
    Ψ (evTrunc n H f v) = coeff n f • w := by
  unfold evTrunc
  rw [Polynomial.aeval_eq_sum_range' (natDegree_trunc_lt f n), LinearMap.sum_apply, map_sum]
  have : ∀ i ∈ Finset.range (n + 1),
      Ψ (((f.trunc (n + 1)).coeff i • H ^ i) v) = if i = n then coeff n f • w else 0 := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [LinearMap.smul_apply, map_smul, hΨ i hi', coeff_trunc, ite_eq_left (Nat.lt_succ_of_le hi')]
    by_cases h : i = n
    · subst h; simp
    · simp [h]
  rw [Finset.sum_congr rfl this]
  simp

/-- **Operator form of the case (i) computation (vector valued).**  `Ψ = π_*`, `H = c₁(O(1)) ∩ -`,
`v = π^*α`: if `H^{n+1} v = 0` and `Ψ(Hᵖ v) = [p = n] w` for `p ≤ n` then
`Ψ(ch_n(O(m)) · td_n(O(1))^{n+1} v) = binom(m+n, n) • w` for every `m : ℤ`.-/
theorem chiOp_int {N : Type*} [AddCommGroup N] [Module ℚ N] (n : ℕ) (H : Module.End ℚ M) (v : M)
    (hv : (H ^ (n + 1)) v = 0) (Ψ : M →ₗ[ℚ] N) (w : N)
    (hΨ : ∀ p ≤ n, Ψ ((H ^ p) v) = if p = n then w else 0) (m : ℤ) :
    Ψ (evTrunc n H (rescale (m : ℚ) (exp ℚ)) (((evTrunc n H tdSer) ^ (n + 1)) v)) =
      Ring.choose ((m : ℚ) + n) n • w := by
  rw [evTrunc_pow_apply n H v hv, ← evTrunc_mul_apply n H v hv, functional_evTrunc n H v Ψ w hΨ]
  rw [← hrrNum_int n m]
  rfl

theorem chiOp_nat {N : Type*} [AddCommGroup N] [Module ℚ N] (n : ℕ) (H : Module.End ℚ M) (v : M)
    (hv : (H ^ (n + 1)) v = 0) (Ψ : M →ₗ[ℚ] N) (w : N)
    (hΨ : ∀ p ≤ n, Ψ ((H ^ p) v) = if p = n then w else 0) (m : ℕ) :
    Ψ (evTrunc n H (rescale (m : ℚ) (exp ℚ)) (((evTrunc n H tdSer) ^ (n + 1)) v)) =
      ((n + m).choose n : ℚ) • w := by
  rw [evTrunc_pow_apply n H v hv, ← evTrunc_mul_apply n H v hv, functional_evTrunc n H v Ψ w hΨ]
  rw [← hrrNum_nat m n]
  rfl

end Eval

/-! ### Numeric sanity lemmas (test cases any correct HRR blueprint must satisfy) -/

theorem coeff_tdSer_one : coeff 1 tdSer = 1 / 2 := by
  have h := congrArg (coeff 1) eSer_mul_tdSer
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ] at h
  simp [eSer, constantCoeff_tdSer, coeff_zero_eq_constantCoeff_apply] at h
  have h0 : coeff 0 tdSer = 1 := by rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_tdSer]
  have h1 : coeff 0 eSer = 1 := by rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_eSer]
  linarith

theorem coeff_tdSer_two : coeff 2 tdSer = 1 / 12 := by
  have h := congrArg (coeff 2) eSer_mul_tdSer
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ] at h
  have h0 : coeff 0 tdSer = 1 := by rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_tdSer]
  have h1 := coeff_tdSer_one
  simp [eSer, h0, h1] at h
  norm_num [Nat.factorial] at h
  linarith

/-- `n = 1`: `∫_{ℙ¹} ch(O(m)) td(T) = m + 1`  (`χ(ℙ¹, O(m)) = m + 1`).-/
theorem hrrNum_one (m : ℤ) : hrrNum (m : ℚ) 1 = (m : ℚ) + 1 := by
  rw [hrrNum_int, Ring.choose_one_right]; simp

theorem ringChoose_two (x : ℚ) : Ring.choose x 2 = x * (x - 1) / 2 := by
  rw [Ring.choose_eq_smul]
  simp [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub]
  ring

/-- `n = 2`: `∫_{ℙ²} ch(O(m)) td(T) = (m+1)(m+2)/2`.-/
theorem hrrNum_two (m : ℤ) : hrrNum (m : ℚ) 2 = ((m : ℚ) + 1) * ((m : ℚ) + 2) / 2 := by
  rw [hrrNum_int, ringChoose_two]
  push_cast
  ring

/-- Direct check for `n = 2`, independent of the general Pascal argument: with `t₁ = 1/2`,
`t₂ = 1/12` the `H²`-coefficient of `e^{mH} (1 + H/2 + H²/12)³` is `m²/2 + 3m/2 + 1`.-/
theorem hrrNum_two_direct (m : ℚ) :
    m ^ 2 / 2 + m * (3 * (1 / 2)) + (3 * (1 / 12) + 3 * (1 / 2) ^ 2) = (m + 1) * (m + 2) / 2 := by
  ring

end AlgebraicGeometry.Chow.M7.CASE1
