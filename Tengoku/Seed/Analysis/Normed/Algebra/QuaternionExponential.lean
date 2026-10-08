/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Quaternion
public import Tengoku.Seed.Analysis.Normed.Algebra.Exponential
public import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Lemmas about `NormedSpace.exp` on `Quaternion`s

This file contains results about `NormedSpace.exp` on `Quaternion ℝ`.

## Main results

* `Quaternion.exp_eq`: the general expansion of the quaternion exponential in terms of `Real.cos`
  and `Real.sin`.
* `Quaternion.exp_of_re_eq_zero`: the special case when the quaternion has a zero real part.
* `Quaternion.norm_exp`: the norm of the quaternion exponential is the norm of the exponential of
  the real part.

-/

public section

open scoped Quaternion Nat

open NormedSpace

namespace Quaternion

/--
@isnad1 id=eq.0h1v.s8.7af2cf928295 from=seed src=0 shape=a8e5eaaa vocab=0cba2601
-/
@[simp, norm_cast]
theorem exp_coe (r : ℝ) : exp (r : ℍ[ℝ]) = ↑(exp r) :=
  (map_exp (algebraMap ℝ ℍ[ℝ]) (continuous_algebraMap _ _) _).symm

/-- The even terms of `expSeries` are real, and correspond to the series for $\cos ‖q‖$.
@isnad1 id=eq.1h2v.s9.fd7bf15cc840 from=seed src=0 shape=0f2b5dcc vocab=04683a56
-/
theorem expSeries_even_of_imaginary {q : Quaternion ℝ} (hq : q.re = 0) (n : ℕ) :
    expSeries ℝ (Quaternion ℝ) (2 * n) (fun _ => q) =
      ↑((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n) / (2 * n)!) := by
  rw [expSeries_apply_eq]
  have hq2 : q ^ 2 = -normSq q := sq_eq_neg_normSq.mpr hq
  let k : ℝ := ↑(2 * n)!
  calc
    k⁻¹ • q ^ (2 * n) = k⁻¹ • (-normSq q) ^ n := by rw [pow_mul, hq2]
    _ = k⁻¹ • ↑((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n)) := ?_
    _ = ↑((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n) / k) := ?_
  · congr 1
    rw [neg_pow, normSq_eq_norm_mul_self, pow_mul, sq]
    push_cast
    rfl
  · rw [← coe_mul_eq_smul, div_eq_mul_inv]
    norm_cast
    ring_nf

/-- The odd terms of `expSeries` are real, and correspond to the series for
$\frac{q}{‖q‖} \sin ‖q‖$.
@isnad1 id=eq.1h2v.s10.823c1ed46ac3 from=seed src=0 shape=5e0715e8 vocab=afac3636
-/
theorem expSeries_odd_of_imaginary {q : Quaternion ℝ} (hq : q.re = 0) (n : ℕ) :
    expSeries ℝ (Quaternion ℝ) (2 * n + 1) (fun _ => q) =
      (((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n + 1) / (2 * n + 1)!) / ‖q‖) • q := by
  rw [expSeries_apply_eq]
  obtain rfl | hq0 := eq_or_ne q 0
  · simp
  have hq2 : q ^ 2 = -normSq q := sq_eq_neg_normSq.mpr hq
  have hqn := norm_ne_zero_iff.mpr hq0
  let k : ℝ := ↑(2 * n + 1)!
  calc
    k⁻¹ • q ^ (2 * n + 1) = k⁻¹ • ((-normSq q) ^ n * q) := by rw [pow_succ, pow_mul, hq2]
    _ = k⁻¹ • ((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n)) • q := ?_
    _ = ((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n + 1) / k / ‖q‖) • q := ?_
  · congr 1
    rw [neg_pow, normSq_eq_norm_mul_self, pow_mul, sq, ← coe_mul_eq_smul]
    norm_cast
  · rw [smul_smul]
    congr 1
    simp_rw [pow_succ, mul_div_assoc, div_div_cancel_left' hqn]
    ring

/-- Auxiliary result; if the power series corresponding to `Real.cos` and `Real.sin` evaluated
at `‖q‖` tend to `c` and `s`, then the exponential series tends to `c + (s / ‖q‖)`.
@isnad1 id=hassum.3h3v.s9.a27a9604ed0f from=seed src=0 shape=67854048 vocab=ec3c6150
-/
theorem hasSum_expSeries_of_imaginary {q : Quaternion ℝ} (hq : q.re = 0) {c s : ℝ}
    (hc : HasSum (fun n => (-1 : ℝ) ^ n * ‖q‖ ^ (2 * n) / (2 * n)!) c)
    (hs : HasSum (fun n => (-1 : ℝ) ^ n * ‖q‖ ^ (2 * n + 1) / (2 * n + 1)!) s) :
    HasSum (fun n => expSeries ℝ (Quaternion ℝ) n fun _ => q) (↑c + (s / ‖q‖) • q) := by
  replace hc := hasSum_coe.mpr hc
  replace hs := (hs.div_const ‖q‖).smul_const q
  refine HasSum.even_add_odd ?_ ?_
  · convert! hc using 1
    ext n : 1
    rw [expSeries_even_of_imaginary hq]
  · convert! hs using 1
    ext n : 1
    rw [expSeries_odd_of_imaginary hq]

set_option backward.isDefEq.respectTransparency false in -- This is needed or we get errors in later declarations.
/-- The closed form for the quaternion exponential on imaginary quaternions.
@isnad1 id=eq.1h1v.s7.4ac66cbc7026 from=seed src=0 shape=99551500 vocab=180e0fc1
-/
theorem exp_of_re_eq_zero (q : Quaternion ℝ) (hq : q.re = 0) :
    exp q = ↑(Real.cos ‖q‖) + (Real.sin ‖q‖ / ‖q‖) • q := by
  rw [exp_eq_tsum ℝ]
  refine HasSum.tsum_eq ?_
  simp_rw [← expSeries_apply_eq]
  exact hasSum_expSeries_of_imaginary hq (Real.hasSum_cos _) (Real.hasSum_sin _)

set_option backward.isDefEq.respectTransparency false in -- This is needed or we get errors in later declarations.
/-- The closed form for the quaternion exponential on arbitrary quaternions.
@isnad1 id=eq.0h1v.s9.b2387dc4bdbd from=seed src=0 shape=391fe9cc vocab=f42e1524
-/
theorem exp_eq (q : Quaternion ℝ) :
    exp q = exp q.re • (↑(Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im) := by
  let +nondep : NormedAlgebra ℚ ℍ := .restrictScalars ℚ ℝ ℍ
  rw [← exp_of_re_eq_zero q.im q.re_im, ← coe_mul_eq_smul, ← exp_coe, ← exp_add_of_commute,
    re_add_im]
  exact Algebra.commutes q.re (_ : ℍ[ℝ])

/--
@isnad1 id=eq.0h1v.s7.fc41aa61f2df from=seed src=0 shape=baf1d5b2 vocab=4bcb1d70
-/
theorem re_exp (q : ℍ[ℝ]) : (exp q).re = exp q.re * Real.cos ‖q - q.re‖ := by simp [exp_eq]

/--
@isnad1 id=eq.0h1v.s8.d63d2e00812b from=seed src=0 shape=7b47dc5d vocab=8eecbd66
-/
theorem im_exp (q : ℍ[ℝ]) : (exp q).im = (exp q.re * (Real.sin ‖q.im‖ / ‖q.im‖)) • q.im := by
  simp [exp_eq, smul_smul]

/--
@isnad1 id=eq.0h1v.s9.6e05e974e7c5 from=seed src=0 shape=3e786c16 vocab=5cacbff6
-/
theorem normSq_exp (q : ℍ[ℝ]) : normSq (exp q) = exp q.re ^ 2 :=
  calc
    normSq (exp q) =
        normSq (exp q.re • (↑(Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im)) := by
      rw [exp_eq]
    _ = exp q.re ^ 2 * normSq (↑(Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im) := by
      rw [normSq_smul]
    _ = exp q.re ^ 2 * (Real.cos ‖q.im‖ ^ 2 + Real.sin ‖q.im‖ ^ 2) := by
      congr 1
      obtain hv | hv := eq_or_ne ‖q.im‖ 0
      · simp [hv]
      rw [normSq_add, normSq_smul, star_smul, coe_mul_eq_smul, re_smul, re_smul, re_star, re_im,
        smul_zero, smul_zero, mul_zero, add_zero, div_pow, normSq_coe,
        normSq_eq_norm_mul_self, ← sq, div_mul_cancel₀ _ (pow_ne_zero _ hv)]
    _ = exp q.re ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]

/-- Note that this implies that exponentials of pure imaginary quaternions are unit quaternions
since in that case the RHS is `1` via `NormedSpace.exp_zero` and `norm_one`.
@isnad1 id=eq.0h1v.s6.bfe103cfff1c from=seed src=0 shape=3a8f291b vocab=1c89568a
-/
@[simp]
theorem norm_exp (q : ℍ[ℝ]) : ‖exp q‖ = ‖exp q.re‖ := by
  rw [norm_eq_sqrt_real_inner (exp q), inner_self, normSq_exp, Real.sqrt_sq_eq_abs,
    Real.norm_eq_abs]

end Quaternion
