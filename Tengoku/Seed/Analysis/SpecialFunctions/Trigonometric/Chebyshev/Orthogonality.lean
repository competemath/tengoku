/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.RingTheory.Polynomial.Chebyshev
public import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Tengoku.Seed.MeasureTheory.Integral.IntegrableOn
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Tengoku.Seed.Topology.Algebra.Polynomial

/-!
# Chebyshev polynomials over the reals: orthogonality

Chebyshev T polynomials are orthogonal with respect to `√(1 - x ^ 2)⁻¹`.

## Main statements

* `integrable_measureT`: continuous functions are integrable with respect to Lebesgue measure
  scaled by `√(1 - x ^ 2)⁻¹` and restricted to `(-1, 1]`.
* `integral_eval_T_real_mul_evalT_real_measureT_of_ne`:
  if `n ≠ m` then the integral of `T_n * T_m` equals `0`.
* `integral_eval_T_real_mul_self_measureT_zero`:
  if `n = m = 0` then the integral equals `π`.
* `integral_eval_T_real_mul_self_measureT_of_ne_zero`:
  if `n = m ≠ 0` then the integral equals `π / 2`.

## TODO

* Prove that Chebyshev U polynomials are orthogonal with respect to `√(1 - x ^ 2)`
* Bundle Chebyshev T polynomials into a HilbertBasis for MeasureTheory.Lp ℝ 2 measureT

-/
public section

namespace Polynomial.Chebyshev

open Real intervalIntegral MeasureTheory

open scoped NNReal

/-- Lebesgue measure scaled by √(1 - x ^ 2)⁻¹. -/
noncomputable def measureT : Measure ℝ :=
  (volume.withDensity
    fun x ↦ ENNReal.ofNNReal (.mk (√(1 - x ^ 2)⁻¹) (by positivity))).restrict (Set.Ioc (-1) 1)

/--
@isnad1 id=eq.0h1v.s6.47c79b94b349 from=seed src=0 shape=a53150ee vocab=6408f5a9
-/
theorem integral_measureT (f : ℝ → ℝ) :
    ∫ x, f x ∂measureT = ∫ x in -1..1, f x * √(1 - x ^ 2)⁻¹ := by
  rw [integral_of_le (by norm_num), measureT,
    restrict_withDensity (by measurability),
    integral_withDensity_eq_integral_smul (by fun_prop)]
  congr! 2 with x hx
  simp [NNReal.smul_def, mul_comm]

/--
@isnad1 id=interval.0h0v.s6.f24a7ebfdac0 from=seed src=0 shape=96568f9c vocab=3b554eac
-/
theorem intervalIntegrable_sqrt_one_sub_sq_inv :
    IntervalIntegrable (fun x ↦ √(1 - x ^ 2)⁻¹) volume (-1) 1 := by
  rw [intervalIntegrable_iff]
  refine integrableOn_deriv_of_nonneg continuous_arccos.neg.continuousOn (fun x hx ↦ ?_) (by simp)
  simpa using! (hasDerivAt_arccos (by aesop) (by aesop)).neg

/--
@isnad1 id=integrab.1h1v.s5.f3d3905da81a from=seed src=0 shape=e1697d80 vocab=0f29a77f
-/
theorem integrable_measureT {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (-1) 1)) :
    Integrable f measureT := by
  replace hf : ContinuousOn f (Set.uIcc (-1) 1) := by rwa [Set.uIcc_of_lt (by norm_num)]
  have := intervalIntegrable_sqrt_one_sub_sq_inv.continuousOn_mul hf
  rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num)] at this
  rw [measureT, restrict_withDensity (by measurability),
    integrable_withDensity_iff (by fun_prop) (by simp)]
  unfold IntegrableOn at this
  convert! this

open Set in
/--
@isnad1 id=eq.0h1v.s5.51c79ecdde77 from=seed src=0 shape=d745263e vocab=77abe1da
-/
theorem integral_measureT_eq_integral_cos {f : ℝ → ℝ} :
    ∫ x, f x ∂measureT = ∫ θ in 0..π, f (cos θ) := calc
  ∫ x, f x ∂measureT = ∫ x in -1..1, f x * √(1 - x ^ 2)⁻¹ := integral_measureT f
  _ = ∫ x in 1..-1, f x * -(√(1 - x ^ 2)⁻¹) := by
    rw [integral_symm, ← intervalIntegral.integral_neg]
    simp
  _ = ∫ θ in (arccos 1)..(arccos (-1)), f (cos θ) := by
    rw [← integral_comp_mul_deriv_of_deriv_nonpos (f' := fun x => -(1 / √(1 - x ^ 2)))]
    · simp_rw [Function.comp_apply]
      exact integral_congr <| fun x hx => by simp [cos_arccos (x := x) (by aesop) (by aesop)]
    · fun_prop
    · exact fun x hx ↦ (hasDerivAt_arccos (by aesop) (by aesop))
    · simp
  _ = ∫ θ in 0..π, f (cos θ) := by simp

/--
@isnad1 id=eq.0h1v.s5.51c79ecdde77 from=seed src=0 shape=d745263e vocab=77abe1da
-/
@[deprecated (since := "2026-03-19")]
alias integral_measureT_eq_integral_cos_of_continuous := integral_measureT_eq_integral_cos

/--
@isnad1 id=eq.0h0v.s5.44ae169ff659 from=seed src=0 shape=9fa005cb vocab=ff5256da
-/
theorem integral_eval_T_real_measureT_zero :
    ∫ x, (T ℝ 0).eval x ∂measureT = π := by
  rw [integral_measureT_eq_integral_cos]; simp

/--
@isnad1 id=eq.1h1v.s5.11ecb5829208 from=seed src=0 shape=5bd112e5 vocab=3f8f1ff1
-/
theorem integral_eval_T_real_measureT_of_ne_zero {n : ℤ} (hn : n ≠ 0) :
    ∫ x, (T ℝ n).eval x ∂measureT = 0 := by
  have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  suffices ∫ θ in 0..n * π, cos θ = 0 by
    rw [integral_measureT_eq_integral_cos]
    simp_rw [T_real_cos]
    rwa [integral_comp_mul_left _ (Int.cast_ne_zero.mpr hn), smul_eq_zero_iff_right (by aesop),
      mul_zero]
  trans ∫ θ in 0..n * π, (deriv sin) θ
  · refine integral_congr <| fun x hx => (congrFun deriv_sin x).symm
  by_cases! 0 ≤ n
  case pos => rw [integral_deriv_of_contDiffOn_Icc contDiff_sin.contDiffOn (by positivity)]; simp
  case neg hn =>
    rw [integral_symm, integral_deriv_of_contDiffOn_Icc contDiff_sin.contDiffOn]
    · simp
    exact mul_nonpos_of_nonpos_of_nonneg (Int.cast_nonpos.mpr <| le_of_lt hn) pi_nonneg

/--
@isnad1 id=eq.0h2v.s7.b8091cf42b84 from=seed src=0 shape=c4467a13 vocab=325a1e5b
-/
theorem integral_eval_T_real_mul_eval_T_real_measureT (n m : ℤ) :
    ∫ x, (T ℝ n).eval x * (T ℝ m).eval x ∂measureT =
    ((∫ x, (T ℝ (n + m)).eval x ∂measureT) +
     (∫ x, (T ℝ (n - m)).eval x ∂measureT)) / 2 := by
  suffices ∫ x, (2 * T ℝ n * T ℝ m).eval x ∂measureT =
      (∫ x, (T ℝ (n + m)).eval x ∂measureT) +
      (∫ x, (T ℝ (n - m)).eval x ∂measureT) by
    simp_rw [eval_mul, eval_ofNat, mul_assoc] at this
    rw [MeasureTheory.integral_const_mul] at this
    grind
  simp_rw [T_mul_T, eval_add]
  rw [MeasureTheory.integral_add
    (integrable_measureT (by fun_prop)) (integrable_measureT (by fun_prop))]

/--
@isnad1 id=eq.1h2v.s6.d4d9ce0e490d from=seed src=0 shape=8601a984 vocab=13831d68
-/
theorem integral_eval_T_real_mul_eval_T_real_measureT_of_ne {n m : ℕ} (h : n ≠ m) :
    ∫ x, (T ℝ n).eval x * (T ℝ m).eval x ∂measureT = 0 := by
  rw [integral_eval_T_real_mul_eval_T_real_measureT,
    integral_eval_T_real_measureT_of_ne_zero (by grind),
    integral_eval_T_real_measureT_of_ne_zero (by grind)]
  simp

/--
@isnad1 id=eq.0h0v.s5.a98816982159 from=seed src=0 shape=b467385e vocab=5eda3937
-/
theorem integral_eval_T_real_mul_self_measureT_zero :
    ∫ x, (T ℝ 0).eval x * (T ℝ 0).eval x ∂measureT = π := by
  simp_rw [← eval_mul, show (T ℝ 0) * (T ℝ 0) = T ℝ 0 by simp]
  exact integral_eval_T_real_measureT_zero

/--
@isnad1 id=eq.1h1v.s6.c36991262ae9 from=seed src=0 shape=fddbc2e8 vocab=286b9d3a
-/
theorem integral_T_real_mul_self_measureT_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ∫ x, (T ℝ n).eval x * (T ℝ n).eval x ∂measureT = π / 2 := by
  rw [integral_eval_T_real_mul_eval_T_real_measureT,
    integral_eval_T_real_measureT_of_ne_zero (by grind), sub_self,
    integral_eval_T_real_measureT_zero, zero_add]

end Polynomial.Chebyshev
