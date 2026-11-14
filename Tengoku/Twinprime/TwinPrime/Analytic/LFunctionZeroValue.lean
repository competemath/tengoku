import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionGrowth
import Tengoku.Seed.Analysis.Calculus.MeanValue
import Tengoku.Seed.Analysis.Complex.RealDeriv
import Tengoku.Seed.NumberTheory.LSeries.Nonvanishing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A real zero and the value of an L-function at one

The real-segment mean value bound keeps the actual function and its actual
derivative. Its primitive specialization gives a finite quantitative bridge;
no uniform Siegel lower bound is assumed or proved here.
-/

noncomputable section

open Set Metric

namespace TwinPrime.Analytic

/-- Restricting a complex differentiable function to a real segment preserves
the complex derivative as a real derivative.
@isnad1 id=le.3h4v.s7.8237c141c424 from=translated src=- shape=2ba25119 vocab=d6ac6959
-/
theorem norm_sub_le_real_segment_deriv_bound {f : ℂ → ℂ} {a b C : ℝ}
    (hab : a ≤ b) (hf : ∀ u ∈ Icc a b, DifferentiableAt ℂ f (u : ℂ))
    (hbound : ∀ u ∈ Icc a b, ‖deriv f (u : ℂ)‖ ≤ C) :
    ‖f (b : ℂ) - f (a : ℂ)‖ ≤ C * (b - a) := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => ((hf u hu).hasDerivAt.comp_ofReal).hasDerivWithinAt)
    hbound (convex_Icc a b) (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using h

/-- A supplied derivative bound gives the exact zero-to-value estimate.
@isnad1 id=le.4h4v.s7.507187c31171 from=translated src=- shape=17162092 vocab=4399f37c
-/
theorem norm_LFunction_one_le_gap_of_deriv_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (β C : ℝ) (hβ1 : β ≤ 1)
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (hbound : ∀ u ∈ Icc β 1, ‖deriv (DirichletCharacter.LFunction χ) (u : ℂ)‖ ≤ C) :
    ‖DirichletCharacter.LFunction χ 1‖ ≤ C * (1 - β) := by
  have h := norm_sub_le_real_segment_deriv_bound hβ1
    (fun u _ => DirichletCharacter.differentiable_LFunction hχ (u : ℂ)) hbound
  simpa only [Complex.ofReal_one, hzero, sub_zero] using h

/-- The existing growth estimate gives a derivative bound on [3/4,1].
The fixed square-root conductor loss is retained explicitly.
@isnad1 id=le.4h3v.s7.9bc016b5a3e2 from=translated src=- shape=96c7b477 vocab=e52a0c60
-/
theorem norm_deriv_LFunction_real_le_growth_budget {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (u : ℝ) (hu : 3 / 4 ≤ u) (hu1 : u ≤ 1) :
    ‖deriv (DirichletCharacter.LFunction χ) (u : ℂ)‖ ≤
      4 + 14 * Real.sqrt q * (1 + Real.log q) := by
  have h := norm_deriv_LFunction_le hq χ hχ (u : ℂ) (1 / 4)
    (by norm_num) (by simp only [Complex.ofReal_re]; linarith)
  have hu0 : 0 ≤ u := by linarith
  have hd : (1 / 2 : ℝ) ≤ u - 1 / 4 := by linarith
  have hH : u + 1 / 4 ≤ (5 / 4 : ℝ) := by linarith
  have hlog := Real.log_natCast_nonneg q
  have hsqrt := Real.sqrt_nonneg (q : ℝ)
  simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hu0] at h
  have hr : (u + 1 / 4) / (u - 1 / 4) ≤ (5 / 2 : ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < u - 1 / 4)).mpr
    linarith
  unfold primitiveLFunctionGrowthBudget at h
  nlinarith [mul_nonneg hsqrt (by linarith : 0 ≤ 1 + Real.log (q : ℝ)),
    mul_le_mul_of_nonneg_left hr (mul_nonneg hsqrt
      (by linarith : 0 ≤ 1 + Real.log (q : ℝ)))]

/--
@isnad1 id=le.5h3v.s7.1148bf664404 from=translated src=- shape=31375c1f vocab=2477bc8f
-/
theorem norm_LFunction_one_le_gap_budget {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (hβ1 : β ≤ 1)
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    ‖DirichletCharacter.LFunction χ 1‖ ≤
      (4 + 14 * Real.sqrt q * (1 + Real.log q)) * (1 - β) := by
  apply norm_LFunction_one_le_gap_of_deriv_bound χ (primitive_character_ne_one hq χ hχ)
    β _ hβ1 hzero
  intro u hu
  exact norm_deriv_LFunction_real_le_growth_budget hq χ hχ u (hβ.trans hu.1) hu.2

end TwinPrime.Analytic
