/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Seed.Analysis.InnerProductSpace.PiL2
import Tengoku.Seed.MeasureTheory.Function.L2Space
import Tengoku.Seed.MeasureTheory.Integral.MeanInequalities
import Tengoku.Seed.MeasureTheory.SpecificCodomains.WithLp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Expected empirical quadratic envelopes

This file isolates the scalar `L²` step used after conditioning a
Rademacher process on the observations.  It is independent of any chaining
or symmetrization argument.
-/

open Real MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}

/-- On a probability space, the first moment of a nonnegative `L²` random
variable is bounded by its quadratic mean.
@isnad1 id=le.2h4v.s7.24c58dc44caf from=translated src=- shape=3872af63 vocab=0fbc4b4f
-/
theorem integral_nonnegative_le_sqrt_integral_sq
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (f : Omega → ℝ) (hf : MemLp f 2 mu)
    (hf_nonneg : 0 ≤ᵐ[mu] f) :
    ∫ omega, f omega ∂mu ≤ Real.sqrt (∫ omega, (f omega) ^ 2 ∂mu) := by
  have hone : MemLp (fun _ : Omega ↦ (1 : ℝ)) 2 mu := by
    exact memLp_const 1
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) mu := by
    norm_num
    exact hf
  have hone' : MemLp (fun _ : Omega ↦ (1 : ℝ))
      (ENNReal.ofReal (2 : ℝ)) mu := by
    norm_num
    exact hone
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := mu) (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two
    hf_nonneg (ae_of_all mu fun _ ↦ zero_le_one) hf' hone'
  simpa only [mul_one, one_pow, integral_const, probReal_univ,
    one_smul, one_rpow, Real.sqrt_eq_rpow, one_div,
    Real.rpow_two] using hholder

/-- The expected Euclidean norm of a finite vector is at most the square
root of the sum of the coordinate second moments.
@isnad1 id=le.1h5v.s7.81e60535a9f9 from=translated src=- shape=903ec0f3 vocab=d23dc30b
-/
theorem integral_sqrt_fin_sum_sq_le
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {n : Nat} (A : Fin n → Omega → ℝ)
    (hA : ∀ i, MemLp (A i) 2 mu) :
    ∫ omega, Real.sqrt (∑ i : Fin n, (A i omega) ^ 2) ∂mu ≤
      Real.sqrt (∑ i : Fin n, ∫ omega, (A i omega) ^ 2 ∂mu) := by
  let F : Omega → EuclideanSpace ℝ (Fin n) :=
    fun omega ↦ WithLp.toLp 2 (fun i ↦ A i omega)
  have hF : MemLp F 2 mu := by
    apply MemLp.of_eval_piLp
    intro i
    simpa only [F, Function.comp_apply, PiLp.toLp_apply] using hA i
  have hnorm := integral_nonnegative_le_sqrt_integral_sq
    (mu := mu) (fun omega ↦ ‖F omega‖) hF.norm
    (ae_of_all mu fun _ ↦ norm_nonneg _)
  have hpoint : ∀ omega,
      ‖F omega‖ = Real.sqrt (∑ i : Fin n, (A i omega) ^ 2) := by
    intro omega
    rw [EuclideanSpace.norm_eq]
    simp only [F, Real.norm_eq_abs, sq_abs]
  have hsq : (∫ omega, ‖F omega‖ ^ 2 ∂mu) =
      ∑ i : Fin n, ∫ omega, (A i omega) ^ 2 ∂mu := by
    simp_rw [EuclideanSpace.real_norm_sq_eq]
    rw [integral_finsetSum]
    intro i hi
    exact (hA i).integrable_sq
  rw [hsq] at hnorm
  simpa only [hpoint] using hnorm

/-- If all coordinate second moments are bounded by `K₂²`, the expected
empirical quadratic envelope is bounded by `√n K₂`.
@isnad1 id=le.3h6v.s7.78172f1daa6f from=translated src=- shape=c58b738f vocab=8624ce4e
-/
theorem integral_sqrt_fin_sum_sq_le_sqrt_nat_mul
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {n : Nat} (A : Fin n → Omega → ℝ) (K₂ : ℝ)
    (hK₂ : 0 ≤ K₂)
    (hA : ∀ i, MemLp (A i) 2 mu)
    (hsecond : ∀ i, ∫ omega, (A i omega) ^ 2 ∂mu ≤ K₂ ^ 2) :
    ∫ omega, Real.sqrt (∑ i : Fin n, (A i omega) ^ 2) ∂mu ≤
      Real.sqrt n * K₂ := by
  calc
    ∫ omega, Real.sqrt (∑ i : Fin n, (A i omega) ^ 2) ∂mu ≤
        Real.sqrt (∑ i : Fin n, ∫ omega, (A i omega) ^ 2 ∂mu) :=
      integral_sqrt_fin_sum_sq_le A hA
    _ ≤ Real.sqrt (∑ _i : Fin n, K₂ ^ 2) := by
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum fun i _hi ↦ hsecond i
    _ = Real.sqrt n * K₂ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_fin, Real.sqrt_mul (Nat.cast_nonneg n),
        Real.sqrt_sq hK₂]

/-- Normalized version of
`integral_sqrt_fin_sum_sq_le_sqrt_nat_mul`: the empirical quadratic scale
has expectation at most `K₂ / √n`.
@isnad1 id=le.4h6v.s7.9f8282e055f8 from=translated src=- shape=4215827f vocab=55608f51
-/
theorem integral_normalized_sqrt_fin_sum_sq_le
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {n : Nat} (hn : 0 < n) (A : Fin n → Omega → ℝ) (K₂ : ℝ)
    (hK₂ : 0 ≤ K₂)
    (hA : ∀ i, MemLp (A i) 2 mu)
    (hsecond : ∀ i, ∫ omega, (A i omega) ^ 2 ∂mu ≤ K₂ ^ 2) :
    ∫ omega, Real.sqrt (∑ i : Fin n, (A i omega) ^ 2) / (n : ℝ) ∂mu ≤
      K₂ / Real.sqrt n := by
  rw [integral_div]
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  calc
    (∫ omega, Real.sqrt (∑ i : Fin n, (A i omega) ^ 2) ∂mu) / (n : ℝ) ≤
        (Real.sqrt n * K₂) / (n : ℝ) :=
      div_le_div_of_nonneg_right
        (integral_sqrt_fin_sum_sq_le_sqrt_nat_mul A K₂ hK₂ hA hsecond)
        hnreal.le
    _ = K₂ / Real.sqrt n := by
      have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnreal
      apply (div_eq_div_iff hnreal.ne' hsqrt.ne').2
      nlinarith [Real.sq_sqrt hnreal.le]

end ProbabilityTheory
