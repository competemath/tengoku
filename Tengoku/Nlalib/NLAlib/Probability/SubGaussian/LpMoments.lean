import Tengoku.Nlalib.NLAlib.Probability.SubGaussian.Moments
import Tengoku.Seed.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integer Lp bounds for sub-Gaussian fluctuations

The actual even scalar moments give an explicit square-root growth bound,
including a zero variance proxy. Centering at the expectation then compares
the Lp norm of an observable with its realized value outside a Gaussian tail.
These estimates supply the scalar moment step in arXiv:2201.05142v3,
Lemma 7.3.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace NLAlib

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A sub-Gaussian fluctuation has the scale-normalized strict Gaussian
tail, including a zero variance proxy.-/
theorem measureReal_sqrt_mul_lt_abs_le_of_hasSubgaussianMGF
    {X : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | Real.sqrt c * t < |X ω|} ≤ 2 * Real.exp (-t ^ 2 / 2) := by
  rcases eq_or_ne c 0 with rfl | hc
  · have hz := h.ae_eq_zero_of_hasSubgaussianMGF_zero
    have he : {ω | Real.sqrt (0 : ℝ≥0) * t < |X ω|} =ᵐ[μ] (∅ : Set Ω) := by
      filter_upwards [hz] with ω hω
      apply propext
      change (Real.sqrt (0 : ℝ≥0) * t < |X ω|) ↔ False
      simp only [Pi.zero_apply] at hω
      simp [hω]
    rw [measureReal_congr he, measureReal_empty]
    positivity
  · have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    have hb := measureReal_lt_abs_le_of_hasSubgaussianMGF h
      (mul_nonneg (Real.sqrt_nonneg (c : ℝ)) ht)
    have he : -(Real.sqrt c * t) ^ 2 / (2 * c) = -t ^ 2 / 2 := by
      have hsqrt : Real.sqrt (c : ℝ) ^ 2 = (c : ℝ) := Real.sq_sqrt c.2
      have hmul := congrArg (fun r : ℝ => r * t ^ 2) hsqrt
      rw [mul_pow]
      field_simp [hc']
      nlinarith
    rwa [he] at hb

end NLAlib
