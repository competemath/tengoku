module

public import Tengoku.AtPalomar.Paper.ParisiCDFGrid

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! # Stability of the actual Parisi correction in CDF distance -/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Paper

/--
@isnad1 id=le.0h2v.s6.295ce500af75 from=translated src=- shape=b3123e7f vocab=215783be
-/
theorem parisiCorrection_integral_sub_le (μ ν : ParisiMeasure) :
    ‖(∫ s in (0 : ℝ)..1, s * parisiCDF μ s) -
        (∫ s in (0 : ℝ)..1, s * parisiCDF ν s)‖ ≤ parisiCDFDistance μ ν := by
  have hi := parisiCorrection_intervalIntegrable μ 0 1
  have hj := parisiCorrection_intervalIntegrable ν 0 1
  have hn : IntervalIntegrable (fun s => ‖parisiCDF μ s - parisiCDF ν s‖)
      volume (0 : ℝ) 1 :=
    ((parisiCDF_monotone μ).intervalIntegrable.sub
      (parisiCDF_monotone ν).intervalIntegrable).norm
  rw [← intervalIntegral.integral_sub hi hj]
  apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    (Eventually.of_forall fun s hs => ?_) hn
  have hsnorm : ‖s‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1.le]
    exact hs.2
  rw [← mul_sub, norm_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hsnorm
    (norm_nonneg (parisiCDF μ s - parisiCDF ν s))

/--
@isnad1 id=le.0h3v.s7.f48c0b36e508 from=translated src=- shape=adb38ac8 vocab=d6572223
-/
theorem parisiCorrection_sub_le (β : ℝ) (μ ν : ParisiMeasure) :
    ‖β ^ 2 / 2 * (∫ s in (0 : ℝ)..1, s * parisiCDF μ s) -
        β ^ 2 / 2 * (∫ s in (0 : ℝ)..1, s * parisiCDF ν s)‖ ≤
      β ^ 2 / 2 * parisiCDFDistance μ ν := by
  rw [← mul_sub, norm_mul,
    Real.norm_of_nonneg (div_nonneg (sq_nonneg β) (by norm_num))]
  exact mul_le_mul_of_nonneg_left (parisiCorrection_integral_sub_le μ ν) (by positivity)

end Paper
