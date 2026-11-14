import Tengoku.Twinprime.TwinPrime.Analytic.ClassicalCenterPrecision
import Tengoku.Twinprime.TwinPrime.Analytic.QuarterBilinearReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The finite classical center at the primary and quarter cutoffs

The actual Bombieri--Vinogradov theorem gives every fixed logarithmic saving
for the errors around the finite classical center. The primary-to-quarter
change is centered with the respective finite Type I main terms. Replacing
the quarter beta coefficient by its prime-only part preserves this precision.
None of these estimates is a signed lower bound for the centered expression.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

/-- The prime-only replacement error also permits the smaller logarithm used
by the classical center, uniformly in the choice of left cutoff.
@isnad1 id=tendsto.0h2v.s6.678d64026e8a from=translated src=- shape=6ab26712 vocab=f5e22df1
-/
theorem tendsto_quarter_abs_bilinear_sub_primeBeta_div_mul_log_two_pow
    (U : ℕ → ℕ) (k : ℕ) :
    Tendsto (fun X : ℕ =>
      |bilinearTerm (U X) (quarterCutoff X) X -
        bilinearPrimeBeta (U X) (quarterCutoff X) X| /
        X * Real.log (2 * X + 2) ^ k) atTop (nhds 0) := by
  have h := (tendsto_quarter_bilinear_sub_primeBeta_div_mul_log_pow U k).abs
  simp only [abs_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · filter_upwards with X
    exact mul_nonneg (div_nonneg (abs_nonneg _) (Nat.cast_nonneg X))
      (pow_nonneg (Real.log_nonneg (by
        have := Nat.cast_nonneg (α := ℝ) X
        linarith)) k)
  · filter_upwards with X
    have hX : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    have hL2 : 0 ≤ Real.log (2 * (X : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hL4 : 0 ≤ Real.log (4 * (X : ℝ) + 4) := Real.log_nonneg (by linarith)
    have hlog : Real.log (2 * (X : ℝ) + 2) ≤ Real.log (4 * (X : ℝ) + 4) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [abs_mul, abs_div, abs_of_nonneg hX, abs_of_nonneg (pow_nonneg hL4 k)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL2 hlog k)
      (div_nonneg (abs_nonneg _) hX)

end TwinPrime.Analytic
