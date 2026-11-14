import Tengoku.Twinprime.TwinPrime.Analytic.MixedTypeICorrelation
import Tengoku.Twinprime.TwinPrime.Analytic.BilinearCutoffShift
import Tengoku.Twinprime.TwinPrime.Analytic.QuarterCutoff
import Tengoku.Twinprime.TwinPrime.Analytic.ClassicalDistribution
import Tengoku.Twinprime.TwinPrime.Analytic.PrimeBetaReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Removing the beta band up to a fourth-root cutoff

The left cutoff remains the fifth root. The right cutoff can be raised to
the fourth root at signed o(X) cost, using the independently proved classical
inputs. This is a whole-sum estimate, not a factorwise absolute band bound.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

theorem eventually_rightCutoff_le_of_primary_product_bound (W : ℕ → ℕ)
    (a : ℝ) (ha : a ≤ 1)
    (hprod : ∀ᶠ X : ℕ in atTop,
      ((primaryCutoff X * W X : ℕ) : ℝ) ≤ (X : ℝ) ^ a) :
    ∀ᶠ X : ℕ in atTop, W X ≤ X := by
  filter_upwards [hprod, eventually_ge_atTop 1] with X hPX hX
  have hp : primaryCutoff X * W X ≤ X := by
    exact_mod_cast hPX.trans (Real.rpow_le_self_of_one_le (by exact_mod_cast hX) ha)
  exact (Nat.le_mul_of_pos_left (W X) (primaryCutoff_pos hX)).trans hp

theorem tendsto_quarter_bilinear_sub_primeBeta_div_mul_log_pow (U : ℕ → ℕ) (k : ℕ) :
    Tendsto (fun X : ℕ =>
      (bilinearTerm (U X) (quarterCutoff X) X - bilinearPrimeBeta (U X) (quarterCutoff X) X) /
        X * (Real.log (4 * X + 4)) ^ k) atTop (nhds 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_abs_bilinear_sub_primeBeta_bound
  apply tendsto_mul_dispersion_log_pow_of_primaryCutoff_neg_half_bound _ C 2 k
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have hU : (0 : ℝ) < primaryCutoff X := by exact_mod_cast primaryCutoff_pos hX
  have hpow : (quarterCutoff X : ℝ) ^ (-1 / 2 : ℝ) ≤
      (primaryCutoff X : ℝ) ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hU (by exact_mod_cast primaryCutoff_le_quarterCutoff hX)
      (by norm_num)
  rw [abs_div, abs_of_nonneg hx.le]
  calc
    _ ≤ (C * (X : ℝ) * (Real.log (4 * X + 4)) ^ 2 *
        (quarterCutoff X : ℝ) ^ (-1 / 2 : ℝ)) / X :=
      div_le_div_of_nonneg_right (hbound (U X) (quarterCutoff X) X
        (quarterCutoff_pos hX) hX) hx.le
    _ = C * (Real.log (4 * X + 4)) ^ 2 * (quarterCutoff X : ℝ) ^ (-1 / 2 : ℝ) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

theorem tendsto_quarter_bilinear_sub_primeBeta_div (U : ℕ → ℕ) :
    Tendsto (fun X : ℕ =>
      (bilinearTerm (U X) (quarterCutoff X) X - bilinearPrimeBeta (U X) (quarterCutoff X) X) / X)
      atTop (nhds 0) := by
  simpa using tendsto_quarter_bilinear_sub_primeBeta_div_mul_log_pow U 0

end TwinPrime.Analytic
