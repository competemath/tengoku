import Tengoku.Twinprime.TwinPrime.Analytic.LogPowerEvenBudget
import Tengoku.Twinprime.TwinPrime.Correlation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Arbitrary fixed logarithmic savings for the actual prime-power error

The explicit Chebyshev bound on Epp is of square-root size up to logarithms.
Thus the actual excluded correlation has zero normalized limit even after
multiplication by any fixed natural power of log(2X+2).
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

/--
@isnad1 id=tendsto.0h1v.s6.5a54165ac9a4 from=translated src=- shape=801b52e0 vocab=4cd93d55
-/
theorem tendsto_Epp_div_mul_log_pow (k : ℕ) :
    Tendsto (fun X : ℕ => Epp X / X * (Real.log (2 * X + 2)) ^ k)
      atTop (nhds 0) := by
  have h := (tendsto_dyadic_power_log_pow_div (2 + k) (a := 1 / 2)
    (by norm_num)).const_mul 4
  simp only [mul_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · filter_upwards with X
    exact mul_nonneg (div_nonneg (Epp_nonneg X) (Nat.cast_nonneg X))
      (pow_nonneg (Real.log_nonneg (by
        have := Nat.cast_nonneg (α := ℝ) X
        linarith)) k)
  · filter_upwards with X
    have hlog : 0 ≤ Real.log (2 * X + 2) := Real.log_nonneg (by
      have := Nat.cast_nonneg (α := ℝ) X
      linarith)
    calc
      _ ≤ (4 * Real.sqrt (2 * X + 2) * (Real.log (2 * X + 2)) ^ 2 / X) *
          (Real.log (2 * X + 2)) ^ k :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (Epp_le_sqrt_mul_log_sq X) (Nat.cast_nonneg X))
          (pow_nonneg hlog k)
      _ = _ := by rw [Real.sqrt_eq_rpow, pow_add]; ring

end TwinPrime.Analytic
