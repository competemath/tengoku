import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Algebra.Order.Floor.Semifield
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An explicit natural cutoff for the centered residue estimate

The ceiling preserves the required lower bound on the cutoff and costs
at most a factor two in its upper bound. The constants are numerical:
`18522 = 441 * 42` and `37044 = 2 * 18522`.
-/

noncomputable section

namespace TwinPrime.Analytic

def residueCutoff (C : ℝ) : ℕ := ⌈(37044 * C) ^ 20⌉₊

theorem power_le_residueCutoff (C : ℝ) :
    (37044 * C) ^ 20 ≤ (residueCutoff C : ℝ) := Nat.le_ceil _

theorem one_le_residueCutoff (C : ℝ) (hC : 1 ≤ C) : 1 ≤ residueCutoff C := by
  apply Nat.one_le_ceil_iff.mpr
  have : 0 < C := by linarith
  positivity

theorem residueCutoff_le_twice_power (C : ℝ) (hC : 1 ≤ C) :
    (residueCutoff C : ℝ) ≤ 2 * (37044 * C) ^ 20 := by
  have hp : (1 : ℝ) ≤ (37044 * C) ^ 20 := one_le_pow₀ (by linarith)
  exact Nat.ceil_le_two_mul (by norm_num; linarith)

theorem residueCutoff_error_le_half (C : ℝ) (hC : 1 ≤ C) :
    18522 * C * (residueCutoff C : ℝ) ^ (-(1 / 20 : ℝ)) ≤ 1 / 2 := by
  have hC0 : 0 < C := by linarith
  have hbase : 0 < 37044 * C := by positivity
  have hp := Real.rpow_le_rpow_of_nonpos (pow_pos hbase 20)
    (power_le_residueCutoff C) (by norm_num : -(1 / 20 : ℝ) ≤ 0)
  calc
    _ ≤ 18522 * C * ((37044 * C) ^ 20) ^ (-(1 / 20 : ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 18522 * C * (37044 * C)⁻¹ := by
      rw [← Real.rpow_natCast_mul hbase.le]
      norm_num [Real.rpow_neg_one]
    _ = _ := by
      field_simp
      ring

end TwinPrime.Analytic
