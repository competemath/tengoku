import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterZero.PowerExistence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

/-- A uniform sufficient bound of order `n^6` when `-1` is an `n`-th power.-/
def centerZeroPowerBound (n : ℕ) : ℕ := (6 * n ^ 3 + 6) ^ 2

/-- A simple uniform upper bound for the exact center-zero constant.-/
theorem centerZeroC0_le_three_pow {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n) :
    centerZeroC0 d ≤ 3 * (n : ℝ) ^ 3 := by
  have hpow : (d : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := by
    exact_mod_cast Nat.pow_le_pow_left hdn 3
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hn)
  have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
  unfold centerZeroC0
  nlinarith

/-- The explicit order-`n^6` bound implies the exact Section 12 inequality.-/
theorem centerZero_power_inequality_of_bound {n d q : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) (hq : centerZeroPowerBound n < q) :
    4 * (d : ℝ) ^ 3 + 3 * (d : ℝ) ^ 2 <
      (q : ℝ) - centerZeroC0 d * Real.sqrt (q : ℝ) := by
  have hqR : (6 * (n : ℝ) ^ 3 + 6) ^ 2 < (q : ℝ) := by exact_mod_cast hq
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hn)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (q : ℝ) by positivity)
  have ht0 := Real.sqrt_nonneg (q : ℝ)
  have ht : 6 * (n : ℝ) ^ 3 + 6 < Real.sqrt (q : ℝ) := by
    by_contra h
    have hm := mul_nonneg (sub_nonneg.mpr (le_of_not_gt h))
      (show 0 ≤ 6 * (n : ℝ) ^ 3 + 6 + Real.sqrt (q : ℝ) by positivity)
    nlinarith
  have hC := mul_le_mul_of_nonneg_right (centerZeroC0_le_three_pow hn hdn) ht0
  have hpow : (d : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := by
    exact_mod_cast Nat.pow_le_pow_left hdn 3
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpow2 : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdR) (sq_nonneg (d : ℝ))]
  have hm := mul_pos (show 0 < Real.sqrt (q : ℝ) by linarith)
    (show 0 < Real.sqrt (q : ℝ) - 3 * (n : ℝ) ^ 3 - 6 by linarith)
  nlinarith

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

end MagicSquares
