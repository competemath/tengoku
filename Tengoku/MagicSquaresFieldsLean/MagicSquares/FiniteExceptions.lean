import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterOne.PowerCount

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finitely many odd n-Parker cardinalities (paper, Theorem 15.1)

The center-one existence theorem uses an inequality involving the power
index d = gcd(n, q - 1). This file bounds its constants using d <= n, then
shows that q > (10*n^8 + 10)^2 implies the required inequality.

Thus every exceptional odd cardinality lies in a finite initial interval.
The numerical bound is sufficient, not an optimal cutoff.
-/

namespace MagicSquares

/-- An explicit (deliberately nonoptimal) uniform bound of order `n^16`.-/
def powerExceptionBound (n : ℕ) : ℕ := (10 * n ^ 8 + 10) ^ 2

/-- The Section 14 constant is uniformly bounded in terms of the exponent.
@isnad1 id=le.2h2v.s5.7c949bb16413 from=translated src=- shape=5c7b8f05 vocab=fd3e26dd
-/
theorem centerOneC1_le_eight_pow {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n) :
    centerOneC1 d ≤ 8 * (n : ℝ) ^ 8 := by
  have hpow : (d : ℝ) ^ 8 ≤ (n : ℝ) ^ 8 := by
    exact_mod_cast Nat.pow_le_pow_left hdn 8
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 8 :=
    one_le_pow₀ (by exact_mod_cast hn)
  have hd7 : (0 : ℝ) ≤ (d : ℝ) ^ 7 := by positivity
  unfold centerOneC1
  nlinarith

/-- Above the explicit bound, the exact numerical hypothesis of
Theorem 14.1 holds for every possible power index.
@isnad1 id=lt.3h3v.s6.b90038bb8775 from=translated src=- shape=a06670d9 vocab=6385c6cb
-/
theorem centerOne_power_inequality_of_bound {n d q : ℕ}
    (hn : 0 < n) (hdn : d ≤ n) (hq : powerExceptionBound n < q) :
    9 * (d : ℝ) ^ 8 < (q : ℝ) - centerOneC1 d * Real.sqrt (q : ℝ) := by
  have hqR : (10 * (n : ℝ) ^ 8 + 10) ^ 2 < (q : ℝ) := by
    exact_mod_cast hq
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 8 :=
    one_le_pow₀ (by exact_mod_cast hn)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (q : ℝ) by positivity)
  have ht0 := Real.sqrt_nonneg (q : ℝ)
  have ht : 10 * (n : ℝ) ^ 8 + 10 < Real.sqrt (q : ℝ) := by
    by_contra h
    have hle := le_of_not_gt h
    have hm := mul_nonneg (sub_nonneg.mpr hle)
      (show 0 ≤ 10 * (n : ℝ) ^ 8 + 10 + Real.sqrt (q : ℝ) by positivity)
    nlinarith
  have hC := mul_le_mul_of_nonneg_right (centerOneC1_le_eight_pow hn hdn) ht0
  have hpow : (d : ℝ) ^ 8 ≤ (n : ℝ) ^ 8 := by
    exact_mod_cast Nat.pow_le_pow_left hdn 8
  have hm := mul_pos (show 0 < Real.sqrt (q : ℝ) by linarith)
    (show 0 < Real.sqrt (q : ℝ) - 8 * (n : ℝ) ^ 8 - 10 by linarith)
  nlinarith

namespace Square3

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

end Square3

end MagicSquares
