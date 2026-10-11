import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.SelectorEntropyDyadic
import Tengoku

namespace OAI

/-!
# The selector's finite entropy estimate

After scaling row `i` by `4^(i+1)`, its binomial coefficient is bounded by
one term of the exponential series at `T * 2^(-(i+1))`. The sum of these
arguments is at most `T`, so their product is at most `exp T ≤ 3^T`.
This proves the row-count estimate directly, including rows of count zero.
-/

namespace TalagrandThreshold

open scoped BigOperators

/-- A scaled binomial coefficient is bounded by an exponential-series term. -/
theorem selector_choose_le_scaled_exp (m t : ℕ) (d y : ℝ)
    (hd : 0 ≤ d) (hy : 0 ≤ y) (hm : (m : ℝ) ≤ d * y) :
    (m.choose t : ℝ) ≤ d ^ t * Real.exp y := by
  calc
    (m.choose t : ℝ) ≤ (m : ℝ) ^ t / (t.factorial : ℝ) :=
      Nat.choose_le_pow_div t m
    _ ≤ (d * y) ^ t / (t.factorial : ℝ) :=
      div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg m) hm t) (Nat.cast_nonneg _)
    _ = d ^ t * (y ^ t / (t.factorial : ℝ)) := by rw [mul_pow]; ring
    _ ≤ d ^ t * Real.exp y :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp y hy t)
        (pow_nonneg hd t)

end TalagrandThreshold

end OAI
