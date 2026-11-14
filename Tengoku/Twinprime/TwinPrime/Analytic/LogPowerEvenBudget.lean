import Tengoku.Twinprime.TwinPrime.Analytic.MixedEvenBudget
import Tengoku.Twinprime.TwinPrime.Analytic.BilinearExceptional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Arbitrary fixed logarithmic savings for the even-modulus budget

A power gap below one dominates every fixed natural logarithmic power.
Applied to the existing finite mixed even-modulus bound, this retains
arbitrary fixed logarithmic precision whenever the cutoff product has
an exponent strictly below one half.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

/--
@isnad1 id=tendsto.3h4v.s7.703a18b939ba from=translated src=- shape=1336191f vocab=557f69dc
-/
theorem tendsto_mixedEvenWeightBudget_div_mul_log_pow
    (U V : ℕ → ℕ) (a : ℝ) (ha : 0 ≤ a) (haHalf : a < 1 / 2)
    (hUV : ∀ᶠ X : ℕ in atTop, ((U X * V X : ℕ) : ℝ) ≤ (X : ℝ) ^ a)
    (k : ℕ) :
    Tendsto (fun X : ℕ => mixedEvenWeightBudget (U X) (V X) X / X *
      (Real.log (2 * X + 2)) ^ k) atTop (nhds 0) := by
  have h := (tendsto_dyadic_power_log_pow_div (2 + k) (a := a + 1 / 2)
    (by linarith)).const_mul 4
  simp only [mul_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · filter_upwards with X
    exact mul_nonneg
      (div_nonneg (mixedEvenWeightBudget_nonneg _ _ _) (Nat.cast_nonneg X))
      (pow_nonneg (Real.log_nonneg (by
        have := Nat.cast_nonneg (α := ℝ) X
        linarith)) k)
  · filter_upwards [hUV] with X hX
    have hbase : (X : ℝ) ^ a ≤ (2 * X + 2 : ℝ) ^ a := by
      apply Real.rpow_le_rpow (Nat.cast_nonneg X) _ ha
      have := Nat.cast_nonneg (α := ℝ) X
      linarith
    have hb := mixedEvenWeightBudget_le_of_product_le (U X) (V X) X a ha
      (hX.trans hbase)
    have hlog : 0 ≤ Real.log (2 * X + 2) := Real.log_nonneg (by
      have := Nat.cast_nonneg (α := ℝ) X
      linarith)
    calc
      _ ≤ (4 * (2 * X + 2 : ℝ) ^ (a + 1 / 2) *
          (Real.log (2 * X + 2)) ^ 2 / X) * (Real.log (2 * X + 2)) ^ k :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hb (Nat.cast_nonneg X)) (pow_nonneg hlog k)
      _ = _ := by rw [pow_add]; ring

end TwinPrime.Analytic
