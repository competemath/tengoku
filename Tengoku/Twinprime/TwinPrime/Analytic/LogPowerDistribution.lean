import Tengoku.Twinprime.TwinPrime.Analytic.PowerLevelDistribution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Arbitrary fixed logarithmic weights on progression errors

The modulus function may be arbitrary below a fixed power smaller than one half.
The logarithmic exponent is fixed before taking the limit.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

theorem MaximalBombieriVinogradov.tendsto_log_pow_mul_sum_error_div_of_power_level
    (hBV : MaximalBombieriVinogradov) (Q : ℕ → ℕ) (a : ℝ) (ha : a < 1 / 2)
    (hQ : ∀ᶠ X : ℕ in atTop, (Q X : ℝ) ≤ (X : ℝ) ^ a) (k : ℕ) :
    Tendsto (fun X : ℕ => Real.log (2 * X + 2) ^ k *
      (∑ q ∈ Icc 1 (Q X), progressionMaxError (2 * X + 2) q) / X)
      atTop (nhds 0) := by
  obtain ⟨B, _, K, _, X₀, _, hdist⟩ := hBV (k + 1 : ℕ) (by positivity)
  have hinv : Tendsto (fun X : ℕ => (Real.log X)⁻¹) atTop (nhds 0) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have hu : Tendsto (fun X : ℕ => (2 ^ k * K) / Real.log X) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul (2 ^ k * K)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards with X
    exact div_nonneg (mul_nonneg (pow_nonneg (Real.log_nonneg
      (by have := Nat.cast_nonneg (α := ℝ) X; linarith)) k)
      (sum_nonneg fun q _ => progressionMaxError_nonneg _ q)) (Nat.cast_nonneg X)
  · filter_upwards [eventually_modulus_le_BV_range_of_power_bound Q a ha hQ B,
        eventually_ge_atTop X₀, eventually_ge_atTop 3] with X hQX hX₀ hX3
    have hx : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    have hlog : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    have hL : 0 ≤ Real.log (2 * (X : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hS : (∑ q ∈ Icc 1 (Q X), progressionMaxError (2 * X + 2) q) ≤
        K * X / (Real.log X) ^ (k + 1) := by
      simpa only [Real.rpow_natCast] using hdist X hX₀ (Q X) hQX
    calc
      _ ≤ (2 * Real.log X) ^ k * (K * X / (Real.log X) ^ (k + 1)) / X := by
        apply div_le_div_of_nonneg_right _ hx.le
        exact mul_le_mul (pow_le_pow_left₀ hL (log_two_mul_add_two_le_two_log hX3) k)
          hS (sum_nonneg fun q _ => progressionMaxError_nonneg _ q) (by positivity)
      _ = _ := by rw [mul_pow, pow_succ]; field_simp

end TwinPrime.Analytic
