import Tengoku.Twinprime.TwinPrime.Analytic.GrowthBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Progression errors below any fixed power smaller than one half

The full maximal progression sum retains a logarithmic weight. The modulus
function is arbitrary subject to the displayed eventual power bound.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

/--
@isnad1 id=eventual.2h3v.s7.2e0a334c3e9a from=translated src=- shape=c8b477b9 vocab=7ce57e46
-/
theorem eventually_modulus_le_BV_range_of_power_bound
    (Q : ℕ → ℕ) (a : ℝ) (ha : a < 1 / 2)
    (hQ : ∀ᶠ X : ℕ in atTop, (Q X : ℝ) ≤ (X : ℝ) ^ a) (B : ℝ) :
    ∀ᶠ X : ℕ in atTop, (Q X : ℝ) ≤
      (X : ℝ) ^ (1 / 2 : ℝ) / (Real.log X) ^ B := by
  have hsmall := ((isLittleO_log_rpow_rpow_atTop B (s := 1 / 2 - a)
    (by linarith)).comp_tendsto tendsto_natCast_atTop_atTop).eventuallyLE
  filter_upwards [hsmall, hQ, eventually_ge_atTop 2] with X hX hQX hX2
  have hx : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hlog : 0 < Real.log X := Real.log_pos hx
  have hden : 0 < (Real.log X) ^ B := Real.rpow_pos_of_pos hlog B
  have hpow : (Real.log X) ^ B ≤ (X : ℝ) ^ (1 / 2 - a) := by
    dsimp only [Function.comp_def] at hX
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog.le B),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) (1 / 2 - a))] using hX
  apply (le_div_iff₀ hden).mpr
  calc
    _ ≤ (X : ℝ) ^ a * (X : ℝ) ^ (1 / 2 - a) :=
      mul_le_mul hQX hpow hden.le (Real.rpow_nonneg (Nat.cast_nonneg X) _)
    _ = _ := by rw [← Real.rpow_add (lt_trans zero_lt_one hx)]; congr 1; ring

/--
@isnad1 id=tendsto.3h2v.s7.de6e428cfbd2 from=translated src=- shape=7e7a2a61 vocab=82691c21
-/
theorem MaximalBombieriVinogradov.tendsto_log_mul_sum_error_div_of_power_level
    (hBV : MaximalBombieriVinogradov) (Q : ℕ → ℕ) (a : ℝ) (ha : a < 1 / 2)
    (hQ : ∀ᶠ X : ℕ in atTop, (Q X : ℝ) ≤ (X : ℝ) ^ a) :
    Tendsto (fun X : ℕ => Real.log (2 * X + 2) *
      (∑ q ∈ Icc 1 (Q X), progressionMaxError (2 * X + 2) q) / X)
      atTop (nhds 0) := by
  obtain ⟨B, _, K, _, X₀, _, hdist⟩ := hBV 2 (by norm_num)
  have hinv : Tendsto (fun X : ℕ => (Real.log X)⁻¹) atTop (nhds 0) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have hu : Tendsto (fun X : ℕ => (2 * K) / Real.log X) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul (2 * K)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards with X
    exact div_nonneg (mul_nonneg (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith))
      (sum_nonneg fun q _ => progressionMaxError_nonneg _ q)) (Nat.cast_nonneg X)
  · filter_upwards [eventually_modulus_le_BV_range_of_power_bound Q a ha hQ B,
        eventually_ge_atTop X₀, eventually_ge_atTop 3] with X hQX hX₀ hX3
    have hx : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    have hlog : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    have hS : (∑ q ∈ Icc 1 (Q X), progressionMaxError (2 * X + 2) q) ≤
        K * X / (Real.log X) ^ 2 := by
      simpa only [Real.rpow_two] using hdist X hX₀ (Q X) hQX
    calc
      _ ≤ (2 * Real.log X) * (K * X / (Real.log X) ^ 2) / X := by
        apply div_le_div_of_nonneg_right _ hx.le
        exact mul_le_mul (log_two_mul_add_two_le_two_log hX3) hS
          (sum_nonneg fun q _ => progressionMaxError_nonneg _ q) (by positivity)
      _ = _ := by field_simp

end TwinPrime.Analytic
