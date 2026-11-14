import Tengoku.Twinprime.TwinPrime.Analytic.DispersionGrowth

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Logarithmic losses in the prime-beta error

A reciprocal square-root of the primary cutoff absorbs every fixed power
of the dispersion logarithm. These numerical limits supply no estimate for
the signed prime correlation that remains after simplifying the beta weight.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

/--
@isnad1 id=tendsto.0h1v.s6.0c8da7775034 from=translated src=- shape=e9b2b10d vocab=795625b6
-/
theorem tendsto_dispersion_log_pow_mul_primaryCutoff_neg_half (k : ℕ) :
    Tendsto (fun X : ℕ => (Real.log (4 * X + 4)) ^ k *
      (primaryCutoff X : ℝ) ^ (-1 / 2 : ℝ)) atTop (nhds 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp
    (tendsto_dispersion_log_pow_div_primaryCutoff (2 * k))
  simp only [Real.sqrt_zero] at h
  apply h.congr'
  filter_upwards with X
  have hL : 0 ≤ Real.log (4 * (X : ℝ) + 4) := by
    apply Real.log_nonneg
    have := Nat.cast_nonneg (α := ℝ) X
    linarith
  dsimp only [Function.comp_def]
  rw [show (Real.log (4 * (X : ℝ) + 4)) ^ (2 * k) =
      ((Real.log (4 * (X : ℝ) + 4)) ^ k) ^ 2 by rw [← pow_mul, Nat.mul_comm],
    Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (pow_nonneg hL k),
    show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
    Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow, div_eq_mul_inv]

/--
@isnad1 id=tendsto.0h1v.s6.e8f051be91a8 from=translated src=- shape=44ab026a vocab=b944e909
-/
theorem tendsto_dispersion_log_pow_div_sqrt_primaryCutoff (k : ℕ) :
    Tendsto (fun X : ℕ => (Real.log (4 * X + 4)) ^ k /
      Real.sqrt (primaryCutoff X : ℝ)) atTop (nhds 0) := by
  have h := tendsto_dispersion_log_pow_mul_primaryCutoff_neg_half k
  apply h.congr'
  filter_upwards with X
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
    Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow, div_eq_mul_inv]

/-- A square-root cutoff saving remains negligible after any additional
fixed power of the logarithm. The eventual bound is the sole input.
@isnad1 id=tendsto.1h4v.s7.e62b9eae8272 from=translated src=- shape=ca4e3b10 vocab=e17c2b02
-/
theorem tendsto_mul_dispersion_log_pow_of_primaryCutoff_neg_half_bound
    (F : ℕ → ℝ) (C : ℝ) (m k : ℕ)
    (hF : ∀ᶠ X : ℕ in atTop, |F X| ≤
      C * (Real.log (4 * X + 4)) ^ m * (primaryCutoff X : ℝ) ^ (-1 / 2 : ℝ)) :
    Tendsto (fun X : ℕ => F X * (Real.log (4 * X + 4)) ^ k) atTop (nhds 0) := by
  have hu := (tendsto_dispersion_log_pow_mul_primaryCutoff_neg_half (m + k)).const_mul C
  simp only [mul_zero] at hu
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards with X
    exact abs_nonneg _
  · filter_upwards [hF] with X hX
    have hL : 0 ≤ Real.log (4 * (X : ℝ) + 4) := by
      apply Real.log_nonneg
      have := Nat.cast_nonneg (α := ℝ) X
      linarith
    dsimp only [Function.comp_def]
    rw [abs_mul, abs_of_nonneg (pow_nonneg hL k)]
    calc
      _ ≤ (C * (Real.log (4 * X + 4)) ^ m *
          (primaryCutoff X : ℝ) ^ (-1 / 2 : ℝ)) * (Real.log (4 * X + 4)) ^ k :=
        mul_le_mul_of_nonneg_right hX (pow_nonneg hL k)
      _ = _ := by rw [pow_add]; ring

end TwinPrime.Analytic
