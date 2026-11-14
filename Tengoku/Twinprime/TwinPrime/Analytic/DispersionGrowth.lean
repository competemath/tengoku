import Tengoku.Twinprime.TwinPrime.Analytic.CutoffLogarithms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Logarithmic losses in a primary-cutoff saving

Every fixed power of the dispersion logarithm is negligible compared with the
fifth-root cutoff. These estimates use only the elementary cutoff comparisons
and standard logarithmic growth, with no arithmetic distribution hypothesis.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

/-- The larger logarithm used in the finite dispersion bounds still costs
only a constant multiple of the cutoff logarithm.
@isnad1 id=le.1h1v.s6.91c1686b0d21 from=translated src=- shape=857676f9 vocab=403a8963
-/
theorem log_four_mul_add_four_le_eight_log_primaryCutoff (X : ℕ) (hX : 1 ≤ X) :
    Real.log (4 * X + 4) ≤ 8 * Real.log (primaryCutoff X + 1) := by
  have hdyadic := log_dyadic_le_seven_log_primaryCutoff X hX
  have hU : 1 ≤ primaryCutoff X := primaryCutoff_pos hX
  have hlog2 : Real.log (2 : ℝ) ≤ Real.log (primaryCutoff X + 1) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast (show 2 ≤ primaryCutoff X + 1 by omega)
  have heq : Real.log (4 * X + 4) = Real.log 2 + Real.log (2 * X + 2) := by
    rw [show (4 * X + 4 : ℝ) = 2 * (2 * X + 2) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  rw [heq]
  linarith

/-- A successor inside a logarithm does not change its negligible growth
relative to a positive integer denominator.
@isnad1 id=tendsto.0h1v.s6.d0c07c83ea8c from=translated src=- shape=9d20fe2d vocab=c2482069
-/
theorem tendsto_log_nat_add_one_pow_div (k : ℕ) :
    Tendsto (fun n : ℕ => (Real.log ((n : ℝ) + 1)) ^ k / n) atTop (nhds 0) := by
  have hbase : Tendsto (fun t : ℝ => (Real.log t) ^ k / t) atTop (nhds 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (k : ℝ) (s := 1) (by norm_num)).tendsto_div_nhds_zero
  have harg : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_natCast_atTop_atTop
    filter_upwards with n
    linarith
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ => 1 + (n : ℝ)⁻¹) atTop (nhds 1) := by
    simpa only [add_zero] using hinv.const_add 1
  have h := (hbase.comp harg).mul hratio
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  dsimp only [Function.comp_def]
  field_simp

/-- Any fixed logarithmic loss is absorbed by one power of the primary cutoff.
@isnad1 id=tendsto.0h1v.s6.70e2c088a24b from=translated src=- shape=0d350ff3 vocab=0b455907
-/
theorem tendsto_dispersion_log_pow_div_primaryCutoff (k : ℕ) :
    Tendsto (fun X : ℕ => (Real.log (4 * X + 4)) ^ k / primaryCutoff X)
      atTop (nhds 0) := by
  have hu := ((tendsto_log_nat_add_one_pow_div k).comp tendsto_primaryCutoff).const_mul
    ((8 : ℝ) ^ k)
  simp only [mul_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards with X
    have hlog : 0 ≤ Real.log (4 * X + 4) := by
      apply Real.log_nonneg
      have := Nat.cast_nonneg (α := ℝ) X
      linarith
    exact div_nonneg (pow_nonneg hlog _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with X hX
    have hlog : 0 ≤ Real.log (4 * X + 4) := by
      apply Real.log_nonneg
      have := Nat.cast_nonneg (α := ℝ) X
      linarith
    have hp := pow_le_pow_left₀ hlog
      (log_four_mul_add_four_le_eight_log_primaryCutoff X hX) k
    have hdiv := div_le_div_of_nonneg_right hp (Nat.cast_nonneg (primaryCutoff X) : (0 : ℝ) ≤ _)
    simpa only [Function.comp_def, mul_pow, mul_div_assoc] using hdiv

/-- A bound with a primary-cutoff denominator remains negligible after any
additional fixed logarithmic weight.
@isnad1 id=tendsto.1h4v.s7.2797c56553e7 from=translated src=- shape=d31e019d vocab=0bd1438f
-/
theorem tendsto_mul_dispersion_log_pow_of_primaryCutoff_bound
    (F : ℕ → ℝ) (C : ℝ) (m k : ℕ)
    (hF : ∀ᶠ X : ℕ in atTop,
      |F X| ≤ C * (Real.log (4 * X + 4)) ^ m / primaryCutoff X) :
    Tendsto (fun X : ℕ => F X * (Real.log (4 * X + 4)) ^ k) atTop (nhds 0) := by
  have hu := (tendsto_dispersion_log_pow_div_primaryCutoff (m + k)).const_mul C
  simp only [mul_zero] at hu
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards with X
    exact abs_nonneg _
  · filter_upwards [hF] with X hX
    have hlog : 0 ≤ Real.log (4 * X + 4) := by
      apply Real.log_nonneg
      have := Nat.cast_nonneg (α := ℝ) X
      linarith
    dsimp only [Function.comp_def]
    rw [abs_mul, abs_of_nonneg (pow_nonneg hlog k)]
    calc
      _ ≤ (C * (Real.log (4 * X + 4)) ^ m / primaryCutoff X) *
          (Real.log (4 * X + 4)) ^ k :=
        mul_le_mul_of_nonneg_right hX (pow_nonneg hlog k)
      _ = _ := by rw [pow_add]; ring

end TwinPrime.Analytic
