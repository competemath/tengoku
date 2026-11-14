import Tengoku.Twinprime.TwinPrime.Analytic.EvenModuli
import Tengoku.Twinprime.TwinPrime.Analytic.Cutoff
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sublinear even-modulus errors at the primary sieve level

The elementary `ψ-θ` error suffices after summation up to `U²`, where
`U = floor(X^(1/5))`. This removes the even-modulus exception without a new
distribution hypothesis or a precise count of powers of two.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

/-- A general dyadic logarithmic error with power strictly below one is sublinear.-/
theorem tendsto_dyadic_power_log_sq_div {a : ℝ} (ha : a < 1) :
    Tendsto (fun X : ℕ => (2 * X + 2 : ℝ) ^ a * (Real.log (2 * X + 2)) ^ 2 / X)
      atTop (nhds 0) := by
  have hlog : Tendsto (fun t : ℝ => (Real.log t) ^ 2 / t ^ (1 - a)) atTop (nhds 0) := by
    simpa only [Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 1 - a) (by linarith)).tendsto_div_nhds_zero
  have harg : Tendsto (fun X : ℕ => (2 : ℝ) * X + 2) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_natCast_atTop_atTop
    filter_upwards with X
    have := Nat.cast_nonneg (α := ℝ) X
    linarith
  have hinv : Tendsto (fun X : ℕ => (X : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun X : ℕ => (2 : ℝ) + 2 * (X : ℝ)⁻¹) atTop (nhds 2) := by
    convert (tendsto_const_nhds.add (hinv.const_mul 2)) using 1
    norm_num
  have h := (hlog.comp harg).mul hratio
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with X hX
  have hx : (X : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hX)
  have hy : (0 : ℝ) < 2 * X + 2 := by positivity
  have hp : (2 * X + 2 : ℝ) ^ (1 - a) ≠ 0 := (Real.rpow_pos_of_pos hy _).ne'
  have heq : (2 * X + 2 : ℝ) ^ a * (2 * X + 2 : ℝ) ^ (1 - a) = 2 * X + 2 := by
    rw [← Real.rpow_add hy]
    simp
  dsimp only [Function.comp_def]
  field_simp
  have heq' : (2 * ((X : ℝ) + 1)) ^ a * (2 * ((X : ℝ) + 1)) ^ (1 - a) =
      2 * ((X : ℝ) + 1) := by simpa only [mul_add, mul_one] using heq
  nlinarith [congrArg (fun t : ℝ => t * (Real.log (2 * ((X : ℝ) + 1))) ^ 2) heq']

/-- Covers every coefficient cap up to `log(2X+2)` on at most `U²+1` moduli.-/
def evenWeightBudget (X : ℕ) : ℝ :=
  ((primaryCutoff X : ℝ) ^ 2 + 1) * Real.log (2 * X + 2) * evenProgressionBound X

theorem evenWeightBudget_nonneg (X : ℕ) : 0 ≤ evenWeightBudget X := by
  unfold evenWeightBudget
  apply mul_nonneg _ (evenProgressionBound_nonneg X)
  apply mul_nonneg (by positivity)
  apply Real.log_nonneg
  have := Nat.cast_nonneg (α := ℝ) X
  linarith

theorem evenWeightBudget_le (X : ℕ) :
    evenWeightBudget X ≤ 4 * (2 * X + 2 : ℝ) ^ (9 / 10 : ℝ) *
      (Real.log (2 * X + 2)) ^ 2 := by
  let Y : ℝ := 2 * X + 2
  have hY : 1 ≤ Y := by dsimp [Y]; have := Nat.cast_nonneg (α := ℝ) X; linarith
  have hlog : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hu : (primaryCutoff X : ℝ) ≤ Y ^ (1 / 5 : ℝ) := by
    apply (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) (1 / 5 : ℝ))).trans
    apply Real.rpow_le_rpow (Nat.cast_nonneg X) _ (by norm_num)
    dsimp [Y]
    have := Nat.cast_nonneg (α := ℝ) X
    linarith
  have hu2 : (primaryCutoff X : ℝ) ^ 2 ≤ Y ^ (2 / 5 : ℝ) := by
    calc
      _ ≤ (Y ^ (1 / 5 : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hu 2
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ Y)]; norm_num
  have hOne : 1 ≤ Y ^ (2 / 5 : ℝ) := Real.one_le_rpow hY (by norm_num)
  have hpow : Y ^ (2 / 5 : ℝ) * Real.sqrt Y = Y ^ (9 / 10 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by linarith : 0 < Y)]
    norm_num
  change ((primaryCutoff X : ℝ) ^ 2 + 1) * Real.log Y *
    (2 * Real.sqrt Y * Real.log Y) ≤ _
  change _ ≤ 4 * Y ^ (9 / 10 : ℝ) * (Real.log Y) ^ 2
  calc
    _ ≤ (2 * Y ^ (2 / 5 : ℝ)) * Real.log Y * (2 * Real.sqrt Y * Real.log Y) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg hY)
    _ = _ := by rw [← hpow]; ring

theorem tendsto_evenWeightBudget_div :
    Tendsto (fun X : ℕ => evenWeightBudget X / X) atTop (nhds 0) := by
  have h := (tendsto_dyadic_power_log_sq_div (a := 9 / 10) (by norm_num)).const_mul 4
  simp only [mul_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · filter_upwards with X
    exact div_nonneg (evenWeightBudget_nonneg X) (Nat.cast_nonneg X)
  · filter_upwards with X
    simpa only [mul_div_assoc, mul_assoc] using
      div_le_div_of_nonneg_right (evenWeightBudget_le X) (Nat.cast_nonneg X)

end TwinPrime.Analytic
