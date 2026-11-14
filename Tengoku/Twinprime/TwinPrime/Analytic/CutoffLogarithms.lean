import Tengoku.Twinprime.TwinPrime.Analytic.MixedCorrelation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transferring logarithmic cancellation through the primary cutoff

The fifth-root floor has the inverse bound `X < (U(X)+1)^5`, so the dyadic
logarithm costs at most seven times `log(U(X)+1)`. The resulting limit lemmas
apply to an arbitrary real sequence and introduce no arithmetic hypothesis.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

/-- The upper side of the floor estimate, with a strictly positive successor.
@isnad1 id=lt.0h1v.s5.642c6494d7ab from=translated src=- shape=c4df414f vocab=07bf6d9a
-/
theorem primaryCutoff_inverse_bound (X : ℕ) : X < (primaryCutoff X + 1) ^ 5 := by
  have hfloor : (X : ℝ) ^ (1 / 5 : ℝ) < (primaryCutoff X : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hp := pow_lt_pow_left₀ hfloor (Real.rpow_nonneg (Nat.cast_nonneg X) _)
    (show (5 : ℕ) ≠ 0 by decide)
  have heq : ((X : ℝ) ^ (1 / 5 : ℝ)) ^ (5 : ℕ) = X := by
    rw [show (1 / 5 : ℝ) = ((5 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow (Nat.cast_nonneg X) (by decide)
  rw [heq] at hp
  exact_mod_cast hp

/-- The inverse cutoff comparison needed to transfer logarithmic decay.
@isnad1 id=le.1h1v.s6.737b3d83c4eb from=translated src=- shape=857676f9 vocab=403a8963
-/
theorem log_dyadic_le_seven_log_primaryCutoff (X : ℕ) (hX : 1 ≤ X) :
    Real.log (2 * X + 2) ≤ 7 * Real.log (primaryCutoff X + 1) := by
  let U := primaryCutoff X
  have hx : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hU : 1 ≤ U := primaryCutoff_pos hX
  have hUr : (2 : ℝ) ≤ (U : ℝ) + 1 := by exact_mod_cast (show 2 ≤ U + 1 by omega)
  have hinv : (X : ℝ) < ((U : ℝ) + 1) ^ (5 : ℕ) := by
    exact_mod_cast primaryCutoff_inverse_bound X
  have hlogX : Real.log X ≤ 5 * Real.log ((U : ℝ) + 1) := by
    have h := Real.log_le_log hx hinv.le
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hlog2 : Real.log (2 : ℝ) ≤ Real.log ((U : ℝ) + 1) :=
    Real.log_le_log (by norm_num) hUr
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  calc
    Real.log (2 * X + 2) ≤ Real.log (4 * (X : ℝ)) := by
      apply Real.log_le_log (by positivity)
      have hxr : (1 : ℝ) ≤ X := by exact_mod_cast hX
      linarith
    _ = Real.log 4 + Real.log X := Real.log_mul (by norm_num) hx.ne'
    _ ≤ 7 * Real.log (primaryCutoff X + 1) := by rw [hfour]; dsimp [U] at *; linarith

private theorem tendsto_inv_log_nat_add_one :
    Tendsto (fun n : ℕ => (Real.log ((n : ℝ) + 1))⁻¹) atTop (nhds 0) := by
  have harg : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_natCast_atTop_atTop
    filter_upwards with n
    linarith
  exact (Real.tendsto_log_atTop.comp harg).inv_tendsto_atTop

/-- A square-logarithmic saving implies a single-logarithmic saving.
@isnad1 id=tendsto.1h1v.s6.b722b8372b80 from=translated src=- shape=0e8e72c0 vocab=e7bc1b26
-/
theorem tendsto_mul_log_of_mul_log_sq_tendsto_zero (F : ℕ → ℝ)
    (hF : Tendsto (fun n : ℕ => F n * (Real.log (n + 1)) ^ 2) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => F n * Real.log (n + 1)) atTop (nhds 0) := by
  have h := hF.mul tendsto_inv_log_nat_add_one
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hlog : Real.log ((n : ℝ) + 1) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))).ne'
  field_simp

/-- Ordinary decay follows from square-logarithmic decay.
@isnad1 id=tendsto.1h1v.s6.e12f543816f8 from=translated src=- shape=a58abafa vocab=e7bc1b26
-/
theorem tendsto_of_mul_log_sq_tendsto_zero (F : ℕ → ℝ)
    (hF : Tendsto (fun n : ℕ => F n * (Real.log (n + 1)) ^ 2) atTop (nhds 0)) :
    Tendsto F atTop (nhds 0) := by
  have h := (tendsto_mul_log_of_mul_log_sq_tendsto_zero F hF).mul
    tendsto_inv_log_nat_add_one
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hlog : Real.log ((n : ℝ) + 1) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))).ne'
  field_simp

/-- Cancellation of an arbitrary sequence transfers to the primary cutoff
with the full dyadic logarithmic weight.
@isnad1 id=tendsto.1h1v.s7.97f87932c762 from=translated src=- shape=6b1c4099 vocab=8b515542
-/
theorem tendsto_primary_mul_log_of_mul_log_sq_tendsto_zero (F : ℕ → ℝ)
    (hF : Tendsto (fun n : ℕ => F n * (Real.log (n + 1)) ^ 2) atTop (nhds 0)) :
    Tendsto (fun X : ℕ => F (primaryCutoff X) * Real.log (2 * X + 2))
      atTop (nhds 0) := by
  have hG := (tendsto_mul_log_of_mul_log_sq_tendsto_zero F hF).comp tendsto_primaryCutoff
  have hu := hG.abs.const_mul 7
  simp only [abs_zero, mul_zero] at hu
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards with X
    exact abs_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with X hX
    have hY : 0 ≤ Real.log (2 * X + 2) := by
      apply Real.log_nonneg
      have := Nat.cast_nonneg (α := ℝ) X
      linarith
    have hU : 0 ≤ Real.log (primaryCutoff X + 1) := by
      apply Real.log_nonneg
      have := Nat.cast_nonneg (α := ℝ) (primaryCutoff X)
      linarith
    dsimp only [Function.comp_def]
    calc
      |F (primaryCutoff X) * Real.log (2 * X + 2)| =
          |F (primaryCutoff X)| * Real.log (2 * X + 2) := by
        rw [abs_mul, abs_of_nonneg hY]
      _ ≤ |F (primaryCutoff X)| * (7 * Real.log (primaryCutoff X + 1)) :=
        mul_le_mul_of_nonneg_left (log_dyadic_le_seven_log_primaryCutoff X hX) (abs_nonneg _)
      _ = 7 * |F (primaryCutoff X) * Real.log (primaryCutoff X + 1)| := by
        rw [abs_mul, abs_of_nonneg hU]
        ring

end TwinPrime.Analytic
