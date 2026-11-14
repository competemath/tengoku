import Tengoku.Twinprime.TwinPrime.Analytic.Cutoff
import Tengoku.Twinprime.TwinPrime.Analytic.PrimeDistribution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The primary cutoff lies inside the distribution range

The squared fifth-root cutoff is at most `X^(2/5)`, and is eventually at most
`X^(1/2) / log(X)^B` for every fixed real `B`. Under the explicitly named
maximal Bombieri–Vinogradov hypothesis, the complete progression-error sum up
to the squared cutoff remains sublinear after one logarithmic weight.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

/-- Both primary factors together use moduli no larger than `X^(2/5)`.
@isnad1 id=le.0h1v.s6.700ac21b07d7 from=translated src=- shape=94fc8469 vocab=34772e32
-/
theorem primaryCutoff_sq_le_rpow (X : ℕ) :
    ((primaryCutoff X ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ (2 / 5 : ℝ) := by
  have hc : (primaryCutoff X : ℝ) ≤ (X : ℝ) ^ (1 / 5 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) _)
  calc
    ((primaryCutoff X ^ 2 : ℕ) : ℝ) = (primaryCutoff X : ℝ) ^ 2 := by norm_cast
    _ ≤ ((X : ℝ) ^ (1 / 5 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
    _ = (X : ℝ) ^ (2 / 5 : ℝ) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg X)]
      norm_num

/-- The fixed power margin absorbs any fixed logarithmic restriction.
@isnad1 id=eventual.0h1v.s6.4071b9230d2c from=translated src=- shape=5a4f8c71 vocab=8021f208
-/
theorem eventually_primaryCutoff_sq_le_BV_range (B : ℝ) :
    ∀ᶠ X : ℕ in atTop,
      ((primaryCutoff X ^ 2 : ℕ) : ℝ) ≤
        (X : ℝ) ^ (1 / 2 : ℝ) / (Real.log X) ^ B := by
  have hsmall := ((isLittleO_log_rpow_rpow_atTop B (s := 1 / 10)
    (by norm_num)).comp_tendsto tendsto_natCast_atTop_atTop).eventuallyLE
  filter_upwards [hsmall, eventually_ge_atTop 2] with X hX hX2
  have hx : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hlog : 0 < Real.log X := Real.log_pos hx
  have hden : 0 < (Real.log X) ^ B := Real.rpow_pos_of_pos hlog B
  have hpow : (Real.log X) ^ B ≤ (X : ℝ) ^ (1 / 10 : ℝ) := by
    dsimp only [Function.comp_def] at hX
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog.le B),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) (1 / 10 : ℝ))] using hX
  apply (le_div_iff₀ hden).mpr
  calc
    _ ≤ (X : ℝ) ^ (2 / 5 : ℝ) * (X : ℝ) ^ (1 / 10 : ℝ) :=
      mul_le_mul (primaryCutoff_sq_le_rpow X) hpow hden.le
        (Real.rpow_nonneg (Nat.cast_nonneg X) _)
    _ = _ := by
      rw [← Real.rpow_add (lt_trans zero_lt_one hx)]
      norm_num

/-- The complete maximal progression-error sum needed for the primary Type I range.-/
def primaryProgressionError (X : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 (primaryCutoff X ^ 2), progressionMaxError (2 * X + 2) q

/--
@isnad1 id=le.0h1v.s3.921e0e7c1501 from=translated src=- shape=b9369acb vocab=92b53769
-/
theorem primaryProgressionError_nonneg (X : ℕ) : 0 ≤ primaryProgressionError X :=
  sum_nonneg fun q _ => progressionMaxError_nonneg _ q

/--
@isnad1 id=le.1h2v.s6.e2fa79236fbe from=translated src=- shape=a18c5f86 vocab=2f528285
-/
theorem sum_progressionMaxError_le_primary {Q X : ℕ}
    (hQ : Q ≤ primaryCutoff X ^ 2) :
    (∑ q ∈ Icc 1 Q, progressionMaxError (2 * X + 2) q) ≤ primaryProgressionError X := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro q hq
    exact mem_Icc.mpr ⟨(mem_Icc.mp hq).1, (mem_Icc.mp hq).2.trans hQ⟩
  · exact fun q _ _ => progressionMaxError_nonneg _ q

/-- An elementary comparison of the dyadic logarithm with the scale logarithm.
@isnad1 id=le.1h1v.s6.3e8b0da78e56 from=translated src=- shape=eff19de0 vocab=45c294fc
-/
theorem log_two_mul_add_two_le_two_log {X : ℕ} (hX : 3 ≤ X) :
    Real.log (2 * X + 2) ≤ 2 * Real.log X := by
  have hx : (3 : ℝ) ≤ X := by exact_mod_cast hX
  have hle : (2 : ℝ) * X + 2 ≤ (X : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((X : ℝ) - 3)]
  calc
    Real.log (2 * X + 2) ≤ Real.log ((X : ℝ) ^ 2) :=
      Real.log_le_log (by positivity) hle
    _ = _ := by rw [Real.log_pow]; norm_num

/-- Under (BV), one logarithmic weight on the full primary modulus range still
costs `o(X)`. The distribution theorem remains an explicit hypothesis.
@isnad1 id=tendsto.1h0v.s6.80111ea83180 from=translated src=- shape=00055cad vocab=2b1ea155
-/
theorem MaximalBombieriVinogradov.tendsto_log_mul_sum_error_div
    (hBV : MaximalBombieriVinogradov) :
    Tendsto (fun X : ℕ => Real.log (2 * X + 2) * primaryProgressionError X / X)
      atTop (nhds 0) := by
  obtain ⟨B, _, K, hK, X₀, _, hdist⟩ := hBV 2 (by norm_num)
  have hinv : Tendsto (fun X : ℕ => (Real.log X)⁻¹) atTop (nhds 0) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have hu : Tendsto (fun X : ℕ => (2 * K) / Real.log X) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul (2 * K)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_ge_atTop 3] with X hX
    apply div_nonneg
    · apply mul_nonneg _ (primaryProgressionError_nonneg X)
      apply Real.log_nonneg
      have hx := Nat.cast_nonneg (α := ℝ) X
      linarith
    · exact Nat.cast_nonneg X
  · filter_upwards [eventually_primaryCutoff_sq_le_BV_range B,
        eventually_ge_atTop X₀, eventually_ge_atTop 3] with X hQ hX₀ hX3
    have hx : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    have hlog : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    have hS : primaryProgressionError X ≤ K * X / (Real.log X) ^ 2 := by
      simpa only [primaryProgressionError, Real.rpow_two] using
        hdist X hX₀ (primaryCutoff X ^ 2) hQ
    calc
      _ ≤ (2 * Real.log X) * (K * X / (Real.log X) ^ 2) / X := by
        apply div_le_div_of_nonneg_right _ hx.le
        exact mul_le_mul (log_two_mul_add_two_le_two_log hX3) hS
          (primaryProgressionError_nonneg X) (by positivity)
      _ = _ := by field_simp

end TwinPrime.Analytic
