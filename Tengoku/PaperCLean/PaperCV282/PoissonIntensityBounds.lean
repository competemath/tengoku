import Tengoku.PaperCLean.PaperCV282.ScalarSteinInput

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Intensity factors with the actual zero-rate convention

These are numerical inequalities for the two proved Stein bounds. No
probabilistic input or restriction to a critical-intensity window is used.
The retained mean comparison assumes half of the full mean is retained;
it is not asserted for arbitrary sparse masks without that hypothesis.
-/

namespace PaperC.V282.PoissonIntensityBounds

open ScalarSteinInput
open scoped NNReal

noncomputable section

/--
@isnad1 id=eq.1h1v.s5.51dee3c82045 from=translated src=- shape=22339b22 vocab=973fdb76
-/
theorem firstSteinFactor_eq_min_inv {rate : ℝ≥0} (hrate : 0 < rate) :
    firstSteinFactor rate = min 1 (rate : ℝ)⁻¹ := by
  simp [firstSteinFactor, ne_of_gt hrate]

/--
@isnad1 id=eq.1h1v.s5.6b9d3520b354 from=translated src=- shape=35db0b71 vocab=0718b775
-/
theorem zeroSteinFactor_eq_min_inv_sqrt {rate : ℝ≥0} (hrate : 0 < rate) :
    zeroSteinFactor rate = min 1 (Real.sqrt (rate : ℝ))⁻¹ := by
  simp [zeroSteinFactor, ne_of_gt hrate]

/--
@isnad1 id=le.1h1v.s4.e27b492adfce from=translated src=- shape=bea17b5e vocab=44bf578b
-/
theorem firstSteinFactor_le_inv {rate : ℝ≥0} (hrate : 0 < rate) :
    firstSteinFactor rate ≤ (rate : ℝ)⁻¹ := by
  rw [firstSteinFactor_eq_min_inv hrate]
  exact min_le_right _ _

/--
@isnad1 id=eq.1h1v.s4.09f0c9340c94 from=translated src=- shape=8acc91d3 vocab=8602552b
-/
theorem firstSteinFactor_eq_one_of_le_one {rate : ℝ≥0} (hrate : (rate : ℝ) ≤ 1) :
    firstSteinFactor rate = 1 := by
  by_cases hz : rate = 0
  · simp [hz, firstSteinFactor]
  · have hp : (0 : ℝ) < rate := by exact_mod_cast (pos_iff_ne_zero.mpr hz)
    rw [firstSteinFactor, ite_eq_right hz, min_eq_left]
    exact (one_le_inv₀ hp).mpr hrate

/--
@isnad1 id=eq.1h1v.s4.fc74719afb14 from=translated src=- shape=4a0c1c60 vocab=64a7ad78
-/
theorem firstSteinFactor_eq_inv_of_one_le {rate : ℝ≥0} (hrate : 1 ≤ (rate : ℝ)) :
    firstSteinFactor rate = (rate : ℝ)⁻¹ := by
  have hp : (0 : ℝ) < rate := by linarith
  rw [firstSteinFactor_eq_min_inv (by exact_mod_cast hp), min_eq_right]
  exact (inv_le_one₀ hp).mpr hrate

/--
@isnad1 id=le.1h2v.s5.9f24fb9ae781 from=translated src=- shape=38ca2eb2 vocab=fc4ff693
-/
theorem firstSteinFactor_le_twice_of_half_le {mu lambda : ℝ≥0}
    (hhalf : (lambda : ℝ) / 2 ≤ (mu : ℝ)) :
    firstSteinFactor mu ≤ 2 * firstSteinFactor lambda := by
  by_cases hsmall : (lambda : ℝ) ≤ 1
  · rw [firstSteinFactor_eq_one_of_le_one hsmall]
    linarith [firstSteinFactor_le_one mu]
  · have hlambda : (0 : ℝ) < lambda := by linarith
    have hmu : (0 : ℝ) < mu := by linarith
    rw [firstSteinFactor_eq_inv_of_one_le (rate := lambda) (by linarith)]
    calc
      firstSteinFactor mu ≤ (mu : ℝ)⁻¹ := firstSteinFactor_le_inv (by exact_mod_cast hmu)
      _ ≤ ((lambda : ℝ) / 2)⁻¹ := inv_anti₀ (by positivity : (0 : ℝ) < (lambda : ℝ) / 2) hhalf
      _ = 2 * (lambda : ℝ)⁻¹ := by simp [div_eq_mul_inv]

/--
@isnad1 id=le.2h2v.s6.0ef3f6f04427 from=translated src=- shape=f335cba9 vocab=61f72345
-/
theorem firstSteinFactor_le_twice_min_inv_of_half_le {mu lambda : ℝ≥0}
    (hlambda : 0 < lambda) (hhalf : (lambda : ℝ) / 2 ≤ (mu : ℝ)) :
    firstSteinFactor mu ≤ 2 * min 1 (lambda : ℝ)⁻¹ := by
  simpa only [firstSteinFactor_eq_min_inv hlambda] using
    firstSteinFactor_le_twice_of_half_le hhalf

/--
@isnad1 id=le.0h1v.s4.ace35f2f8302 from=translated src=- shape=62cde15b vocab=fe08e6cf
-/
theorem firstSteinFactor_mul_le_one (rate : ℝ≥0) :
    firstSteinFactor rate * (rate : ℝ) ≤ 1 := by
  by_cases hz : rate = 0
  · simp [hz]
  · have hp : (0 : ℝ) < rate := by exact_mod_cast (pos_iff_ne_zero.mpr hz)
    calc
      _ ≤ (rate : ℝ)⁻¹ * (rate : ℝ) :=
        mul_le_mul_of_nonneg_right (firstSteinFactor_le_inv (by exact_mod_cast hp)) rate.coe_nonneg
      _ = 1 := inv_mul_cancel₀ hp.ne'

/--
@isnad1 id=le.0h1v.s4.56d33334ac4f from=translated src=- shape=93a81373 vocab=fe08e6cf
-/
theorem firstSteinFactor_mul_le_self (rate : ℝ≥0) :
    firstSteinFactor rate * (rate : ℝ) ≤ (rate : ℝ) := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (firstSteinFactor_le_one rate) rate.coe_nonneg

/--
@isnad1 id=le.0h1v.s5.a2c901bb9ada from=translated src=- shape=2afe014e vocab=f659bd74
-/
theorem firstSteinFactor_mul_square_le (rate : ℝ≥0) :
    firstSteinFactor rate * (rate : ℝ) ^ 2 ≤ (rate : ℝ) := by
  have h := mul_le_mul_of_nonneg_right (firstSteinFactor_mul_le_one rate) rate.coe_nonneg
  nlinarith

/--
@isnad1 id=le.0h1v.s5.f007c75776c8 from=translated src=- shape=760bfc02 vocab=3f897304
-/
theorem firstSteinFactor_mul_square_add_le_twice (rate : ℝ≥0) :
    firstSteinFactor rate * ((rate : ℝ) ^ 2 + (rate : ℝ)) ≤ 2 * (rate : ℝ) := by
  nlinarith [firstSteinFactor_mul_square_le rate, firstSteinFactor_mul_le_self rate]

/--
@isnad1 id=le.0h1v.s5.689257d2eb0a from=translated src=- shape=2e1aa7f5 vocab=3f897304
-/
theorem firstSteinFactor_mul_square_add_le_add_one (rate : ℝ≥0) :
    firstSteinFactor rate * ((rate : ℝ) ^ 2 + (rate : ℝ)) ≤ (rate : ℝ) + 1 := by
  nlinarith [firstSteinFactor_mul_square_le rate, firstSteinFactor_mul_le_one rate]

/--
@isnad1 id=le.0h1v.s6.8735729949c7 from=translated src=- shape=a10094e4 vocab=3f897304
-/
theorem firstSteinFactor_mul_square_add_twice_le (rate : ℝ≥0) :
    firstSteinFactor rate * ((rate : ℝ) ^ 2 + 2 * (rate : ℝ)) ≤ (rate : ℝ) + 2 := by
  nlinarith [firstSteinFactor_mul_square_le rate, firstSteinFactor_mul_le_one rate]

/--
@isnad1 id=le.0h1v.s6.526a8e550b0f from=translated src=- shape=17b85b14 vocab=3f897304
-/
theorem firstSteinFactor_mul_square_add_twice_le_three_mul (rate : ℝ≥0) :
    firstSteinFactor rate * ((rate : ℝ) ^ 2 + 2 * (rate : ℝ)) ≤ 3 * (rate : ℝ) := by
  nlinarith [firstSteinFactor_mul_square_le rate, firstSteinFactor_mul_le_self rate]

/--
@isnad1 id=le.1h1v.s6.7e6201d00888 from=translated src=- shape=48ddb0e0 vocab=d94f55e3
-/
theorem min_inv_mul_square_add_le {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    min 1 lambda⁻¹ * (lambda ^ 2 + lambda) ≤ 2 * lambda := by
  by_cases hz : lambda = 0
  · simp [hz]
  · have hp : 0 < lambda := lt_of_le_of_ne hlambda (Ne.symm hz)
    let rate : ℝ≥0 := ⟨lambda, hlambda⟩
    have hrate : 0 < rate := by exact_mod_cast hp
    have h := firstSteinFactor_mul_square_add_le_twice rate
    change firstSteinFactor rate * (lambda ^ 2 + lambda) ≤ 2 * lambda at h
    rw [firstSteinFactor_eq_min_inv hrate] at h
    exact h

/--
@isnad1 id=le.0h1v.s4.8dd90f00afe6 from=translated src=- shape=93a81373 vocab=d708e710
-/
theorem zeroSteinFactor_mul_le_self (rate : ℝ≥0) :
    zeroSteinFactor rate * (rate : ℝ) ≤ (rate : ℝ) := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (zeroSteinFactor_le_one rate) rate.coe_nonneg

/--
@isnad1 id=le.0h1v.s4.b38ec1ffbc8f from=translated src=- shape=4c9694e2 vocab=694d152a
-/
theorem zeroSteinFactor_mul_le_sqrt (rate : ℝ≥0) :
    zeroSteinFactor rate * (rate : ℝ) ≤ Real.sqrt (rate : ℝ) := by
  by_cases hz : rate = 0
  · simp [hz]
  · have hp : (0 : ℝ) < rate := by exact_mod_cast (pos_iff_ne_zero.mpr hz)
    have hs : 0 < Real.sqrt (rate : ℝ) := Real.sqrt_pos.mpr hp
    rw [zeroSteinFactor_eq_min_inv_sqrt (by exact_mod_cast hp)]
    calc
      _ ≤ (Real.sqrt (rate : ℝ))⁻¹ * (rate : ℝ) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) rate.coe_nonneg
      _ = Real.sqrt (rate : ℝ) := by
        apply (mul_left_cancel₀ hs.ne')
        rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
        nlinarith [Real.sq_sqrt rate.coe_nonneg]

/--
@isnad1 id=le.0h1v.s5.55386aea00f2 from=translated src=- shape=479bfafc vocab=abc11441
-/
theorem firstSteinFactor_mul_square_le_max_one (rate : ℝ≥0) :
    firstSteinFactor rate * (rate : ℝ) ^ 2 ≤ max 1 (rate : ℝ) :=
  (firstSteinFactor_mul_square_le rate).trans (le_max_right _ _)

/--
@isnad1 id=le.0h1v.s4.51df20be4ff4 from=translated src=- shape=1ddb7a56 vocab=9c9162d1
-/
theorem zeroSteinFactor_mul_le_sqrt_max_one (rate : ℝ≥0) :
    zeroSteinFactor rate * (rate : ℝ) ≤ Real.sqrt (max 1 (rate : ℝ)) :=
  (zeroSteinFactor_mul_le_sqrt rate).trans (Real.sqrt_le_sqrt (le_max_right _ _))

end

end PaperC.V282.PoissonIntensityBounds
