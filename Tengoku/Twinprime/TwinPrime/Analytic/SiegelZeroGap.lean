import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionLogarithmicZeroValue
import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionFiniteConductors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Conditional conversion from values at one to exceptional-zero gaps

The value lower bound is an explicit hypothesis, not a theorem of this file.
The proved logarithmic-square derivative estimate and finite-conductor
nonvanishing constants convert that hypothesis to a uniform arbitrary-power
gap for actual zeros in the proved logarithmic region.
-/

noncomputable section

namespace TwinPrime.Analytic

/--
@isnad1 id=le.1h2v.s6.d2b43e88b81f from=translated src=- shape=e05eee1d vocab=af303085
-/
theorem log_natCast_sq_le_rpow_half (q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (Real.log q) ^ 2 ≤ 16 * (q : ℝ) ^ (ε / 2) / ε ^ 2 := by
  have h := Real.log_natCast_le_rpow_div q (show 0 < ε / 4 by positivity)
  have hsq := pow_le_pow_left₀ (Real.log_natCast_nonneg q) h 2
  apply hsq.trans_eq
  rw [div_pow]
  have hp : ((q : ℝ) ^ (ε / 4)) ^ 2 = (q : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg q)]
    congr 1
    ring
  rw [hp]
  field_simp
  ring

/-- The logarithmic-square cost consumes half of a chosen power saving.
@isnad1 id=le.3h3v.s7.cf1667fc0820 from=translated src=- shape=f1bb7f9a vocab=ac08dee7
-/
theorem power_gap_constant_le_div_log_sq {q : ℕ} (hq : 1 < q)
    (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    (c * ε ^ 2 / (160 * Real.exp 2)) * (q : ℝ) ^ (-ε) ≤
      (c * (q : ℝ) ^ (-(ε / 2))) / (10 * Real.exp 2 * (Real.log q) ^ 2) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  have hp0 : 0 < (q : ℝ) ^ (ε / 2) := Real.rpow_pos_of_pos hq0 _
  have hlarge : 0 < 10 * Real.exp 2 * (16 * (q : ℝ) ^ (ε / 2) / ε ^ 2) := by
    positivity
  have hpow : (q : ℝ) ^ (-ε) * (q : ℝ) ^ (ε / 2) =
      (q : ℝ) ^ (-(ε / 2)) := by
    rw [← Real.rpow_add hq0]
    congr 1
    ring
  calc
    _ = (c * (q : ℝ) ^ (-(ε / 2))) /
        (10 * Real.exp 2 * (16 * (q : ℝ) ^ (ε / 2) / ε ^ 2)) := by
      apply (eq_div_iff hlarge.ne').mpr
      calc
        _ = c * ((q : ℝ) ^ (-ε) * (q : ℝ) ^ (ε / 2)) := by
          field_simp
          ring
        _ = _ := by rw [hpow]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (log_natCast_sq_le_rpow_half q ε hε) (by positivity)

/-- Explicit large-conductor conversion for a supplied value lower bound.
@isnad1 id=le.7h5v.s8.38699b00e2de from=translated src=- shape=82028506 vocab=20c4ac3b
-/
theorem real_zero_power_gap_of_value_lower_bound {q : ℕ} [NeZero q]
    (hq : 256 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (c ε β : ℝ) (hc : 0 ≤ c) (hε : 0 < ε)
    (hvalue : c * (q : ℝ) ^ (-(ε / 2)) ≤ ‖DirichletCharacter.LFunction χ 1‖)
    (hβ : 1 - 1 / Real.log q ≤ β)
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    (c * ε ^ 2 / (160 * Real.exp 2)) * (q : ℝ) ^ (-ε) ≤ 1 - β := by
  apply (power_gap_constant_le_div_log_sq (by omega) c ε hc hε).trans
  apply (div_le_div_of_nonneg_right hvalue (by positivity)).trans
  exact real_zero_gap_ge_LFunction_one_div_log_sq hq χ hχ β hβ hzero

end TwinPrime.Analytic
