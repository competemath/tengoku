import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionZeroValue
import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionNearOneGrowth
import Tengoku.Twinprime.TwinPrime.Analytic.ZeroFreeLogarithms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Logarithmic-square zero-to-value bound

The actual conductor truncation and real-segment estimate give a zero-distance
bound in terms of the actual value at one. A uniform lower bound for that value
is the separate Siegel input proved in `SiegelValue`.
-/

noncomputable section

namespace TwinPrime.Analytic

/--
@isnad1 id=le.1h2v.s5.d159abefef82 from=translated src=- shape=3dffdaab vocab=8798bc40
-/
theorem primitiveLogZeroFreeWidth_le_one_div_log {q : ℕ}
    (hq : 1 < q) (t : ℝ) :
    primitiveLogZeroFreeWidth q t ≤ 1 / Real.log q := by
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  have hH : 0 ≤ Real.log (|t| + 4) := Real.log_nonneg (by have := abs_nonneg t; linarith)
  have hC := zeroFreeLogConstant_ge
  unfold primitiveLogZeroFreeWidth
  apply one_div_le_one_div_of_le hlog
  nlinarith [mul_nonneg (by linarith : 0 ≤ zeroFreeLogConstant)
    (by linarith : 0 ≤ 1 + Real.log (q : ℝ) + Real.log (|t| + 4))]

/-- The actual value at one is bounded by the distance to any nearby real zero,
with only a logarithmic-square loss.
@isnad1 id=le.4h3v.s7.661aebbff077 from=translated src=- shape=7b155ce1 vocab=140de6a9
-/
theorem norm_LFunction_one_le_log_sq_gap {q : ℕ} [NeZero q]
    (hq : 256 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (β : ℝ) (hβ : 1 - 1 / Real.log q ≤ β)
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    ‖DirichletCharacter.LFunction χ 1‖ ≤
      (10 * Real.exp 2 * (Real.log q) ^ 2) * (1 - β) := by
  have hq1 : 1 < q := by omega
  have hβ1 : β ≤ 1 := by
    have h := primitiveLFunction_zero_re_lt_one hq1 χ hχ (β : ℂ) hzero
    simpa only [Complex.ofReal_re] using h.le
  apply norm_LFunction_one_le_gap_of_deriv_bound χ (primitive_character_ne_one hq1 χ hχ)
    β _ hβ1 hzero
  intro u hu
  exact norm_deriv_LFunction_near_one_le hq χ hχ u (hβ.trans hu.1) hu.2

/--
@isnad1 id=le.4h3v.s7.842c083c3086 from=translated src=- shape=8f8dcf71 vocab=140de6a9
-/
theorem real_zero_gap_ge_LFunction_one_div_log_sq {q : ℕ} [NeZero q]
    (hq : 256 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (β : ℝ) (hβ : 1 - 1 / Real.log q ≤ β)
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    ‖DirichletCharacter.LFunction χ 1‖ /
      (10 * Real.exp 2 * (Real.log q) ^ 2) ≤ 1 - β := by
  have hlog : 0 < Real.log (q : ℝ) := by
    linarith [one_le_log_of_256_le q hq]
  apply (div_le_iff₀ (by positivity : 0 < 10 * Real.exp 2 * (Real.log (q : ℝ)) ^ 2)).mpr
  simpa only [mul_comm] using norm_LFunction_one_le_log_sq_gap hq χ hχ β hβ hzero

end TwinPrime.Analytic
