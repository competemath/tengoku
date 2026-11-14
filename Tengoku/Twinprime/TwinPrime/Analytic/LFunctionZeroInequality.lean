import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionLocalExpansion
import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionZeroSigns

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!

# One-sided local L-function logarithmic-derivative bounds

The proved expansion over the actual divisor combines with the sign of
each zero contribution to give an upper bound for the negative logarithmic
derivative. A selected actual zero contributes its reciprocal explicitly.
-/

noncomputable section

open Metric

namespace TwinPrime.Analytic

def primitiveLFunctionLogBudget (q : ℕ) (t : ℝ) : ℝ :=
  (144 * (1 + Real.log 5 / Real.log (6 / 5))) *
    (1 + Real.log 16 + 2 * Real.log q + Real.log (‖(2 : ℂ) + Complex.I * t‖ + 2))

/--
@isnad1 id=le.0h2v.s4.9fbf087b7b14 from=translated src=- shape=787c1379 vocab=5cfd426d
-/
theorem primitiveLFunctionLogBudget_nonneg (q : ℕ) (t : ℝ) :
    0 ≤ primitiveLFunctionLogBudget q t := by
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have h65 : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  have h16 : 0 ≤ Real.log (16 : ℝ) := Real.log_nonneg (by norm_num)
  have hq := Real.log_natCast_nonneg q
  have hH : 0 ≤ Real.log (‖(2 : ℂ) + Complex.I * t‖ + 2) :=
    Real.log_nonneg (by have := norm_nonneg ((2 : ℂ) + Complex.I * t); linarith)
  unfold primitiveLFunctionLogBudget
  positivity

/--
@isnad1 id=le.2h3v.s4.33b61a4a5f73 from=translated src=- shape=5f95ae82 vocab=5cfd426d
-/
theorem primitiveLFunctionLogBudget_mono_conductor (d q : ℕ)
    (hd : 1 ≤ d) (hdq : d ≤ q) (t : ℝ) :
    primitiveLFunctionLogBudget d t ≤ primitiveLFunctionLogBudget q t := by
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have h65 : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  have hl : Real.log (d : ℝ) ≤ Real.log q :=
    Real.log_le_log (by exact_mod_cast (show 0 < d by omega)) (by exact_mod_cast hdq)
  unfold primitiveLFunctionLogBudget
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

/-- The stated real range lies in the closed unit disk about `2+it`.
@isnad1 id=mem.2h2v.s6.2620c5a3f0cf from=translated src=- shape=ba8f537b vocab=54afdfef
-/
theorem sigma_add_I_mul_mem_local_disk (σ t : ℝ) (hσ : 1 < σ) (hσu : σ ≤ 9 / 8) :
    (σ : ℂ) + Complex.I * t ∈ closedBall ((2 : ℂ) + Complex.I * t) 1 := by
  have heq : (σ : ℂ) + Complex.I * t - ((2 : ℂ) + Complex.I * t) =
      ((σ - 2 : ℝ) : ℂ) := by push_cast; ring
  rw [mem_closedBall_iff_norm, heq, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end TwinPrime.Analytic
