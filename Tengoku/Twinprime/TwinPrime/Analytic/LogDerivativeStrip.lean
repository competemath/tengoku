import Tengoku.Twinprime.TwinPrime.Analytic.WideLFunctionLocalExpansion
import Tengoku.Twinprime.TwinPrime.Analytic.WideZetaLocalExpansion
import Tengoku.Twinprime.TwinPrime.Analytic.ZeroSumNorm
import Tengoku.Twinprime.TwinPrime.Analytic.ZeroFreeRectangle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Complex norm bounds in zero-free strips

The widened local expansion reaches left of one. A rectangle that extends
two height units and twice the evaluation width separates every actual
local zero. Jensen's multiplicity count then bounds the full complex
logarithmic derivative, not only its real part.
-/

noncomputable section

open Metric MeromorphicOn

namespace TwinPrime.Analytic

def primitiveStripLogDerivativeBudget (q : ℕ) (H δ : ℝ) : ℝ :=
  (288 * (1 + Real.log 5 / Real.log (6 / 5))) *
      (1 + Real.log 16 + 2 * Real.log q + Real.log (H + 4)) +
    ((Real.log 16 + 2 * Real.log q + Real.log (H + 4)) / Real.log (6 / 5)) / δ

def zetaStripLogDerivativeBudget (H δ : ℝ) : ℝ :=
  (288 * (1 + Real.log 5 / Real.log (6 / 5))) *
      (1 + Real.log 16 + 2 * Real.log (H + 4)) +
    ((Real.log 16 + 2 * Real.log (H + 4)) / Real.log (6 / 5)) / δ

/--
@isnad1 id=le.1h2v.s5.0e578be438d3 from=translated src=- shape=ca1a7c78 vocab=31682fdc
-/
theorem norm_two_add_I_im_le (H : ℝ) (s : ℂ) (hs : |s.im| ≤ H) :
    ‖(2 : ℂ) + Complex.I * s.im‖ ≤ H + 2 := by
  have h := norm_add_le (2 : ℂ) (Complex.I * s.im)
  norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
  linarith

/--
@isnad1 id=mem.3h2v.s7.43e186885f3f from=translated src=- shape=98a0b248 vocab=13e03f21
-/
theorem mem_wide_center_disk_of_re_bounds (s : ℂ) (δ : ℝ)
    (hδ : δ ≤ 1 / 16) (hs : 1 - δ ≤ s.re) (hs2 : s.re ≤ 2) :
    s ∈ closedBall ((2 : ℂ) + Complex.I * s.im) (17 / 16) := by
  have he : s - ((2 : ℂ) + Complex.I * s.im) = ((s.re - 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [mem_closedBall_iff_norm, he, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def zetaEvaluationWidth (H : ℝ) : ℝ :=
  min (1 / 16) (zetaLogZeroFreeWidth (H + 2) / 2)

/--
@isnad1 id=lt.0h1v.s3.3eccb04faf22 from=translated src=- shape=8a62b088 vocab=649a8e7e
-/
theorem zetaEvaluationWidth_pos (H : ℝ) : 0 < zetaEvaluationWidth H := by
  have hw := zetaLogZeroFreeWidth_pos (H + 2)
  unfold zetaEvaluationWidth
  positivity

end TwinPrime.Analytic
