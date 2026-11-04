module

public import Tengoku.AtPalomar.Paper.Gaussian
public import Tengoku.Seed.MeasureTheory.Integral.IntegralEqImproper

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Gaussian integration by parts

The standard Gaussian Stein identity is derived from the derivative of its
actual probability density and whole-line integration by parts. The bounded
version discharges weighted integrability. Boundary terms are discharged by
Mathlib's whole-line theorem for integrable products; no limiting boundary
identity is assumed.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

/-- The first absolute Gaussian moment has an integrable density on `ℝ`.-/
theorem integrable_mul_standardGaussianPDF :
    Integrable (fun x : ℝ => x * gaussianPDFReal 0 1 x) := by
  have hi := (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹)
  convert hi using 1
  funext x
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  rw [show -(1 / 2 : ℝ) * x ^ 2 = -(x ^ 2) / 2 by ring]
  ring

end Paper
