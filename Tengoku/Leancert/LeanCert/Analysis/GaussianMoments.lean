import Tengoku.Leancert.LeanCert.Analysis.PolynomialDecay
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Integrable polynomial-weighted Gaussian majorants on the positive half-line. -/
namespace LeanCert.Analysis
open MeasureTheory Set

theorem integrableOn_gaussian_moment (m : ℕ) :
    IntegrableOn (fun u : ℝ => u^m * Real.exp (-u^2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
    (show (-1 : ℝ) < (m : ℝ) by have := Nat.cast_nonneg (α := ℝ) m; linarith)
  simpa using h

end LeanCert.Analysis
