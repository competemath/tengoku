module

public import Tengoku.AtPalomar.Paper.Hyperbolic
public import Tengoku.AtPalomar.Paper.Semigroup
public import Tengoku.AtPalomar.Paper.SymmetrizedWeight
public import Tengoku.AtPalomar.Paper.DoobHeat
public import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# The actual radial weight in the heat-contraction estimate

This file checks every analytic hypothesis of the Gaussian-kernel contraction
for the paper's `sech³` and its symmetrized Gaussian/cosh weight, with the
positive scalar normalization removed. In particular integrability is proved,
not supplied as an assumption.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Paper

theorem sech_cube_bound (x : ℝ) : ‖sech x ^ 3‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (pow_nonneg (sech_pos x).le 3)]
  simpa using pow_le_pow_left₀ (sech_pos x).le (sech_le_one x) 3

/-- The tilt/cosh ratio is at most one in the parameter region used in the paper.-/
theorem radialWeight_le_gaussian {v c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (x : ℝ) :
    radialWeight v c x ≤ Real.exp (-x ^ 2 / (2 * v)) := by
  have hc : Real.cosh (c * x) ≤ Real.cosh x := by
    rw [Real.cosh_le_cosh, abs_mul, abs_of_nonneg hc0]
    nlinarith [abs_nonneg x]
  unfold radialWeight
  rw [div_le_iff₀ (Real.cosh_pos x)]
  exact mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le

/-- Symmetrization against an even test function preserves the Gaussian/cosh
pairing. Its only analytic hypothesis is integrability of that pairing.-/
theorem integral_gaussian_cosh_even_symmetrization (h : ℝ) (v : ℝ≥0)
    (f : ℝ → ℝ) (hf_even : ∀ x, f (-x) = f x)
    (hf : Integrable (fun x => ProbabilityTheory.gaussianPDFReal h v x / Real.cosh x * f x)) :
    (∫ x, ProbabilityTheory.gaussianPDFReal h v x / Real.cosh x * f x) =
      ∫ x, symmetrizedWeight h v x * f x := by
  have href : Integrable
      (fun x => ProbabilityTheory.gaussianPDFReal h v (-x) / Real.cosh x * f x) := by
    simpa only [Real.cosh_neg, hf_even] using hf.comp_neg
  have hreflect :
      (∫ x, ProbabilityTheory.gaussianPDFReal h v (-x) / Real.cosh x * f x) =
        ∫ x, ProbabilityTheory.gaussianPDFReal h v x / Real.cosh x * f x := by
    simpa only [Real.cosh_neg, hf_even] using
      integral_neg_eq_self (fun x => ProbabilityTheory.gaussianPDFReal h v x / Real.cosh x * f x) volume
  have heq : (fun x => symmetrizedWeight h v x * f x) =
      (fun x => (ProbabilityTheory.gaussianPDFReal h v x / Real.cosh x * f x +
        ProbabilityTheory.gaussianPDFReal h v (-x) / Real.cosh x * f x) / 2) := by
    ext x
    unfold symmetrizedWeight
    ring
  rw [heq, integral_div, integral_add hf href, hreflect]
  ring

end Paper
