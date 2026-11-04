module

public import Tengoku.AtPalomar.Paper.Hyperbolic
public import Tengoku.Seed.Probability.Distributions.Gaussian.Real
public import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# The symmetrized Gaussian weight in Proposition 5.5

The formula in the paper is proved for the actual Gaussian density, and
relates its symmetrized weight to the radial function analyzed in
`Paper.Hyperbolic`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

/-- The exact weight obtained by symmetrizing the Gaussian density.-/
def symmetrizedWeight (h : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  (gaussianPDFReal h v x + gaussianPDFReal h v (-x)) / (2 * Real.cosh x)

/-- Factoring the Gaussian density gives the radial formula in the paper.-/
theorem symmetrizedWeight_eq_radialWeight (h : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    symmetrizedWeight h v x =
      gaussianPDFReal h v 0 * radialWeight (v : ℝ) (h / (v : ℝ)) x := by
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hp : -(x - h) ^ 2 / (2 * (v : ℝ)) =
      -h ^ 2 / (2 * (v : ℝ)) + (-x ^ 2 / (2 * (v : ℝ)) + h / (v : ℝ) * x) := by
    field_simp
    ring
  have hn : -(-x - h) ^ 2 / (2 * (v : ℝ)) =
      -h ^ 2 / (2 * (v : ℝ)) + (-x ^ 2 / (2 * (v : ℝ)) - h / (v : ℝ) * x) := by
    field_simp
    ring
  unfold symmetrizedWeight radialWeight gaussianPDFReal
  simp only [zero_sub, neg_sq]
  rw [hp, hn, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_sub, Real.cosh_eq (h / (v : ℝ) * x)]
  rw [Real.exp_neg]
  field_simp

/-- The symmetrized density weight is even.-/
@[simp] theorem symmetrizedWeight_neg (h : ℝ) (v : ℝ≥0) (x : ℝ) :
    symmetrizedWeight h v (-x) = symmetrizedWeight h v x := by
  simp [symmetrizedWeight, add_comm]

/-- Nonnegativity of the actual symmetrized Gaussian weight.-/
theorem symmetrizedWeight_nonneg (h : ℝ) (v : ℝ≥0) (x : ℝ) :
    0 ≤ symmetrizedWeight h v x := by
  unfold symmetrizedWeight
  exact div_nonneg
    (add_nonneg (gaussianPDFReal_nonneg h v x) (gaussianPDFReal_nonneg h v (-x)))
    (mul_nonneg (by norm_num) (Real.cosh_pos x).le)

end Paper
