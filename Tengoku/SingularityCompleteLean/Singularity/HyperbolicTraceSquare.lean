import Tengoku.SingularityCompleteLean.Singularity.HyperbolicTraceNormalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Negative traces and positive dilation normalization

For determinant-one two-by-two matrices, tr(g²) = tr(g)² - 2. Squaring a
hyperbolic element therefore gives trace > 2 regardless of its original sign.
-/

noncomputable section
open scoped MatrixGroups

namespace Singularity

/-- The two-by-two trace identity for a square in SL(2,ℝ).
@isnad1 id=eq.0h1v.s9.e59263b75954 from=translated src=- shape=51866096 vocab=4bf5886e
-/
theorem slTwo_trace_square (g : SL(2, ℝ)) :
    (g ^ 2) 0 0 + (g ^ 2) 1 1 = (g 0 0 + g 1 1) ^ 2 - 2 := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  simp only [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  nlinarith

/-- Either sign of hyperbolic trace gives a square of trace greater than two.
@isnad1 id=lt.1h1v.s9.9c1139a86f1f from=translated src=- shape=8824d8dc vocab=3f70b56b
-/
theorem slTwo_trace_square_gt_two (g : SL(2, ℝ)) (hg : 2 < |g 0 0 + g 1 1|) :
    2 < (g ^ 2) 0 0 + (g ^ 2) 1 1 := by
  rw [slTwo_trace_square]
  have hs := sq_abs (g 0 0 + g 1 1)
  nlinarith

/-- The square of every real hyperbolic matrix is conjugate to a positive dilation.
@isnad1 id=ex.1h1v.s9.d27c1d8e12e1 from=translated src=- shape=7900bdf2 vocab=15fe9b4f
-/
theorem exists_dilation_conjugacy_of_abs_trace (g : SL(2, ℝ))
    (hg : 2 < |g 0 0 + g 1 1|) :
    ∃ t : ℝ, 0 < t ∧ ∃ B : SL(2, ℝ), g ^ 2 = B * dilationMatrix t * B⁻¹ :=
  exists_dilation_conjugacy_of_trace_gt_two (g ^ 2) (slTwo_trace_square_gt_two g hg)

end Singularity
