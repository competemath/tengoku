import Tengoku.SingularityCompleteLean.Singularity.GeometricPathConvergence
import Tengoku.SingularityCompleteLean.Singularity.WeightedOccupation
import Tengoku.SingularityCompleteLean.Singularity.GreenPoissonBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Geometric convergence from a lower Green comparison

The spectral gap and a lower bound comparing the Green row with exponential
hyperbolic distance imply almost-sure summable radial decay. Thus the two-sided
Green comparison already used in the rigidity route supplies full geometric
convergence, without an additional convergence hypothesis. The comparison and
spectral gap themselves remain explicit hypotheses.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Topology Classical MatrixGroups UpperHalfPlane

namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableMul Γ]

omit [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ] in
/-- The lower half of the distance comparison controls the radial weight by a Green row.
@isnad1 id=le.2h5v.s11.0a0c8864216c from=translated src=- shape=c997da89 vocab=001e9090
-/
theorem radial_le_green_of_comparison (s : Finset Γ) (μ : Γ → ℝ)
    {C : ℝ} (hC : 0 < C) (hcmp : GreenDistanceComparison Γ s μ C) (g : Γ) :
    Real.exp (-dist (g • UpperHalfPlane.I) UpperHalfPlane.I) ≤ C * walkGreen s μ 1 g := by
  have h := mul_le_mul_of_nonneg_left (hcmp 1 g).1 hC.le
  simpa only [one_smul, ← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul,
    dist_comm UpperHalfPlane.I] using h

end Singularity
