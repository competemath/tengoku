import Tengoku.SingularityCompleteLean.Singularity.ConjugateSubgroup
import Tengoku.SingularityCompleteLean.Singularity.BoundaryMeasureClasses

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Singularity under a change of hyperbolic coordinates

The compact boundary action is a measurable embedding, and visual measures
transform covariantly. Thus conjugating coordinates preserves and reflects the
singularity conclusion, including any atoms at infinity.
-/

noncomputable section
open MeasureTheory OnePoint
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

/-- Every real projective SL action is a measurable embedding on the compact boundary.
@isnad1 id=measurab.0h1v.s7.bc36ec03279b from=translated src=- shape=9ad1d871 vocab=94915752
-/
theorem measurableEmbedding_compactBoundary_smul (B : SL(2, ℝ)) :
    MeasurableEmbedding (fun p : OnePoint ℝ => B • p) :=
  ((continuous_const_smul B).isClosedEmbedding (MulAction.injective B)).measurableEmbedding

/-- The visual-singularity conclusion is invariant under a hyperbolic change of coordinates.
@isnad1 id=iff.0h3v.s8.787d735540dc from=translated src=- shape=d9371fb6 vocab=bba804e5
-/
theorem compactBoundary_visual_singularity_conjugacy (B : SL(2, ℝ))
    (ν : Measure (OnePoint ℝ)) (z : ℍ) :
    Measure.map (fun p : OnePoint ℝ => B • p) ν ⟂ₘ compactPoissonMeasure (B • z) ↔
      ν ⟂ₘ compactPoissonMeasure z := by
  rw [← compactPoissonMeasure_covariance]
  exact mutuallySingular_map_iff_of_embedding _ (measurableEmbedding_compactBoundary_smul B) _ _

end Singularity
