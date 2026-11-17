import Tengoku.SingularityCompleteLean.Singularity.CocompactGlobalHarnack
import Tengoku.SingularityCompleteLean.Singularity.GreenProductBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Green comparison through a hyperbolic ball

The entrance part is controlled by a product through the center with a cost
at most exponential in the ball radius. The killed Green kernel is the exact
additive error, so no avoidance probability or boundary limit is assumed.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- A bounded open ball contains only finitely many group vertices, with all
stabilizer multiplicities retained.-/
theorem finite_hyperbolic_orbit_openBall (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    (u : Γ) (R : ℝ) :
    {g : Γ | dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R}.Finite := by
  apply (finite_group_vertices_in_compact Γ UpperHalfPlane.I
    (isCompact_closedBall (u • UpperHalfPlane.I) R)).subset
  intro g hg
  change dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R at hg
  exact hg.le

end Singularity
