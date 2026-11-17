import Tengoku.SingularityCompleteLean.Singularity.CompactBoundaryEscape
import Tengoku.SingularityCompleteLean.Singularity.WalkLimitConstruction
import Tengoku.SingularityCompleteLean.Singularity.ReflectedSupport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Conditional construction of the geometric hitting law

All topology, measurability, actions and boundary-support conclusions now refer
to the actual compact sphere and its real projective boundary. The remaining
probabilistic input is existence of almost-sure limits of orbit positions.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Topology Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- Countability supplies joint measurability for the genuine restricted sphere action.-/
theorem measurable_compactSubgroupAction (Γ : Subgroup SL(2, ℝ))
    [Countable Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ] :
    Measurable (fun p : Γ × OnePoint ℂ => p.1 • p.2) :=
  measurable_from_prod_countable_right (fun g => (continuous_const_smul g).measurable)

/-- The orbit map into the sphere is genuinely equivariant.-/
theorem compactOrbit_equivariant (Γ : Subgroup SL(2, ℝ)) (z : ℍ) (g h : Γ) :
    hyperbolicCompactEmbedding ((g * h) • z) = g • hyperbolicCompactEmbedding (h • z) := by
  rw [mul_smul]
  exact hyperbolicCompactEmbedding_smul (g : SL(2, ℝ)) (h • z)

end Singularity
