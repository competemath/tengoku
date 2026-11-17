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

/-- Countability supplies joint measurability for the genuine restricted sphere action.
@isnad1 id=measurab.0h1v.s11.2cc80f2d9c10 from=translated src=- shape=36e53fc2 vocab=bb7e935f
-/
theorem measurable_compactSubgroupAction (Γ : Subgroup SL(2, ℝ))
    [Countable Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ] :
    Measurable (fun p : Γ × OnePoint ℂ => p.1 • p.2) :=
  measurable_from_prod_countable_right (fun g => (continuous_const_smul g).measurable)

/-- The orbit map into the sphere is genuinely equivariant.
@isnad1 id=eq.0h4v.s12.2d67c638191a from=translated src=- shape=0fdc29be vocab=a554488b
-/
theorem compactOrbit_equivariant (Γ : Subgroup SL(2, ℝ)) (z : ℍ) (g h : Γ) :
    hyperbolicCompactEmbedding ((g * h) • z) = g • hyperbolicCompactEmbedding (h • z) := by
  rw [mul_smul]
  exact hyperbolicCompactEmbedding_smul (g : SL(2, ℝ)) (h • z)

end Singularity
