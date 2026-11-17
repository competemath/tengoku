import Tengoku.SingularityCompleteLean.Singularity.MartinAction
import Tengoku.SingularityCompleteLean.Singularity.WeightedCurrent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Conditional invariant currents on the actual Martin boundaries

Finite generation makes the boundary action Borel measurable. If measures on the
forward and reflected boundaries have the stated pushforward densities, and a
measurable real kernel has the Naïm covariance law, its nonnegative part weights
an invariant product measure. The derivative and full-kernel hypotheses are
explicit: this file does not construct hitting measures or prove those hypotheses.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ a ∈ s, 0 < μ a)
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

/-- The constructed Martin-boundary homeomorphism is a Borel equivalence.-/
def martinBoundaryMeasurableEquiv (o g : Γ) :
    martinBoundary s μ o ≃ᵐ martinBoundary s μ o := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  exact (martinBoundaryHomeomorph s μ hpos hgen hgap o g).toMeasurableEquiv

omit [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] in
include hgen in
/-- The actual normalization cocycle is measurable on the boundary.
@isnad1 id=measurab.1h5v.s6.ded20d43cc02 from=translated src=- shape=9fcbd410 vocab=10fdd721
-/
theorem measurable_martinBoundaryCocycle (o g : Γ) :
    Measurable (martinBoundaryCocycle s μ o g) := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  exact (continuous_martinBoundaryCocycle s μ o g).measurable

end Singularity
