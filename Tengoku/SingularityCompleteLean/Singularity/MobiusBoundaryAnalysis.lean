import Tengoku.SingularityCompleteLean.Singularity.PoissonDomination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Boundary analysis from a single bounded measure and Möbius translates

A bound by B times one Poisson measure supplies all bounds for the finitely
many translated base measures. Thus the bounded analysis family needs no
independent Poisson-bound hypotheses at the orbit representatives.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal MatrixGroups UpperHalfPlane

namespace Singularity

variable {J : Type*} [Fintype J] (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
  {τ : ℝ} (hτ : 0 < τ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
  (z : ℍ) (B : ℝ) (hB : 0 ≤ B)
  (hbound : ν ≤ ENNReal.ofReal B • poissonBoundaryMeasure z) (g : J → SL(2, ℝ))

end Singularity
