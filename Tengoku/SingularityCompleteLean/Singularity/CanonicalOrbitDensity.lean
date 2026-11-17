import Tengoku.SingularityCompleteLean.Singularity.MobiusOrbitDensity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Canonical densities for all matrix orbit measures

A single initial Poisson bound gives a measurable nonnegative density for each
actual Möbius pushforward. On a diagonal cyclic orbit these yield the density
columns and the nonzero orthogonal vector from the lattice obstruction.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal MatrixGroups UpperHalfPlane

namespace Singularity

/-- A canonical everywhere bounded density for a Möbius pushforward.-/
def mobiusPushforwardDensity (ν : Measure ℝ) (z : ℍ) (B : ℝ) (g : SL(2, ℝ)) : ℝ → ℝ :=
  poissonCappedDensity (Measure.map (realBoundaryMobius g) ν) (g • z).re (g • z).im B

theorem measurable_mobiusPushforwardDensity (ν : Measure ℝ) (z : ℍ) (B : ℝ) (g : SL(2, ℝ)) :
    Measurable (mobiusPushforwardDensity ν z B g) := measurable_poissonCappedDensity _ _ _ _

theorem mobiusPushforwardDensity_nonneg (ν : Measure ℝ) (z : ℍ) {B : ℝ}
    (hB : 0 ≤ B) (g : SL(2, ℝ)) (u : ℝ) : 0 ≤ mobiusPushforwardDensity ν z B g u :=
  poissonCappedDensity_nonneg _ _ (g • z).im_pos hB u

variable {J : Type*} [Fintype J] (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
  {τ : ℝ} (hτ : 0 < τ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
  (z : ℍ) (B : ℝ) (hB : 0 ≤ B)
  (hbound : ν ≤ ENNReal.ofReal B • poissonBoundaryMeasure z) (b : J → SL(2, ℝ))

end Singularity
