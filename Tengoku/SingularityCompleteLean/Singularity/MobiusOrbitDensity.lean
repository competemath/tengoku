import Tengoku.SingularityCompleteLean.Singularity.DilationOrbit
import Tengoku.SingularityCompleteLean.Singularity.DensityVector

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Identification of the lattice densities with actual matrix-orbit measures

The row at (n,j) is a logarithmic density for (a^n b_j)_*ν, where a is the
explicit diagonal dilation matrix. The identification is independent of
representatives and holds simultaneously for all rows on a common full-measure
set, supplying the actual ℓ² density columns used in the pairing argument.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal MatrixGroups UpperHalfPlane

namespace Singularity

variable {J : Type*} [Fintype J] (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
  {τ : ℝ} (hτ : 0 < τ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
  (z : ℍ) (B : ℝ) (hB : 0 ≤ B)
  (hbound : ν ≤ ENNReal.ofReal B • poissonBoundaryMeasure z) (b : J → SL(2, ℝ))
  (q : ℤ → J → ℝ → ℝ) (hq : ∀ n j, Measurable (q n j)) (hpq : ∀ n j u, 0 ≤ q n j u)
  (hmeasure : ∀ n j, volume.withDensity (fun u => ENNReal.ofReal (q n j u)) =
    Measure.map (realBoundaryMobius (dilationMatrix τ ^ n * b j)) ν)

include hq hpq hmeasure

end Singularity
