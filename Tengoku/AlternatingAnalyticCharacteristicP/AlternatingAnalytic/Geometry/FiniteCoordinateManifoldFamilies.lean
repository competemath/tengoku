import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.FiniteCoordinateFamilies
import Tengoku.Seed.Geometry.Manifold.ContMDiff.NormedSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The alternating action on analytic families over finite-coordinate manifolds

On an open subset of an analytic manifold whose model has continuous linear coordinates
`P ≃L[K] K^d`, the model action `alternatingMapAction` takes analytic families
`γ = (u, v)` to analytic families. This is the finite-coordinate input to Corollary 4.6,
from Theorem 4.4 via `isAdmissibleOn_of_finite_coordinates`. Neither the field nor the fibers
need be complete.
-/

noncomputable section

open scoped Manifold ContDiff
open Set

namespace AlternatingAnalytic

variable {K P M E E' F F' : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup P] [NormedSpace K P]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]
  [NormedAddCommGroup F'] [NormedSpace K F']

variable [TopologicalSpace M] [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]

end AlternatingAnalytic
