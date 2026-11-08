module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvgMoments
import Tengoku.Seed.Tactic.FunProp
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic lemmas for `sphereAvg24`

This file collects integrability and linearity lemmas for the spherical average `sphereAvg24`.
These are shared between the design computations and the `44` common-neighbors moment package.

## Main statements
* `integrable_coord_pow_mul_coord_pow`
* `integrable_inner_pow_mul_inner_pow`
* `sphereAvg24_congr`
* `sphereAvg24_neg`
* `sphereAvg24_finset_sum`
* `sphereAvg24_finset_sum₂`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14

noncomputable section

open scoped RealInnerProductSpace BigOperators ENNReal
open MeasureTheory Set

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14
