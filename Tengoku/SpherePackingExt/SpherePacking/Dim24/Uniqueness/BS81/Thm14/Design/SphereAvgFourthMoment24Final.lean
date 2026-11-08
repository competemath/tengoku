module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvg24Lemmas
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fourth coordinate moment for `sphereAvg24`

This file computes the fourth moment of a coordinate under the spherical average in dimension `24`:
`sphereAvg24 (x ↦ (x 0) ^ 4) = 1 / 208`.

The proof uses rotation invariance and a short linear system relating
`E[x_0 ^ 4]` and `E[x_0 ^ 2 * x_1 ^ 2]`.

## Main statements
* `exists_linearIsometryEquiv_map_unit_to_basis0`
* `sphereAvg24_coord_pow_four`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14

noncomputable section

open scoped RealInnerProductSpace BigOperators ENNReal

open MeasureTheory

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
## Linearity helpers for `sphereAvg24`
-/

/-!
## Odd mixed terms vanish by sign symmetry
-/

/-!
## Fourth coordinate moment
-/

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14
