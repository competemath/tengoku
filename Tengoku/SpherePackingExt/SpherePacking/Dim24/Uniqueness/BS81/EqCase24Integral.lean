module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.LatticeL
import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.EqCase24Support

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integer-valued inner products after scaling

In the BS81 equality case, the inner products between code vectors lie in the support set
`{1, -1, ±1/2, ±1/4, 0}`. After scaling the code by `2`, all such inner products become integers.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

open scoped RealInnerProductSpace Pointwise

end SpherePacking.Dim24.Uniqueness.BS81
