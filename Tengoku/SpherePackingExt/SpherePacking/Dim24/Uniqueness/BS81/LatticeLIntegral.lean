module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.LatticeL
import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.EqCase24Integral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integrality of `latticeL`

In the BS81 equality case, the lattice `latticeL C := span_ℤ (2 • C)` is integral: all inner
products between lattice vectors are integers. The key input is that pairwise inner products on
`twoCodeVectors C` are integers and integrality is preserved under taking `ℤ`-linear combinations.

## Main statements
* `Uniqueness.BS81.inner_latticeL_int`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81

noncomputable section

open scoped RealInnerProductSpace Pointwise

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

end

end SpherePacking.Dim24.Uniqueness.BS81
