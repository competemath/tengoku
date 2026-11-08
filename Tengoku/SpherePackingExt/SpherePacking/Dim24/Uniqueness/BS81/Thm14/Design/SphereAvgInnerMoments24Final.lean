module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvgMoments
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvgFourthMoment24Final

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Inner-product moments for `sphereAvg24`

This file packages the second and fourth moments of `x ↦ ⟪x,u⟫` on the unit sphere `Ω₂₄`, in a form
convenient for deriving the BS81 distance distribution (equation (11)).

## Main statements
* `sphereAvg24_inner_pow_two_of_norm_one`
* `sphereAvg24_inner_pow_four_of_norm_one`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14

noncomputable section

open scoped RealInnerProductSpace BigOperators

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
## Existence of an isometry sending a unit vector to `e₀`

We use the orthonormal-basis extension lemma from
`SphereAvgFourthMoment24Final` (`exists_linearIsometryEquiv_map_unit_to_basis0`).
-/

/-!
## Second and fourth inner moments
-/

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14
