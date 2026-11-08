module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvgInnerMoments24Final

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Inner-product moments for `sphereAvg24`

This file derives formulas for the moments of `x ↦ ⟪x, v⟫` on `Ω₂₄` for an arbitrary vector `v`,
reducing to the unit-vector case proved in
`SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvgInnerMoments24Final`.

## Main statements
* `SphereAvgMoments24.sphereAvg24_inner_pow_two`
* `SphereAvgMoments24.sphereAvg24_inner_pow_four`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Uniqueness.BS81.Thm14

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SphereAvgMoments24

end SphereAvgMoments24

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16
