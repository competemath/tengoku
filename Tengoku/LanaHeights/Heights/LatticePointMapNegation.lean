import Tengoku.LanaHeights.Heights.LatticeQuotientPoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option linter.style.header false

/-!
# Negation compatibility of the lattice point map

This file records the first algebraic compatibility of the explicit
Weierstrass point map. Evenness of `℘` and oddness of `℘′` show that complex
negation maps to elliptic-curve negation, both before and after descent to
`ℂ/L`; the origin maps to the point at infinity.

This does not prove compatibility with addition, so it does not package the
map as a group homomorphism. It also does not prove injectivity, surjectivity,
or complex uniformization.
-/

open scoped UpperHalfPlane

noncomputable section

namespace Heights

/-- The origin of `ℂ` maps to the point at infinity. -/
@[simp] theorem latticePointMap_zero (τ : ℍ) :
    latticePointMap τ 0 = 0 :=
  latticePointMap_of_mem τ 0
    (periodPairOfUpperHalfPlane τ).lattice.zero_mem

/-- Complex negation agrees with elliptic-curve negation under the total
lattice point map. -/
@[simp] theorem latticePointMap_neg (τ : ℍ) (z : ℂ) :
    latticePointMap τ (-z) = -latticePointMap τ z := by
  classical
  by_cases hz : z ∈ (periodPairOfUpperHalfPlane τ).lattice
  · have hnz : -z ∈ (periodPairOfUpperHalfPlane τ).lattice := neg_mem hz
    rw [latticePointMap_of_mem τ z hz, latticePointMap_of_mem τ (-z) hnz]
    exact (WeierstrassCurve.Affine.Point.neg_zero).symm
  · have hnz : -z ∉ (periodPairOfUpperHalfPlane τ).lattice := by
      simpa only [neg_mem_iff] using hz
    rw [latticePointMap_of_notMem τ z hz, latticePointMap_of_notMem τ (-z) hnz]
    simp only [latticeAffinePoint, WeierstrassCurve.Affine.Point.mk,
      WeierstrassCurve.Affine.Point.neg_def, WeierstrassCurve.Affine.Point.neg]
    congr 1
    · exact (periodPairOfUpperHalfPlane τ).weierstrassP_neg z
    · rw [(periodPairOfUpperHalfPlane τ).derivWeierstrassP_neg]
      simp [WeierstrassCurve.Affine.negY]
      ring

end Heights
