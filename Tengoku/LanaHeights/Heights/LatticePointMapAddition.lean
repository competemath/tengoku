import Tengoku.LanaHeights.Heights.WeierstrassAddition
import Tengoku.LanaHeights.Heights.LatticePointMapInjectivity
import Tengoku.LanaHeights.Heights.WeierstrassSurjectivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option linter.style.header false

/-!
# Addition compatibility of the lattice point map

The global Weierstrass addition formula is matched here with mathlib's affine
elliptic-curve group law.  After recording the nonvertical secant case, the
tangent case is reduced to three generic secants by choosing an auxiliary
point outside a countable exceptional set.  The total map is therefore
additive in all cases, and its quotient descent is packaged as an additive
equivalence.
-/

open scoped UpperHalfPlane

noncomputable section
namespace Heights

/-- The total lattice point map respects addition when all three arguments are
finite and the corresponding secant is nonvertical. -/
theorem latticePointMap_add_of_notMem_of_weierstrassP_ne (τ : ℍ) (z w : ℂ)
    (hz : z ∉ (periodPairOfUpperHalfPlane τ).lattice)
    (hw : w ∉ (periodPairOfUpperHalfPlane τ).lattice)
    (hzw : z + w ∉ (periodPairOfUpperHalfPlane τ).lattice)
    (hne : (periodPairOfUpperHalfPlane τ).weierstrassP z ≠
      (periodPairOfUpperHalfPlane τ).weierstrassP w) :
    latticePointMap τ (z + w) = latticePointMap τ z + latticePointMap τ w := by
  let L := periodPairOfUpperHalfPlane τ
  have hadd := weierstrass_addition_coordinates L z w hz hw hzw hne
  rw [latticePointMap_of_notMem τ (z + w) hzw,
    latticePointMap_of_notMem τ z hz, latticePointMap_of_notMem τ w hw]
  unfold latticeAffinePoint
  simp only [WeierstrassCurve.Affine.Point.mk]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hne]
  congr 1
  · dsimp only [L] at hadd ⊢
    simp only [WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.slope_of_X_ne hne,
      latticeWeierstrassCurve_a₁, latticeWeierstrassCurve_a₂, zero_mul,
      sub_zero]
    rw [← hadd.1]
    unfold weierstrassSecantAddX weierstrassSecantSlope
    field_simp [hne]
    ring
  · dsimp only [L] at hadd ⊢
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.slope_of_X_ne hne,
      latticeWeierstrassCurve_a₁, latticeWeierstrassCurve_a₂,
      latticeWeierstrassCurve_a₃, zero_mul, sub_zero]
    rw [← hadd.2]
    unfold weierstrassSecantAddY weierstrassSecantAddX
      weierstrassSecantSlope
    field_simp [hne]
    ring

end Heights
