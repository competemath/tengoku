import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.ModelIdentification
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Direct product transport to the Hermitian split Albert model

The conventional Hermitian square is checked against all 27 coordinates of
the frozen product.  Polarization then transports the full bilinear product.
-/

namespace AlbertLean

open Generated

set_option maxHeartbeats 2000000 in
theorem coordToHermitian_productForm_square (x : Coord) :
    coordToHermitian (productForm x x) =
      Hermitian3.square (coordToHermitian x) := by
  apply Hermitian3.ext
  all_goals try apply Zorn.ext
  all_goals try apply Vec3.ext
  all_goals
    simp [coordToHermitian, coordV, coordS, coordC, Hermitian3.square,
      Hermitian3.add, Zorn.add, Zorn.smul, Zorn.conj, Zorn.mul, Zorn.norm,
      Vec3.add, Vec3.smul, Vec3.neg, Vec3.dot, Vec3.cross,
      productForm, v, q] <;>
    ring

set_option maxHeartbeats 2000000 in
private theorem productForm_polarization (x y : Coord) :
    productForm x y = (2 : ℚ)⁻¹ •
      (productForm (x + y) (x + y) -
        (productForm x x + productForm y y)) := by
  funext k
  fin_cases k <;>
    simp [productForm, v, q] <;>
    ring

/-- The frozen Springer product is the conventional symmetrized H3 product.-/
theorem coordToHermitian_structuredProduct (x y : Coord) :
    coordToHermitian (structuredProduct x y) =
      Hermitian3.jordan (coordToHermitian x) (coordToHermitian y) := by
  rw [structuredProduct_eq_productForm, productForm_polarization,
    coordToHermitian_smul, coordToHermitian_sub, coordToHermitian_add,
    coordToHermitian_productForm_square,
    coordToHermitian_productForm_square,
    coordToHermitian_productForm_square,
    coordToHermitian_add]
  rfl

/-- The frozen C0 product is explicitly the conventional split Albert algebra.-/
theorem conventionalSplitAlbertIdentification :
    ConventionalSplitAlbertIdentification := by
  exact ⟨hermitianToCoord_coordToHermitian,
    coordToHermitian_hermitianToCoord,
    coordToHermitian_add,
    coordToHermitian_smul,
    coordToHermitian_one,
    coordToHermitian_cubicNorm,
    coordToHermitian_structuredProduct⟩

end AlbertLean
