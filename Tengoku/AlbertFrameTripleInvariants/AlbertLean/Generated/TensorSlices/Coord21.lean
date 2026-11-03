import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff21Nat : Nat → Nat → ℚ
  | 0, 21 => q (1) 2
  | 1, 21 => q (1) 2
  | 4, 13 => q (1) 2
  | 6, 15 => q (1) 2
  | 8, 16 => q (1) 2
  | 10, 18 => q (-1) 2
  | 13, 4 => q (1) 2
  | 15, 6 => q (1) 2
  | 16, 8 => q (1) 2
  | 18, 10 => q (-1) 2
  | 21, 0 => q (1) 2
  | 21, 1 => q (1) 2
  | _, _ => 0

/--
@isnad1 id=eq.0h2v.s5.a37f7b6c8ee0 from=translated src=- shape=f9c2948e vocab=e53bb119
-/
theorem tensorCoeff_slice_21 (i j : Fin 27) :
    tensorCoeff i j (21 : Fin 27) = coeff21Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

/--
@isnad1 id=eq.0h2v.s5.ceec966ea301 from=translated src=- shape=fe54b80c vocab=ac69a6c3
-/
theorem tensorProduct_coord_21_slice (x y : Coord) :
    tensorProduct x y (21 : Fin 27) = productForm x y (21 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_21]
  simp [coeff21Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
