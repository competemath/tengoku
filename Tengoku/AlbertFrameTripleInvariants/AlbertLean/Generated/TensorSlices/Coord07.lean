import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff07Nat : Nat → Nat → ℚ
  | 1, 7 => q (1) 2
  | 2, 7 => q (1) 2
  | 7, 1 => q (1) 2
  | 7, 2 => q (1) 2
  | 11, 22 => q (1) 2
  | 14, 19 => q (-1) 2
  | 16, 25 => q (1) 2
  | 17, 24 => q (-1) 2
  | 19, 14 => q (-1) 2
  | 22, 11 => q (1) 2
  | 24, 17 => q (-1) 2
  | 25, 16 => q (1) 2
  | _, _ => 0

/--
@isnad1 id=eq.0h2v.s5.e56601241005 from=translated src=- shape=f9c2948e vocab=9d16170e
-/
theorem tensorCoeff_slice_07 (i j : Fin 27) :
    tensorCoeff i j (7 : Fin 27) = coeff07Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

/--
@isnad1 id=eq.0h2v.s5.5a6fa9d69d73 from=translated src=- shape=fe54b80c vocab=ac69a6c3
-/
theorem tensorProduct_coord_07_slice (x y : Coord) :
    tensorProduct x y (7 : Fin 27) = productForm x y (7 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_07]
  simp [coeff07Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
