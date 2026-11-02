import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff11Nat : Nat → Nat → ℚ
  | 0, 11 => q (1) 2
  | 2, 11 => q (1) 2
  | 3, 19 => q (1) 2
  | 5, 24 => q (1) 2
  | 6, 25 => q (1) 2
  | 7, 26 => q (1) 2
  | 11, 0 => q (1) 2
  | 11, 2 => q (1) 2
  | 19, 3 => q (1) 2
  | 24, 5 => q (1) 2
  | 25, 6 => q (1) 2
  | 26, 7 => q (1) 2
  | _, _ => 0

theorem tensorCoeff_slice_11 (i j : Fin 27) :
    tensorCoeff i j (11 : Fin 27) = coeff11Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

theorem tensorProduct_coord_11_slice (x y : Coord) :
    tensorProduct x y (11 : Fin 27) = productForm x y (11 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_11]
  simp [coeff11Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
