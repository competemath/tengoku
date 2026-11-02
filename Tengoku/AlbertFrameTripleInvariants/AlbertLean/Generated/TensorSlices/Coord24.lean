import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff24Nat : Nat → Nat → ℚ
  | 0, 24 => q (1) 2
  | 1, 24 => q (1) 2
  | 3, 16 => q (1) 2
  | 6, 14 => q (1) 2
  | 7, 13 => q (-1) 2
  | 10, 11 => q (1) 2
  | 11, 10 => q (1) 2
  | 13, 7 => q (-1) 2
  | 14, 6 => q (1) 2
  | 16, 3 => q (1) 2
  | 24, 0 => q (1) 2
  | 24, 1 => q (1) 2
  | _, _ => 0

theorem tensorCoeff_slice_24 (i j : Fin 27) :
    tensorCoeff i j (24 : Fin 27) = coeff24Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

theorem tensorProduct_coord_24_slice (x y : Coord) :
    tensorProduct x y (24 : Fin 27) = productForm x y (24 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_24]
  simp [coeff24Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
