import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff23Nat : Nat → Nat → ℚ
  | 0, 23 => q (1) 2
  | 1, 23 => q (1) 2
  | 3, 15 => q (1) 2
  | 8, 14 => q (-1) 2
  | 9, 13 => q (1) 2
  | 10, 12 => q (-1) 2
  | 12, 10 => q (-1) 2
  | 13, 9 => q (1) 2
  | 14, 8 => q (-1) 2
  | 15, 3 => q (1) 2
  | 23, 0 => q (1) 2
  | 23, 1 => q (1) 2
  | _, _ => 0

theorem tensorCoeff_slice_23 (i j : Fin 27) :
    tensorCoeff i j (23 : Fin 27) = coeff23Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

theorem tensorProduct_coord_23_slice (x y : Coord) :
    tensorProduct x y (23 : Fin 27) = productForm x y (23 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_23]
  simp [coeff23Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
