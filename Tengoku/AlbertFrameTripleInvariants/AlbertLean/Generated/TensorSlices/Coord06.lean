import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff06Nat : Nat → Nat → ℚ
  | 1, 6 => q (1) 2
  | 2, 6 => q (1) 2
  | 6, 1 => q (1) 2
  | 6, 2 => q (1) 2
  | 11, 21 => q (1) 2
  | 13, 19 => q (-1) 2
  | 16, 26 => q (-1) 2
  | 18, 24 => q (1) 2
  | 19, 13 => q (-1) 2
  | 21, 11 => q (1) 2
  | 24, 18 => q (1) 2
  | 26, 16 => q (-1) 2
  | _, _ => 0

theorem tensorCoeff_slice_06 (i j : Fin 27) :
    tensorCoeff i j (6 : Fin 27) = coeff06Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

theorem tensorProduct_coord_06_slice (x y : Coord) :
    tensorProduct x y (6 : Fin 27) = productForm x y (6 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_06]
  simp [coeff06Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
