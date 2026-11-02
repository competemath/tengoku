import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff03Nat : Nat → Nat → ℚ
  | 1, 3 => q (1) 2
  | 2, 3 => q (1) 2
  | 3, 1 => q (1) 2
  | 3, 2 => q (1) 2
  | 11, 23 => q (1) 2
  | 12, 24 => q (1) 2
  | 13, 25 => q (1) 2
  | 14, 26 => q (1) 2
  | 23, 11 => q (1) 2
  | 24, 12 => q (1) 2
  | 25, 13 => q (1) 2
  | 26, 14 => q (1) 2
  | _, _ => 0

theorem tensorCoeff_slice_03 (i j : Fin 27) :
    tensorCoeff i j (3 : Fin 27) = coeff03Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

theorem tensorProduct_coord_03_slice (x y : Coord) :
    tensorProduct x y (3 : Fin 27) = productForm x y (3 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_03]
  simp [coeff03Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
