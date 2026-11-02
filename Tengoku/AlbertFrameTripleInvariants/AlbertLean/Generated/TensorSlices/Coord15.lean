import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff15Nat : Nat → Nat → ℚ
  | 0, 15 => q (1) 2
  | 2, 15 => q (1) 2
  | 4, 23 => q (1) 2
  | 8, 22 => q (1) 2
  | 9, 21 => q (-1) 2
  | 10, 20 => q (1) 2
  | 15, 0 => q (1) 2
  | 15, 2 => q (1) 2
  | 20, 10 => q (1) 2
  | 21, 9 => q (-1) 2
  | 22, 8 => q (1) 2
  | 23, 4 => q (1) 2
  | _, _ => 0

theorem tensorCoeff_slice_15 (i j : Fin 27) :
    tensorCoeff i j (15 : Fin 27) = coeff15Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

theorem tensorProduct_coord_15_slice (x y : Coord) :
    tensorProduct x y (15 : Fin 27) = productForm x y (15 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_15]
  simp [coeff15Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
