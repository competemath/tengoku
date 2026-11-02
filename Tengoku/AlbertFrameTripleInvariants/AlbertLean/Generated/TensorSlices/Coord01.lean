import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff01Nat : Nat → Nat → ℚ
  | 1, 1 => q (1) 1
  | 3, 4 => q (1) 2
  | 4, 3 => q (1) 2
  | 5, 10 => q (1) 2
  | 6, 9 => q (-1) 2
  | 7, 8 => q (1) 2
  | 8, 7 => q (1) 2
  | 9, 6 => q (-1) 2
  | 10, 5 => q (1) 2
  | 19, 23 => q (1) 2
  | 20, 24 => q (1) 2
  | 21, 25 => q (1) 2
  | 22, 26 => q (1) 2
  | 23, 19 => q (1) 2
  | 24, 20 => q (1) 2
  | 25, 21 => q (1) 2
  | 26, 22 => q (1) 2
  | _, _ => 0

theorem tensorCoeff_slice_01 (i j : Fin 27) :
    tensorCoeff i j (1 : Fin 27) = coeff01Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

theorem tensorProduct_coord_01_slice (x y : Coord) :
    tensorProduct x y (1 : Fin 27) = productForm x y (1 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_01]
  simp [coeff01Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
