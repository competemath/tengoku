import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff09Nat : Nat → Nat → ℚ
  | 1, 9 => q (1) 2
  | 2, 9 => q (1) 2
  | 9, 1 => q (1) 2
  | 9, 2 => q (1) 2
  | 12, 22 => q (1) 2
  | 14, 20 => q (-1) 2
  | 15, 25 => q (-1) 2
  | 17, 23 => q (1) 2
  | 20, 14 => q (-1) 2
  | 22, 12 => q (1) 2
  | 23, 17 => q (1) 2
  | 25, 15 => q (-1) 2
  | _, _ => 0

theorem tensorCoeff_slice_09 (i j : Fin 27) :
    tensorCoeff i j (9 : Fin 27) = coeff09Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

theorem tensorProduct_coord_09_slice (x y : Coord) :
    tensorProduct x y (9 : Fin 27) = productForm x y (9 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_09]
  simp [coeff09Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
