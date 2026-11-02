import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff16Nat : Nat → Nat → ℚ
  | 0, 16 => q (1) 2
  | 2, 16 => q (1) 2
  | 4, 24 => q (1) 2
  | 6, 22 => q (-1) 2
  | 7, 21 => q (1) 2
  | 10, 19 => q (-1) 2
  | 16, 0 => q (1) 2
  | 16, 2 => q (1) 2
  | 19, 10 => q (-1) 2
  | 21, 7 => q (1) 2
  | 22, 6 => q (-1) 2
  | 24, 4 => q (1) 2
  | _, _ => 0

theorem tensorCoeff_slice_16 (i j : Fin 27) :
    tensorCoeff i j (16 : Fin 27) = coeff16Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

theorem tensorProduct_coord_16_slice (x y : Coord) :
    tensorProduct x y (16 : Fin 27) = productForm x y (16 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_16]
  simp [coeff16Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
