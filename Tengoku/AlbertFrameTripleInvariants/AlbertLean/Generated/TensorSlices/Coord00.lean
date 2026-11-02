import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff00Nat : Nat → Nat → ℚ
  | 0, 0 => q (1) 1
  | 11, 15 => q (1) 2
  | 12, 16 => q (1) 2
  | 13, 17 => q (1) 2
  | 14, 18 => q (1) 2
  | 15, 11 => q (1) 2
  | 16, 12 => q (1) 2
  | 17, 13 => q (1) 2
  | 18, 14 => q (1) 2
  | 19, 23 => q (1) 2
  | 20, 24 => q (1) 2
  | 21, 25 => q (1) 2
  | 22, 26 => q (1) 2
  | 23, 19 => q (1) 2
  | 24, 20 => q (1) 2
  | 25, 21 => q (1) 2
  | 26, 22 => q (1) 2
  | _, _ => 0

theorem tensorCoeff_slice_00 (i j : Fin 27) :
    tensorCoeff i j (0 : Fin 27) = coeff00Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

theorem tensorProduct_coord_00_slice (x y : Coord) :
    tensorProduct x y (0 : Fin 27) = productForm x y (0 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_00]
  simp [coeff00Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
