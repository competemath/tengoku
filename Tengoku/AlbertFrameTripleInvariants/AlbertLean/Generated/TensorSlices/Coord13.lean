import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff13Nat : Nat → Nat → ℚ
  | 0, 13 => q (1) 2
  | 2, 13 => q (1) 2
  | 3, 21 => q (1) 2
  | 6, 23 => q (-1) 2
  | 8, 24 => q (-1) 2
  | 10, 26 => q (1) 2
  | 13, 0 => q (1) 2
  | 13, 2 => q (1) 2
  | 21, 3 => q (1) 2
  | 23, 6 => q (-1) 2
  | 24, 8 => q (-1) 2
  | 26, 10 => q (1) 2
  | _, _ => 0

theorem tensorCoeff_slice_13 (i j : Fin 27) :
    tensorCoeff i j (13 : Fin 27) = coeff13Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

theorem tensorProduct_coord_13_slice (x y : Coord) :
    tensorProduct x y (13 : Fin 27) = productForm x y (13 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_13]
  simp [coeff13Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
