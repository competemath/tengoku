import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff05Nat : Nat → Nat → ℚ
  | 1, 5 => q (1) 2
  | 2, 5 => q (1) 2
  | 5, 1 => q (1) 2
  | 5, 2 => q (1) 2
  | 11, 20 => q (1) 2
  | 12, 19 => q (-1) 2
  | 17, 26 => q (1) 2
  | 18, 25 => q (-1) 2
  | 19, 12 => q (-1) 2
  | 20, 11 => q (1) 2
  | 25, 18 => q (-1) 2
  | 26, 17 => q (1) 2
  | _, _ => 0

theorem tensorCoeff_slice_05 (i j : Fin 27) :
    tensorCoeff i j (5 : Fin 27) = coeff05Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

theorem tensorProduct_coord_05_slice (x y : Coord) :
    tensorProduct x y (5 : Fin 27) = productForm x y (5 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_05]
  simp [coeff05Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
