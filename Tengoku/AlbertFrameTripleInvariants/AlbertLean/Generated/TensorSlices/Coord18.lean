import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff18Nat : Nat → Nat → ℚ
  | 0, 18 => q (1) 2
  | 2, 18 => q (1) 2
  | 4, 26 => q (1) 2
  | 5, 21 => q (-1) 2
  | 6, 20 => q (1) 2
  | 8, 19 => q (-1) 2
  | 18, 0 => q (1) 2
  | 18, 2 => q (1) 2
  | 19, 8 => q (-1) 2
  | 20, 6 => q (1) 2
  | 21, 5 => q (-1) 2
  | 26, 4 => q (1) 2
  | _, _ => 0

theorem tensorCoeff_slice_18 (i j : Fin 27) :
    tensorCoeff i j (18 : Fin 27) = coeff18Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

theorem tensorProduct_coord_18_slice (x y : Coord) :
    tensorProduct x y (18 : Fin 27) = productForm x y (18 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_18]
  simp [coeff18Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
