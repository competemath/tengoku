import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff19Nat : Nat → Nat → ℚ
  | 0, 19 => q (1) 2
  | 1, 19 => q (1) 2
  | 4, 11 => q (1) 2
  | 5, 16 => q (-1) 2
  | 6, 17 => q (-1) 2
  | 7, 18 => q (-1) 2
  | 11, 4 => q (1) 2
  | 16, 5 => q (-1) 2
  | 17, 6 => q (-1) 2
  | 18, 7 => q (-1) 2
  | 19, 0 => q (1) 2
  | 19, 1 => q (1) 2
  | _, _ => 0

theorem tensorCoeff_slice_19 (i j : Fin 27) :
    tensorCoeff i j (19 : Fin 27) = coeff19Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

theorem tensorProduct_coord_19_slice (x y : Coord) :
    tensorProduct x y (19 : Fin 27) = productForm x y (19 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_19]
  simp [coeff19Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
