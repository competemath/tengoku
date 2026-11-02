import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff20Nat : Nat → Nat → ℚ
  | 0, 20 => q (1) 2
  | 1, 20 => q (1) 2
  | 4, 12 => q (1) 2
  | 5, 15 => q (1) 2
  | 8, 17 => q (-1) 2
  | 9, 18 => q (-1) 2
  | 12, 4 => q (1) 2
  | 15, 5 => q (1) 2
  | 17, 8 => q (-1) 2
  | 18, 9 => q (-1) 2
  | 20, 0 => q (1) 2
  | 20, 1 => q (1) 2
  | _, _ => 0

theorem tensorCoeff_slice_20 (i j : Fin 27) :
    tensorCoeff i j (20 : Fin 27) = coeff20Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

theorem tensorProduct_coord_20_slice (x y : Coord) :
    tensorProduct x y (20 : Fin 27) = productForm x y (20 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_20]
  simp [coeff20Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
