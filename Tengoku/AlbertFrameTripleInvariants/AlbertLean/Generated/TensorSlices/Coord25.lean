import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff25Nat : Nat → Nat → ℚ
  | 0, 25 => q (1) 2
  | 1, 25 => q (1) 2
  | 3, 17 => q (1) 2
  | 5, 14 => q (-1) 2
  | 7, 12 => q (1) 2
  | 9, 11 => q (-1) 2
  | 11, 9 => q (-1) 2
  | 12, 7 => q (1) 2
  | 14, 5 => q (-1) 2
  | 17, 3 => q (1) 2
  | 25, 0 => q (1) 2
  | 25, 1 => q (1) 2
  | _, _ => 0

/--
@isnad1 id=eq.0h2v.s5.62719aa2fd4f from=translated src=- shape=f9c2948e vocab=65bf7d57
-/
theorem tensorCoeff_slice_25 (i j : Fin 27) :
    tensorCoeff i j (25 : Fin 27) = coeff25Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

/--
@isnad1 id=eq.0h2v.s5.fe12501d1671 from=translated src=- shape=fe54b80c vocab=ac69a6c3
-/
theorem tensorProduct_coord_25_slice (x y : Coord) :
    tensorProduct x y (25 : Fin 27) = productForm x y (25 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_25]
  simp [coeff25Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
