import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff26Nat : Nat → Nat → ℚ
  | 0, 26 => q (1) 2
  | 1, 26 => q (1) 2
  | 3, 18 => q (1) 2
  | 5, 13 => q (1) 2
  | 6, 12 => q (-1) 2
  | 8, 11 => q (1) 2
  | 11, 8 => q (1) 2
  | 12, 6 => q (-1) 2
  | 13, 5 => q (1) 2
  | 18, 3 => q (1) 2
  | 26, 0 => q (1) 2
  | 26, 1 => q (1) 2
  | _, _ => 0

/--
@isnad1 id=eq.0h2v.s5.f9ea033e5e48 from=translated src=- shape=f9c2948e vocab=08b60391
-/
theorem tensorCoeff_slice_26 (i j : Fin 27) :
    tensorCoeff i j (26 : Fin 27) = coeff26Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

/--
@isnad1 id=eq.0h2v.s5.7e022f1075b5 from=translated src=- shape=fe54b80c vocab=ac69a6c3
-/
theorem tensorProduct_coord_26_slice (x y : Coord) :
    tensorProduct x y (26 : Fin 27) = productForm x y (26 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_26]
  simp [coeff26Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
