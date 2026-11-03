import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff14Nat : Nat → Nat → ℚ
  | 0, 14 => q (1) 2
  | 2, 14 => q (1) 2
  | 3, 22 => q (1) 2
  | 7, 23 => q (-1) 2
  | 9, 24 => q (-1) 2
  | 10, 25 => q (-1) 2
  | 14, 0 => q (1) 2
  | 14, 2 => q (1) 2
  | 22, 3 => q (1) 2
  | 23, 7 => q (-1) 2
  | 24, 9 => q (-1) 2
  | 25, 10 => q (-1) 2
  | _, _ => 0

/--
@isnad1 id=eq.0h2v.s5.16eb62253713 from=translated src=- shape=f9c2948e vocab=09e9beb6
-/
theorem tensorCoeff_slice_14 (i j : Fin 27) :
    tensorCoeff i j (14 : Fin 27) = coeff14Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

/--
@isnad1 id=eq.0h2v.s5.8ba090c153bc from=translated src=- shape=fe54b80c vocab=ac69a6c3
-/
theorem tensorProduct_coord_14_slice (x y : Coord) :
    tensorProduct x y (14 : Fin 27) = productForm x y (14 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_14]
  simp [coeff14Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
