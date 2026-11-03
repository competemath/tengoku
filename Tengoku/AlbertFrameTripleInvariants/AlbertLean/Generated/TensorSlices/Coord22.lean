import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff22Nat : Nat → Nat → ℚ
  | 0, 22 => q (1) 2
  | 1, 22 => q (1) 2
  | 4, 14 => q (1) 2
  | 7, 15 => q (1) 2
  | 9, 16 => q (1) 2
  | 10, 17 => q (1) 2
  | 14, 4 => q (1) 2
  | 15, 7 => q (1) 2
  | 16, 9 => q (1) 2
  | 17, 10 => q (1) 2
  | 22, 0 => q (1) 2
  | 22, 1 => q (1) 2
  | _, _ => 0

/--
@isnad1 id=eq.0h2v.s5.f61fc76d2d65 from=translated src=- shape=f9c2948e vocab=2df208f0
-/
theorem tensorCoeff_slice_22 (i j : Fin 27) :
    tensorCoeff i j (22 : Fin 27) = coeff22Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

/--
@isnad1 id=eq.0h2v.s5.0d818b5874b7 from=translated src=- shape=fe54b80c vocab=ac69a6c3
-/
theorem tensorProduct_coord_22_slice (x y : Coord) :
    tensorProduct x y (22 : Fin 27) = productForm x y (22 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_22]
  simp [coeff22Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
