import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff04Nat : Nat → Nat → ℚ
  | 1, 4 => q (1) 2
  | 2, 4 => q (1) 2
  | 4, 1 => q (1) 2
  | 4, 2 => q (1) 2
  | 15, 19 => q (1) 2
  | 16, 20 => q (1) 2
  | 17, 21 => q (1) 2
  | 18, 22 => q (1) 2
  | 19, 15 => q (1) 2
  | 20, 16 => q (1) 2
  | 21, 17 => q (1) 2
  | 22, 18 => q (1) 2
  | _, _ => 0

/--
@isnad1 id=eq.0h2v.s5.e96f40be811f from=translated src=- shape=f9c2948e vocab=1f85da5c
-/
theorem tensorCoeff_slice_04 (i j : Fin 27) :
    tensorCoeff i j (4 : Fin 27) = coeff04Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

/--
@isnad1 id=eq.0h2v.s5.dc2beb79ca1a from=translated src=- shape=fe54b80c vocab=ac69a6c3
-/
theorem tensorProduct_coord_04_slice (x y : Coord) :
    tensorProduct x y (4 : Fin 27) = productForm x y (4 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_04]
  simp [coeff04Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
