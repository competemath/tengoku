import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff12Nat : Nat → Nat → ℚ
  | 0, 12 => q (1) 2
  | 2, 12 => q (1) 2
  | 3, 20 => q (1) 2
  | 5, 23 => q (-1) 2
  | 8, 25 => q (1) 2
  | 9, 26 => q (1) 2
  | 12, 0 => q (1) 2
  | 12, 2 => q (1) 2
  | 20, 3 => q (1) 2
  | 23, 5 => q (-1) 2
  | 25, 8 => q (1) 2
  | 26, 9 => q (1) 2
  | _, _ => 0

/--
@isnad1 id=eq.0h2v.s5.43a45dfb0813 from=translated src=- shape=f9c2948e vocab=eb0447ad
-/
theorem tensorCoeff_slice_12 (i j : Fin 27) :
    tensorCoeff i j (12 : Fin 27) = coeff12Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

/--
@isnad1 id=eq.0h2v.s5.b00d9115fb1f from=translated src=- shape=fe54b80c vocab=ac69a6c3
-/
theorem tensorProduct_coord_12_slice (x y : Coord) :
    tensorProduct x y (12 : Fin 27) = productForm x y (12 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_12]
  simp [coeff12Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
