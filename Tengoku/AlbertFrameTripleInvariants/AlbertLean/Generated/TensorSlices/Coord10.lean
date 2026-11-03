import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff10Nat : Nat → Nat → ℚ
  | 1, 10 => q (1) 2
  | 2, 10 => q (1) 2
  | 10, 1 => q (1) 2
  | 10, 2 => q (1) 2
  | 13, 22 => q (1) 2
  | 14, 21 => q (-1) 2
  | 15, 24 => q (1) 2
  | 16, 23 => q (-1) 2
  | 21, 14 => q (-1) 2
  | 22, 13 => q (1) 2
  | 23, 16 => q (-1) 2
  | 24, 15 => q (1) 2
  | _, _ => 0

/--
@isnad1 id=eq.0h2v.s5.18b040b95b6a from=translated src=- shape=f9c2948e vocab=3d97c8ff
-/
theorem tensorCoeff_slice_10 (i j : Fin 27) :
    tensorCoeff i j (10 : Fin 27) = coeff10Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

/--
@isnad1 id=eq.0h2v.s5.08b086cc09e3 from=translated src=- shape=fe54b80c vocab=ac69a6c3
-/
theorem tensorProduct_coord_10_slice (x y : Coord) :
    tensorProduct x y (10 : Fin 27) = productForm x y (10 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_10]
  simp [coeff10Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
