import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff17Nat : Nat → Nat → ℚ
  | 0, 17 => q (1) 2
  | 2, 17 => q (1) 2
  | 4, 25 => q (1) 2
  | 5, 22 => q (1) 2
  | 7, 20 => q (-1) 2
  | 9, 19 => q (1) 2
  | 17, 0 => q (1) 2
  | 17, 2 => q (1) 2
  | 19, 9 => q (1) 2
  | 20, 7 => q (-1) 2
  | 22, 5 => q (1) 2
  | 25, 4 => q (1) 2
  | _, _ => 0

/--
@isnad1 id=eq.0h2v.s5.b5d395f4649b from=translated src=- shape=f9c2948e vocab=0a32c89d
-/
theorem tensorCoeff_slice_17 (i j : Fin 27) :
    tensorCoeff i j (17 : Fin 27) = coeff17Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

/--
@isnad1 id=eq.0h2v.s5.9e17f81b79b4 from=translated src=- shape=fe54b80c vocab=ac69a6c3
-/
theorem tensorProduct_coord_17_slice (x y : Coord) :
    tensorProduct x y (17 : Fin 27) = productForm x y (17 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_17]
  simp [coeff17Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
