import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff08Nat : Nat → Nat → ℚ
  | 1, 8 => q (1) 2
  | 2, 8 => q (1) 2
  | 8, 1 => q (1) 2
  | 8, 2 => q (1) 2
  | 12, 21 => q (1) 2
  | 13, 20 => q (-1) 2
  | 15, 26 => q (1) 2
  | 18, 23 => q (-1) 2
  | 20, 13 => q (-1) 2
  | 21, 12 => q (1) 2
  | 23, 18 => q (-1) 2
  | 26, 15 => q (1) 2
  | _, _ => 0

/--
@isnad1 id=eq.0h2v.s5.6442935f1c4a from=translated src=- shape=f9c2948e vocab=054cbf87
-/
theorem tensorCoeff_slice_08 (i j : Fin 27) :
    tensorCoeff i j (8 : Fin 27) = coeff08Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

/--
@isnad1 id=eq.0h2v.s5.a514f74e9052 from=translated src=- shape=fe54b80c vocab=ac69a6c3
-/
theorem tensorProduct_coord_08_slice (x y : Coord) :
    tensorProduct x y (8 : Fin 27) = productForm x y (8 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_08]
  simp [coeff08Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
