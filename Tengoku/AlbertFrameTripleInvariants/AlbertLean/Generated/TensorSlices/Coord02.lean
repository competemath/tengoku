import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

def coeff02Nat : Nat → Nat → ℚ
  | 2, 2 => q (1) 1
  | 3, 4 => q (1) 2
  | 4, 3 => q (1) 2
  | 5, 10 => q (1) 2
  | 6, 9 => q (-1) 2
  | 7, 8 => q (1) 2
  | 8, 7 => q (1) 2
  | 9, 6 => q (-1) 2
  | 10, 5 => q (1) 2
  | 11, 15 => q (1) 2
  | 12, 16 => q (1) 2
  | 13, 17 => q (1) 2
  | 14, 18 => q (1) 2
  | 15, 11 => q (1) 2
  | 16, 12 => q (1) 2
  | 17, 13 => q (1) 2
  | 18, 14 => q (1) 2
  | _, _ => 0

/--
@isnad1 id=eq.0h2v.s5.3dd362aada2e from=translated src=- shape=f9c2948e vocab=a8b70ecd
-/
theorem tensorCoeff_slice_02 (i j : Fin 27) :
    tensorCoeff i j (2 : Fin 27) = coeff02Nat i.val j.val := by
  fin_cases i <;> fin_cases j <;> rfl

/--
@isnad1 id=eq.0h2v.s5.7410bac6da93 from=translated src=- shape=fe54b80c vocab=ac69a6c3
-/
theorem tensorProduct_coord_02_slice (x y : Coord) :
    tensorProduct x y (2 : Fin 27) = productForm x y (2 : Fin 27) := by
  simp only [tensorProduct, tensorCoeff_slice_02]
  simp [coeff02Nat, productForm, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean.Generated
