import Tengoku.TheIwasawaTowerLawForRamanujanSThirdOrderMockThetaFunction.IwasawaTower.CharacteristicThree
import Tengoku.Seed.Algebra.Polynomial.Div

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The finite characteristic-three polynomial congruence

Author: Joesph D. Burke III.
-/

noncomputable section

namespace IwasawaTower

open Polynomial

abbrev 𝔽₃ := ZMod 3

/-- `F_N(1-Y)` over `𝔽₃`.-/
def reducedReversedPolynomial (N : ℕ) : 𝔽₃[X] :=
  (FPoly N : 𝔽₃[X]).comp (1 - X)

/-- `F_N(1-Y)` over `ℤ`, before reduction modulo three.-/
def integerReversedPolynomial (N : ℕ) : ℤ[X] :=
  (FPoly N : ℤ[X]).comp (1 - X)

private theorem map_APoly (r : ℕ) :
    (APoly r : ℤ[X]).map (Int.castRingHom 𝔽₃) = (APoly r : 𝔽₃[X]) := by
  simp only [APoly]
  change (Polynomial.mapRingHom (Int.castRingHom 𝔽₃))
    (∏ j ∈ Finset.range r, (1 + X ^ (j + 1))) = _
  rw [map_prod (Polynomial.mapRingHom (Int.castRingHom 𝔽₃))]
  simp

private theorem map_FPoly (N : ℕ) :
    (FPoly N : ℤ[X]).map (Int.castRingHom 𝔽₃) = (FPoly N : 𝔽₃[X]) := by
  simp only [FPoly]
  change (Polynomial.mapRingHom (Int.castRingHom 𝔽₃))
    (∑ r ∈ Finset.range N, X ^ (r + 1) * (APoly r : ℤ[X]) ^ 2) = _
  rw [map_sum (Polynomial.mapRingHom (Int.castRingHom 𝔽₃))]
  simp [map_APoly]

/--
@isnad1 id=eq.0h1v.s5.07ca161d39a3 from=translated src=- shape=81d85d90 vocab=c34ec458
-/
@[simp] theorem map_integerReversedPolynomial (N : ℕ) :
    (integerReversedPolynomial N).map (Int.castRingHom 𝔽₃) =
      reducedReversedPolynomial N := by
  rw [integerReversedPolynomial, reducedReversedPolynomial, Polynomial.map_comp,
    map_FPoly]
  simp

end IwasawaTower
