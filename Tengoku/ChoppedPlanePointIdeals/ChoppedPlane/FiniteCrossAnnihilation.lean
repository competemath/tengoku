module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.FiniteAuxiliaryMaps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! The cross substitution is annihilated by the directional derivative,
over an arbitrary commutative ring and with arbitrary module coefficients. -/

noncomputable section
namespace ChoppedPlane.FiniteCech

open MvPolynomial SymmetricDerivative
open scoped TensorProduct

variable {R : Type*} [CommRing R]

/--
@isnad1 id=eq.1h4v.s9.262c86b4b480 from=translated src=- shape=ea92568d vocab=a413fd8f
-/
theorem directional_linearChange_zero (f : Fin 3 → R)
    (A : Matrix (Fin 3) (Fin 3) R)
    (hA : ∀ i, ∑ j, f j * A i j = 0) (P : Aux R) :
    directional f (linearChange A P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
    simp [map_mul, Derivation.leibniz, hP, directional_linearForm, hA]

/--
@isnad1 id=eq.0h5v.s9.170b68a9a19e from=translated src=- shape=5df708a6 vocab=5c1cdb88
-/
theorem directional_cross_zero (u v z : R) (P : Aux R) :
    directional ![u,v,z] (linearChange (crossMatrix u v z) P) = 0 := by
  apply directional_linearChange_zero
  intro i
  fin_cases i <;> simp [crossMatrix, Fin.sum_univ_three] <;> ring

/--
@isnad1 id=eq.0h4v.s8.4cf4e66f7c6b from=translated src=- shape=03d19d01 vocab=e18882eb
-/
theorem linearChange_cross_linearForm_zero (u v z : R) :
    linearChange (crossMatrix u v z) (linearForm ![u,v,z]) = 0 := by
  rw [linearChange_linearForm]
  have h : (fun k => ∑ j, ![u,v,z] j * crossMatrix u v z j k) = 0 := by
    funext k
    fin_cases k <;> simp [crossMatrix, Fin.sum_univ_three] <;> ring
  rw [h]
  simp [linearForm]

variable {M : Type*} [AddCommGroup M] [Module R M]

end ChoppedPlane.FiniteCech
