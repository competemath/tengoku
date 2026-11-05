module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.LaurentAuxiliaryAdjoints

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
The coefficient operators in the auxiliary residue transpose theorem are
exactly the actual finite tensor differentiation and multiplication maps,
including coefficient modules over a commutative algebra extension.
-/
noncomputable section
namespace ChoppedPlane.LaurentPairing
open Module MvPolynomial SymmetricDerivative FiniteCech
open scoped Classical TensorProduct
variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Literal monomial coefficients of the actual finite tensor linear multiplication.
@isnad1 id=eq.0h6v.s10.a29ffe277f36 from=translated src=- shape=10eb8724 vocab=4c947c35
-/
theorem finiteMultiply_monomial_coefficients (f : Fin 3 → R) (t : ℕ)
    (q : Sym (Fin 3) t → M) (b : Sym (Fin 3) (t + 1)) :
    finiteMultiply f t q b = ∑ s : Sym (Fin 3) t, ∑ i : Fin 3,
      (X i * monomial (homogeneousTensorExponent t s) 1 : MvPolynomial (Fin 3) R).coeff
        (homogeneousTensorExponent (t + 1) b) • (f i • q s) := by
  change tensorCoefficients (((LinearMap.mulLeft R (linearForm f)).rTensor M)
    (∑ s, (monomial (homogeneousTensorExponent t s) 1 : MvPolynomial (Fin 3) R) ⊗ₜ[R] q s))
      (homogeneousTensorExponent (t + 1) b) = _
  simp only [map_sum, Finsupp.finsetSum_apply, LinearMap.rTensor_tmul, LinearMap.mulLeft_apply,
    tensorCoefficients_tmul, linearForm, Finset.sum_mul, mul_assoc, coeff_sum,
    coeff_C_mul, Finset.sum_smul, mul_smul]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro i hi
  exact smul_comm _ _ _

section Algebra
variable [Algebra K R] [Module K M] [IsScalarTower K R M]

/-- The actual action of a coefficient-ring element, restricted to the base field.-/
def scalarAction (a : R) : M →ₗ[K] M :=
  (a • (LinearMap.id : M →ₗ[R] M)).restrictScalars K

/--
@isnad1 id=eq.0h5v.s8.c496502887f4 from=translated src=- shape=d41fd6c4 vocab=bec9eccb
-/
@[simp] theorem scalarAction_apply (a : R) (m : M) : scalarAction (K := K) a m = a • m := rfl

/-- Derivative monomial coefficients commute with extension of coefficients.
@isnad1 id=eq.0h5v.s10.53acc137751d from=translated src=- shape=6732061a vocab=940d9149
-/
theorem algebraMap_pderiv_monomial_coeff (s b : Fin 3 →₀ ℕ) (i : Fin 3) :
    algebraMap K R ((pderiv i (monomial b 1 : Poly K 3)).coeff s) =
      (pderiv i (monomial b 1 : MvPolynomial (Fin 3) R)).coeff s := by
  rw [← coeff_map]
  rw [← pderiv_map]
  simp

/-- Variable-multiplication monomial coefficients commute with extension of coefficients.
@isnad1 id=eq.0h5v.s9.89e7c9cfa96a from=translated src=- shape=4365e580 vocab=aece9c58
-/
theorem algebraMap_X_monomial_coeff (s b : Fin 3 →₀ ℕ) (i : Fin 3) :
    algebraMap K R ((X i * monomial s 1 : Poly K 3).coeff b) =
      (X i * monomial s 1 : MvPolynomial (Fin 3) R).coeff b := by
  rw [← coeff_map]
  simp

/-- The actual finite tensor multiplication is precisely the three-operator
variable multiplication in scalar-action coordinates.
@isnad1 id=eq.0h6v.s10.896387a26cd5 from=translated src=- shape=1a78f1c5 vocab=458f69e8
-/
theorem finiteMultiply_eq_auxiliaryOperatorMultiply (f : Fin 3 → R) (t : ℕ)
    (q : Sym (Fin 3) t → M) :
    finiteMultiply f t q = auxiliaryOperatorMultiply (fun i => scalarAction (K := K) (f i)) t q := by
  funext b
  rw [finiteMultiply_monomial_coefficients, auxiliaryOperatorMultiply_apply]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro i hi
  rw [scalarAction_apply, ← algebraMap_X_monomial_coeff (K := K)]
  exact algebraMap_smul R _ _

end Algebra
end ChoppedPlane.LaurentPairing
