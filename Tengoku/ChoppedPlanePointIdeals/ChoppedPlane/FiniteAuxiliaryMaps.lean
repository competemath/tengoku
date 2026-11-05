module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.FiniteCechDuality
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.HomogeneousTensorCoordinates
public import Tengoku.Seed.RingTheory.MvPolynomial.EulerIdentity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# The actual finite auxiliary coefficient maps

These maps are coefficient forms of tensor multiplication, directional
differentiation and the cross substitution, indexed by finite symmetric
powers.  Their exactness comes from the explicit unit-chart calculations.
-/

noncomputable section
namespace ChoppedPlane.FiniteCech

open MvPolynomial SymmetricDerivative
open scoped TensorProduct

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/--
@isnad1 id=tensorho.1h5v.s7.8a54ddd2cb5f from=translated src=- shape=20ca4d1e vocab=69b41a80
-/
lemma tensorHomogeneous_tmul {n : ℕ} {P : Aux R} (hP : P.IsHomogeneous n) (m : M) :
    TensorHomogeneous n (P ⊗ₜ[R] m) := by
  change ((homogeneousComponent n).rTensor M) (P ⊗ₜ[R] m) = _
  simp only [LinearMap.rTensor_tmul, homogeneousComponent_eq_self hP]

/--
@isnad1 id=tensorho.1h6v.s7.b703f165f157 from=translated src=- shape=c1b6c1d2 vocab=28e9f995
-/
lemma tensorHomogeneous_sum {ι : Type*} (s : Finset ι)
    {n : ℕ} (P : ι → AuxTensor (R := R) (M := M))
    (hP : ∀ i ∈ s, TensorHomogeneous n (P i)) : TensorHomogeneous n (∑ i ∈ s, P i) := by
  change ((homogeneousComponent n).rTensor M) _ = _
  simp only [map_sum]
  exact Finset.sum_congr rfl hP

/-- Finite coefficient form of homogeneous cross substitution.-/
def finiteCross (A : Matrix (Fin 3) (Fin 3) R) (n : ℕ) :
    (Sym (Fin 3) n → M) →ₗ[R] (Sym (Fin 3) n → M) :=
  (homogeneousTensorCoefficientMap n).comp
    ((tensorChange A).comp (homogeneousTensorSynthesisMap n))

/-- Finite coefficient form of multiplication by the actual auxiliary linear form.-/
def finiteMultiply (f : Fin 3 → R) (n : ℕ) :
    (Sym (Fin 3) n → M) →ₗ[R] (Sym (Fin 3) (n + 1) → M) :=
  (homogeneousTensorCoefficientMap (n + 1)).comp
    ((tensorMultiplyLinear f).comp (homogeneousTensorSynthesisMap n))

/-- Finite coefficient form of directional differentiation.-/
def finiteDirectional (f : Fin 3 → R) (n : ℕ) :
    (Sym (Fin 3) (n + 1) → M) →ₗ[R] (Sym (Fin 3) n → M) :=
  (homogeneousTensorCoefficientMap n).comp
    ((tensorDirectional f).comp (homogeneousTensorSynthesisMap (n + 1)))

/-- Each finite cross entry is the literal coefficient of the substituted monomial.
@isnad1 id=eq.0h6v.s10.6b12b6370d39 from=translated src=- shape=96312afe vocab=fa7fb299
-/
theorem finiteCross_apply (A : Matrix (Fin 3) (Fin 3) R) (n : ℕ)
    (c : Sym (Fin 3) n → M) (j : Sym (Fin 3) n) :
    finiteCross A n c j = ∑ i : Sym (Fin 3) n,
      (linearChange A (monomial (homogeneousTensorExponent n i) 1)).coeff
        (homogeneousTensorExponent n j) • c i := by
  change tensorCoefficients (((linearChange A).toLinearMap.rTensor M)
    (∑ i, (monomial (homogeneousTensorExponent n i) 1 : Aux R) ⊗ₜ[R] c i))
      (homogeneousTensorExponent n j) = _
  simp only [map_sum, LinearMap.rTensor_tmul, Finsupp.finsetSum_apply,
    tensorCoefficients_tmul, AlgHom.toLinearMap_apply]

namespace CrossPresentation

variable {u v z : R} (T : CrossPresentation u v z)
include T

end CrossPresentation
end ChoppedPlane.FiniteCech
