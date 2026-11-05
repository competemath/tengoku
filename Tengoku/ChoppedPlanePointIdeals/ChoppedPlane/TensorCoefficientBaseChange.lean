module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.SymmetricBaseChange
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.FiniteAuxiliaryMaps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Naturality of the actual auxiliary coefficient maps

The coefficient extension is the existing explicit semilinear tensor map.
Linear substitutions, multiplication and directional differentiation commute
with it. Reading and synthesizing the finite homogeneous coefficient vectors
then gives the literal chart transition diagrams, over arbitrary commutative
rings and arbitrary coefficient modules.
-/
noncomputable section
namespace ChoppedPlane.SymmetricDerivative
open MvPolynomial
open scoped TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S]
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
variable {σ : Type*} {θ : R →+* S}

/-- Auxiliary coefficient extension, using the canonical coefficientwise map.-/
abbrev auxCoefficientBaseChange (T : M →ₛₗ[θ] N) :
    (MvPolynomial σ R ⊗[R] M) →ₛₗ[θ] (MvPolynomial σ S ⊗[S] N) := tensorBaseChange T

/--
@isnad1 id=eq.0h9v.s11.a77412fadffb from=translated src=- shape=c57c8cbf vocab=f2e7a556
-/
@[simp] theorem auxCoefficientBaseChange_coefficients (T : M →ₛₗ[θ] N)
    (P : MvPolynomial σ R ⊗[R] M) (s : σ →₀ ℕ) :
    tensorCoefficients (auxCoefficientBaseChange T P) s = T (tensorCoefficients P s) :=
  tensorCoefficients_baseChange T P s

/--
@isnad1 id=eq.0h9v.s10.5617e20ad9d3 from=translated src=- shape=19d009ae vocab=471f0e8a
-/
@[simp] theorem auxCoefficientBaseChange_tmul (T : M →ₛₗ[θ] N)
    (P : MvPolynomial σ R) (m : M) :
    auxCoefficientBaseChange T (P ⊗ₜ[R] m) = MvPolynomial.map θ P ⊗ₜ[S] T m :=
  tensorBaseChange_tmul T P m

/-- A genuine auxiliary linear form commutes with scalar extension.
@isnad1 id=eq.0h4v.s8.19d9b18f82c1 from=translated src=- shape=8c72d956 vocab=55a8cbe6
-/
@[simp] theorem map_linearForm (θ : R →+* S) (f : Fin 3 → R) :
    MvPolynomial.map θ (linearForm f) = linearForm (fun i => θ (f i)) := by
  simp [linearForm]

/-- A genuine auxiliary linear substitution commutes with scalar extension.
@isnad1 id=eq.0h5v.s10.150f42f01844 from=translated src=- shape=a199b9bc vocab=17ac13ef
-/
theorem map_linearChange (θ : R →+* S) (A : Matrix (Fin 3) (Fin 3) R)
    (P : Aux R) :
    MvPolynomial.map θ (linearChange A P) =
      linearChange (A.map θ) (MvPolynomial.map θ P) := by
  have h : (MvPolynomial.map θ).comp (linearChange A).toRingHom =
      (linearChange (A.map θ)).toRingHom.comp (MvPolynomial.map θ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change MvPolynomial.map θ (linearChange A (C r)) =
        linearChange (A.map θ) (MvPolynomial.map θ (C r))
      simp only [linearChange_C, map_C]
    · intro i
      change MvPolynomial.map θ (linearChange A (X i)) =
        linearChange (A.map θ) (MvPolynomial.map θ (X i))
      simp only [linearChange_X, map_X, map_linearForm]
      rfl
  exact congrArg (fun f : Aux R →+* Aux S => f P) h

/-- Homogeneous coefficient reading is exactly coefficientwise scalar extension.
@isnad1 id=eq.0h8v.s10.3be87061e5f9 from=translated src=- shape=5e0a8437 vocab=c570cacf
-/
@[simp] theorem homogeneousTensorCoefficientVector_baseChange (T : M →ₛₗ[θ] N)
    (n : ℕ) (P : AuxTensor (R := R) (M := M)) :
    homogeneousTensorCoefficientVector n (tensorBaseChange T P) =
      fun i => T (homogeneousTensorCoefficientVector n P i) := by
  funext i
  exact tensorCoefficients_baseChange T P _

/-- Actual homogeneous tensor synthesis is natural under coefficient extension.
@isnad1 id=eq.0h8v.s10.7f4f2986ea6c from=translated src=- shape=3e1424d6 vocab=d19538f6
-/
@[simp] theorem tensorBaseChange_homogeneousSynthesis (T : M →ₛₗ[θ] N)
    (n : ℕ) (c : Sym (Fin 3) n → M) :
    tensorBaseChange T (homogeneousTensorSynthesis n c) =
      homogeneousTensorSynthesis n (fun i => T (c i)) := by
  simp only [homogeneousTensorSynthesis, map_sum, tensorBaseChange_tmul,
    map_monomial, map_one]

end ChoppedPlane.SymmetricDerivative

namespace ChoppedPlane.FiniteCech
open SymmetricDerivative

variable {R S : Type*} [CommRing R] [CommRing S]
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
variable {θ : R →+* S}

/-- Coefficient extension on the actual finite homogeneous coefficient vectors.-/
def finiteCoefficientBaseChange (T : M →ₛₗ[θ] N) (n : ℕ) :
    (Sym (Fin 3) n → M) →ₛₗ[θ] (Sym (Fin 3) n → N) where
  toFun c i := T (c i)
  map_add' c d := by ext i; exact T.map_add _ _
  map_smul' r c := by ext i; exact T.map_smulₛₗ _ _

/--
@isnad1 id=eq.0h9v.s8.dff7b0b7b17d from=translated src=- shape=4a474860 vocab=6c6aaaaa
-/
@[simp] theorem finiteCoefficientBaseChange_apply (T : M →ₛₗ[θ] N)
    (n : ℕ) (c : Sym (Fin 3) n → M) (i : Sym (Fin 3) n) :
    finiteCoefficientBaseChange T n c i = T (c i) := rfl

end ChoppedPlane.FiniteCech
