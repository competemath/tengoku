module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.SymmetricCoordinates
public import Tengoku.Seed.Data.Finsupp.Multiset
public import Tengoku.Seed.Data.Sym.Card
public import Tengoku.Seed.LinearAlgebra.FixedSubmodule

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
Finite coordinates for an actual auxiliary-homogeneous tensor polynomial.
The coefficient module is arbitrary: neither freeness nor flatness is needed.
The inverse map synthesizes a finite sum of genuine coefficient-one monomials.
-/

noncomputable section
namespace ChoppedPlane.SymmetricDerivative
open MvPolynomial
open scoped TensorProduct
variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Symmetric variable indices encode exactly the exponent vectors of degree `n`.
This equivalence depends on the indices alone, independently of the base ring.-/
def homogeneousTensorExponentEquiv (n : ℕ) :
    Sym (Fin 3) n ≃ {s : Fin 3 →₀ ℕ // s.degree = n} :=
  Sym.equivNatSum (Fin 3) n

/-- The exponent vector attached to one finite symmetric index.-/
def homogeneousTensorExponent (n : ℕ) (i : Sym (Fin 3) n) : Fin 3 →₀ ℕ :=
  (homogeneousTensorExponentEquiv n i).val

/--
@isnad1 id=eq.0h2v.s7.379cc210a025 from=translated src=- shape=3385ddcd vocab=4cfdd21d
-/
@[simp] theorem homogeneousTensorExponent_degree (n : ℕ) (i : Sym (Fin 3) n) :
    (homogeneousTensorExponent n i).degree = n :=
  (homogeneousTensorExponentEquiv n i).property

/--
@isnad1 id=injectiv.0h1v.s4.dd817923afbe from=translated src=- shape=e24c25f9 vocab=1e691eba
-/
theorem homogeneousTensorExponent_injective (n : ℕ) :
    Function.Injective (homogeneousTensorExponent n) := by
  intro i j h
  apply (homogeneousTensorExponentEquiv n).injective
  exact Subtype.ext h

/--
@isnad1 id=ex.1h2v.s7.a847a7118965 from=translated src=- shape=dd5c372c vocab=4cfdd21d
-/
theorem exists_homogeneousTensorExponent (n : ℕ) (s : Fin 3 →₀ ℕ)
    (hs : s.degree = n) : ∃ i : Sym (Fin 3) n, homogeneousTensorExponent n i = s := by
  refine ⟨(homogeneousTensorExponentEquiv n).symm ⟨s,hs⟩, ?_⟩
  simp [homogeneousTensorExponent]

/-- The genuine submodule of tensors fixed by auxiliary degree-`n` extraction.-/
def homogeneousTensorSubmodule (n : ℕ) : Submodule R (AuxTensor (R := R) (M := M)) :=
  ((homogeneousComponent n).rTensor M).fixedSubmodule

/--
@isnad1 id=iff.0h4v.s8.6771fe92c37e from=translated src=- shape=c9c005bd vocab=a522de27
-/
@[simp] theorem mem_homogeneousTensorSubmodule (n : ℕ) (P : AuxTensor (R := R) (M := M)) :
    P ∈ homogeneousTensorSubmodule n ↔ TensorHomogeneous n P := Iff.rfl

/-- Read the finite degree-`n` coefficient vector from an actual tensor polynomial.-/
def homogeneousTensorCoefficientVector (n : ℕ) (P : AuxTensor (R := R) (M := M)) :
    Sym (Fin 3) n → M := fun i => tensorCoefficients P (homogeneousTensorExponent n i)

/-- Coefficient reading is an actual linear map on the full tensor module.-/
def homogeneousTensorCoefficientMap (n : ℕ) :
    AuxTensor (R := R) (M := M) →ₗ[R] (Sym (Fin 3) n → M) where
  toFun := homogeneousTensorCoefficientVector n
  map_add' P Q := by
    ext i
    simp [homogeneousTensorCoefficientVector]
  map_smul' r P := by
    ext i
    simp [homogeneousTensorCoefficientVector]

/--
@isnad1 id=eq.0h6v.s7.c705929b66f6 from=translated src=- shape=7b3be781 vocab=dd1b98e9
-/
@[simp] theorem homogeneousTensorCoefficientVector_tmul (n : ℕ) (P : Aux R)
    (m : M) (i : Sym (Fin 3) n) :
    homogeneousTensorCoefficientVector n (P ⊗ₜ[R] m) i =
      P.coeff (homogeneousTensorExponent n i) • m := by
  simp [homogeneousTensorCoefficientVector]

/-- Synthesize a tensor polynomial by the finite sum of its homogeneous monomials.-/
def homogeneousTensorSynthesis (n : ℕ) (c : Sym (Fin 3) n → M) :
    AuxTensor (R := R) (M := M) :=
  ∑ i, monomial (homogeneousTensorExponent n i) 1 ⊗ₜ[R] c i

/-- Finite monomial synthesis is linear in the module coefficients.-/
def homogeneousTensorSynthesisMap (n : ℕ) :
    (Sym (Fin 3) n → M) →ₗ[R] AuxTensor (R := R) (M := M) where
  toFun := homogeneousTensorSynthesis n
  map_add' c d := by
    simp [homogeneousTensorSynthesis, TensorProduct.tmul_add, Finset.sum_add_distrib]
  map_smul' r c := by
    simp [homogeneousTensorSynthesis, TensorProduct.tmul_smul, Finset.smul_sum]

/-- Each synthesized coefficient is exactly the coefficient supplied to it.
@isnad1 id=eq.0h4v.s5.ee27b7eed66a from=translated src=- shape=7a51fbf6 vocab=41de9925
-/
@[simp] theorem homogeneousTensorCoefficientVector_synthesis (n : ℕ)
    (c : Sym (Fin 3) n → M) :
    homogeneousTensorCoefficientVector n (homogeneousTensorSynthesis (R := R) n c) = c := by
  classical
  funext i
  simp only [homogeneousTensorCoefficientVector, homogeneousTensorSynthesis,
    map_sum, Finsupp.finsetSum_apply, tensorCoefficients_monomial, Finsupp.single_apply]
  simp only [(homogeneousTensorExponent_injective n).eq_iff,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end ChoppedPlane.SymmetricDerivative
