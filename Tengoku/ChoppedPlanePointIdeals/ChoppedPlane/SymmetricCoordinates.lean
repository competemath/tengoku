module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.SymmetricDerivative
public import Tengoku.Seed.LinearAlgebra.DirectSum.Finsupp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Coefficients of module-valued symmetric powers

The tensor description of the directional kernel has unique, finite module
coefficients. In auxiliary degree `n` these are indexed by the `n + 1` binary
monomials. No freeness assumption on the coefficient module is required.
-/

noncomputable section
namespace ChoppedPlane.SymmetricDerivative
open MvPolynomial
open scoped TensorProduct
variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {σ : Type*}

/-- Coefficient identification for module-valued multivariate polynomials.-/
def tensorCoefficients : (MvPolynomial σ R ⊗[R] M) ≃ₗ[R] ((σ →₀ ℕ) →₀ M) := by
  classical
  exact (basisMonomials σ R).repr.rTensor M ≪≫ₗ
    TensorProduct.finsuppScalarLeft R M (σ →₀ ℕ)

@[simp] theorem tensorCoefficients_tmul (P : MvPolynomial σ R) (m : M) (s : σ →₀ ℕ) :
    tensorCoefficients (P ⊗ₜ[R] m) s = P.coeff s • m := by
  classical
  change TensorProduct.finsuppScalarLeft R M (σ →₀ ℕ)
    ((basisMonomials σ R).repr P ⊗ₜ[R] m) s = _
  rw [TensorProduct.finsuppScalarLeft_apply_tmul_apply]
  rfl

@[simp] theorem tensorCoefficients_monomial (s : σ →₀ ℕ) (m : M) :
    tensorCoefficients ((monomial s 1 : MvPolynomial σ R) ⊗ₜ[R] m) =
      Finsupp.single s m := by
  classical
  ext t
  simp [coeff_monomial, Finsupp.single_apply, ite_smul]

@[simp] theorem tensorCoefficients_symm_single (s : σ →₀ ℕ) (m : M) :
    tensorCoefficients.symm (Finsupp.single s m) =
      (monomial s 1 : MvPolynomial σ R) ⊗ₜ[R] m := by
  apply tensorCoefficients.injective
  simp

/-- Finite tensor sums are read coefficientwise.-/
@[simp] theorem tensorCoefficients_sum {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ R ⊗[R] M) (α : σ →₀ ℕ) :
    tensorCoefficients (∑ j ∈ s, P j) α = ∑ j ∈ s, tensorCoefficients (P j) α := by
  simp only [map_sum, Finsupp.finsetSum_apply]

/-- Every module-valued polynomial is its finite sum of coefficient monomials.-/
theorem tensor_as_sum_monomials (P : MvPolynomial σ R ⊗[R] M) :
    P = (tensorCoefficients P).sum (fun s m => (monomial s 1) ⊗ₜ[R] m) := by
  have h : (tensorCoefficients P).sum (fun s m => Finsupp.single s m) =
      tensorCoefficients P := Finsupp.sum_single _
  apply_fun (tensorCoefficients (R := R) (M := M) (σ := σ)).symm at h
  simp only [Finsupp.sum, map_sum, tensorCoefficients_symm_single,
    LinearEquiv.symm_apply_apply] at h
  exact h.symm

/-- The exponent of the `j`th degree-`n` binary monomial.-/
def binaryExponent (n : ℕ) (j : Fin (n + 1)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 j.val + Finsupp.single 1 (n - j.val)

@[simp] theorem binaryExponent_zero (n : ℕ) (j : Fin (n + 1)) :
    binaryExponent n j 0 = j.val := by simp [binaryExponent]

@[simp] theorem binaryExponent_one (n : ℕ) (j : Fin (n + 1)) :
    binaryExponent n j 1 = n - j.val := by simp [binaryExponent]

@[simp] theorem binaryExponent_degree (n : ℕ) (j : Fin (n + 1)) :
    (binaryExponent n j).degree = n := by
  simp only [binaryExponent, map_add, Finsupp.degree_single]
  omega

theorem binaryExponent_injective (n : ℕ) : Function.Injective (binaryExponent n) := by
  intro i j h
  apply Fin.ext
  simpa using congrArg (fun s : Fin 2 →₀ ℕ => s 0) h

theorem binary_degree (s : Fin 2 →₀ ℕ) : s.degree = s 0 + s 1 := by
  change s.sum (fun _ n => n) = _
  rw [Finsupp.sum_fintype]
  · simp [Fin.sum_univ_two]
  · simp

/-- Every degree-`n` binary exponent has a unique index between zero and `n`.-/
theorem exists_binaryExponent (n : ℕ) (s : Fin 2 →₀ ℕ) (hs : s.degree = n) :
    ∃ j : Fin (n + 1), binaryExponent n j = s := by
  have hsum : s 0 + s 1 = n := (binary_degree s).symm.trans hs
  refine ⟨⟨s 0, by omega⟩, ?_⟩
  ext i
  fin_cases i
  · simp
  · change binaryExponent n ⟨s 0, _⟩ (1 : Fin 2) = s 1
    rw [binaryExponent_one]
    change n - s 0 = s 1
    omega

/-- The finite coefficient vector of a degree-`n` binary module polynomial.-/
def binaryCoefficients (n : ℕ) (P : BinaryTensor (R := R) (M := M)) : Fin (n + 1) → M :=
  fun j => tensorCoefficients P (binaryExponent n j)

/-- Synthesize a binary symmetric tensor from its finite coefficient vector.-/
def binarySynthesis (n : ℕ) (c : Fin (n + 1) → M) : BinaryTensor (R := R) (M := M) :=
  ∑ j, monomial (binaryExponent n j) 1 ⊗ₜ[R] c j

@[simp] theorem binaryCoefficients_synthesis (n : ℕ) (c : Fin (n + 1) → M) :
    binaryCoefficients n (binarySynthesis (R := R) n c) = c := by
  classical
  funext j
  simp only [binaryCoefficients, binarySynthesis, map_sum, Finsupp.finsetSum_apply,
    tensorCoefficients_monomial, Finsupp.single_apply]
  simp only [(binaryExponent_injective n).eq_iff, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- The binary monomial corresponding to its finite index is the expected product of powers.-/
theorem binaryExponent_monomial (n : ℕ) (j : Fin (n + 1)) :
    (monomial (binaryExponent n j) 1 : Binary R) = X 0 ^ j.val * X 1 ^ (n - j.val) := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul]
  rfl

/-- A degree-`n` symmetric expression in the two kernel linear forms.-/
def kernelSynthesis (A : Matrix (Fin 3) (Fin 3) R) (n : ℕ) (c : Fin (n + 1) → M) :
    AuxTensor (R := R) (M := M) :=
  ∑ j, (linearForm (A 1) ^ j.val * linearForm (A 2) ^ (n - j.val)) ⊗ₜ[R] c j

/-- The abstract binary kernel embedding is the explicit finite symmetric expression.-/
theorem kernelEmbedding_synthesis (A : Matrix (Fin 3) (Fin 3) R)
    (n : ℕ) (c : Fin (n + 1) → M) :
    kernelEmbedding A (binarySynthesis n c) = kernelSynthesis A n c := by
  simp only [binarySynthesis, kernelSynthesis, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change linearChange A (binaryEmbedding (monomial (binaryExponent n j) 1)) ⊗ₜ[R] c j = _
  rw [binaryExponent_monomial, map_mul, map_pow, map_pow]
  have hx0 : binaryEmbedding (X 0 : Binary R) = (X 1 : Aux R) := by simp [binaryEmbedding]
  have hx1 : binaryEmbedding (X 1 : Binary R) = (X 2 : Aux R) := by simp [binaryEmbedding]
  rw [hx0, hx1, map_mul, map_pow, map_pow, linearChange_X, linearChange_X]

/-- The finite symmetric coefficient vector is unique.-/
theorem kernelSynthesis_injective (A B : Matrix (Fin 3) (Fin 3) R) (hAB : A * B = 1)
    (n : ℕ) : Function.Injective (kernelSynthesis (M := M) A n) := by
  intro c c' h
  have h' := congrArg (kernelCoordinates (M := M) B) h
  rw [← kernelEmbedding_synthesis, ← kernelEmbedding_synthesis,
    kernelCoordinates_embedding A B hAB, kernelCoordinates_embedding A B hAB] at h'
  have hc := congrArg (binaryCoefficients (R := R) n) h'
  simpa using hc

variable {K : Type*} [Field K] [CharZero K] [Algebra K R]
include K

end ChoppedPlane.SymmetricDerivative
