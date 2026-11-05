module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.FiniteAuxiliaryMaps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Coefficient grading of the finite cross substitution

Only the coefficient-module grading is used.  Each entry of the cross row
acts in degree one, so a substituted auxiliary monomial of degree `n` acts
in coefficient degree `n`.  This argument works for Laurent coefficient
modules without choosing bases in the cubic quotient ring.
-/

noncomputable section
namespace ChoppedPlane.FiniteCech

open MvPolynomial SymmetricDerivative
open scoped TensorProduct
variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Every coefficient belongs to one fixed additive homogeneous component.-/
def CoefficientGrade (G : ℤ → AddSubgroup M) (k : ℤ)
    (P : AuxTensor (R := R) (M := M)) : Prop :=
  ∀ s : Fin 3 →₀ ℕ, tensorCoefficients P s ∈ G k

/--
@isnad1 id=coeffici.0h4v.s6.21ba4b36f288 from=translated src=- shape=8c1b803c vocab=75f7e23e
-/
lemma coefficientGrade_zero (G : ℤ → AddSubgroup M) (k : ℤ) :
    CoefficientGrade G k (0 : AuxTensor (R := R) (M := M)) := by
  intro s
  simp only [map_zero, Finsupp.zero_apply]
  exact (G k).zero_mem

/--
@isnad1 id=coeffici.1h7v.s7.038672b87f51 from=translated src=- shape=dc900014 vocab=91ea7b61
-/
lemma coefficientGrade_sum {ι : Type*} (G : ℤ → AddSubgroup M) (k : ℤ)
    (s : Finset ι) (P : ι → AuxTensor (R := R) (M := M))
    (hP : ∀ i ∈ s, CoefficientGrade G k (P i)) :
    CoefficientGrade G k (∑ i ∈ s, P i) := by
  intro e
  simp only [map_sum, Finsupp.finsetSum_apply]
  exact (G k).sum_mem fun i hi => hP i hi e

/--
@isnad1 id=coeffici.1h5v.s8.834f95d4f77b from=translated src=- shape=a6727050 vocab=ee5760cb
-/
lemma coefficientGrade_constant (G : ℤ → AddSubgroup M) (k : ℤ)
    (m : M) (hm : m ∈ G k) :
    CoefficientGrade G k ((monomial 0 1 : Aux R) ⊗ₜ[R] m) := by
  intro s
  rw [tensorCoefficients_monomial]
  by_cases hs : (0 : Fin 3 →₀ ℕ) = s
  · subst s
    simpa using hm
  · simp only [Finsupp.single_apply, ite_eq_right hs]
    exact (G k).zero_mem

/-- Iterated multiplication is the ordinary power of the linear form.
@isnad1 id=eq.0h6v.s9.0a096bc48e94 from=translated src=- shape=7e700018 vocab=e3ce4728
-/
lemma tensorMultiplyLinear_iterate_tmul (f : Fin 3 → R) (d : ℕ)
    (P : Aux R) (m : M) :
    (tensorMultiplyLinear f)^[d] (P ⊗ₜ[R] m) =
      (linearForm f ^ d * P) ⊗ₜ[R] m := by
  induction d with
  | zero => simp
  | succ d hd =>
    rw [Function.iterate_succ_apply', hd]
    change (linearForm f * (linearForm f ^ d * P)) ⊗ₜ[R] m = _
    apply congrArg (fun Q : Aux R => Q ⊗ₜ[R] m)
    rw [pow_succ]
    ring

/-- Synthesis of a fixed-degree coefficient vector preserves its coefficient component.
@isnad1 id=coeffici.1h6v.s6.2e82bccdf323 from=translated src=- shape=6849d67a vocab=f3613b30
-/
theorem coefficientGrade_synthesis (G : ℤ → AddSubgroup M) (k : ℤ) (n : ℕ)
    (c : Sym (Fin 3) n → M) (hc : ∀ i, c i ∈ G k) :
    CoefficientGrade G k (homogeneousTensorSynthesis (R := R) n c) := by
  intro s
  change tensorCoefficients
    (∑ i, (monomial (homogeneousTensorExponent n i) 1 : Aux R) ⊗ₜ[R] c i) s ∈ _
  simp only [map_sum, Finsupp.finsetSum_apply, tensorCoefficients_monomial]
  apply (G k).sum_mem
  intro i hi
  by_cases heq : homogeneousTensorExponent n i = s
  · simp only [Finsupp.single_apply, heq, ite_true]
    exact hc i
  · simp only [Finsupp.single_apply, ite_eq_right heq]
    exact (G k).zero_mem

/-- The cross matrix inherits degree-one action from its three coefficients.
@isnad1 id=mem.2h10v.s8.f81f6077239d from=translated src=- shape=3cf14bd3 vocab=06a0b037
-/
theorem crossMatrix_degree_one (G : ℤ → AddSubgroup M) (u v z : R)
    (hf : ∀ k i m, m ∈ G k → (![u,v,z] : Fin 3 → R) i • m ∈ G (k + 1)) :
    ∀ k i j m, m ∈ G k → crossMatrix u v z i j • m ∈ G (k + 1) := by
  intro k i j m hm
  have hu : u • m ∈ G (k + 1) := by simpa using hf k 0 m hm
  have hv : v • m ∈ G (k + 1) := by simpa using hf k 1 m hm
  have hz : z • m ∈ G (k + 1) := by simpa using hf k 2 m hm
  fin_cases i <;> fin_cases j <;> simp [crossMatrix, neg_smul] <;> assumption

end ChoppedPlane.FiniteCech
