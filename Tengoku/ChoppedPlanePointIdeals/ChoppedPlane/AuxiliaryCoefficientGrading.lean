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

lemma coefficientGrade_zero (G : ℤ → AddSubgroup M) (k : ℤ) :
    CoefficientGrade G k (0 : AuxTensor (R := R) (M := M)) := by
  intro s
  simp only [map_zero, Finsupp.zero_apply]
  exact (G k).zero_mem

lemma coefficientGrade_sum {ι : Type*} (G : ℤ → AddSubgroup M) (k : ℤ)
    (s : Finset ι) (P : ι → AuxTensor (R := R) (M := M))
    (hP : ∀ i ∈ s, CoefficientGrade G k (P i)) :
    CoefficientGrade G k (∑ i ∈ s, P i) := by
  intro e
  simp only [map_sum, Finsupp.finsetSum_apply]
  exact (G k).sum_mem fun i hi => hP i hi e

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

/-- Iterated multiplication is the ordinary power of the linear form.-/
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

/-- Synthesis of a fixed-degree coefficient vector preserves its coefficient component.-/
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

/-- The cross matrix inherits degree-one action from its three coefficients.-/
theorem crossMatrix_degree_one (G : ℤ → AddSubgroup M) (u v z : R)
    (hf : ∀ k i m, m ∈ G k → (![u,v,z] : Fin 3 → R) i • m ∈ G (k + 1)) :
    ∀ k i j m, m ∈ G k → crossMatrix u v z i j • m ∈ G (k + 1) := by
  intro k i j m hm
  have hu : u • m ∈ G (k + 1) := by simpa using hf k 0 m hm
  have hv : v • m ∈ G (k + 1) := by simpa using hf k 1 m hm
  have hz : z • m ∈ G (k + 1) := by simpa using hf k 2 m hm
  fin_cases i <;> fin_cases j <;> simp [crossMatrix, neg_smul] <;> assumption

end ChoppedPlane.FiniteCech
