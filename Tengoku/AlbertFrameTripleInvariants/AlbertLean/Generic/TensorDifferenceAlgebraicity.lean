import Tengoku.Seed.Algebra.Algebra.Equiv
import Tengoku.Seed.Algebra.Polynomial.AlgebraMap
import Tengoku.Seed.Algebra.Polynomial.Degree.Operations
import Tengoku.Seed.Algebra.Polynomial.Monic
import Tengoku.Seed.Data.Nat.Choose.Sum
import Tengoku.Seed.LinearAlgebra.Basis.VectorSpace
import Tengoku.Seed.LinearAlgebra.TensorProduct.Associator
import Tengoku.Seed.LinearAlgebra.TensorProduct.Map
import Tengoku.Seed.RingTheory.TensorProduct.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms scalarRetraction_algebraMap` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms contractRight_tmul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms descentPolynomial_monic` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_monic_annihilator_of_tensorDifference_pow_eq_zero` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Nilpotent tensor difference implies algebraicity.  This is the first descent
lemma only; it assumes neither that the extension is algebraic nor
characteristic zero.
-/

noncomputable section
namespace AlbertLean.Generic.TensorDifferenceAlgebraicity

open scoped TensorProduct
open scoped BigOperators

universe u v
variable (H : Type u) (K : Type v) [Field H] [Field K] [Algebra H K]

/-- A chosen `H`-linear retraction of the scalar inclusion.-/
def scalarRetraction : K →ₗ[H] H :=
  (Algebra.linearMap H K).leftInverse

theorem scalarRetraction_algebraMap (x : H) :
    scalarRetraction H K (algebraMap H K x) = x := by
  apply LinearMap.leftInverse_apply_of_inj
  exact LinearMap.ker_eq_bot.mpr (algebraMap H K).injective

@[simp] theorem scalarRetraction_one : scalarRetraction H K 1 = 1 := by
  simpa using scalarRetraction_algebraMap H K 1

/-- Apply the chosen functional to the right tensor factor.-/
def contractRight : K ⊗[H] K →ₗ[H] K :=
  (TensorProduct.rid H K).toLinearMap.comp
    (TensorProduct.map LinearMap.id (scalarRetraction H K))

@[simp] theorem contractRight_tmul (x y : K) :
    contractRight H K (x ⊗ₜ[H] y) =
      (scalarRetraction H K y) • x := by
  simp [contractRight]

/-- The polynomial obtained by contracting the binomial expansion of
`(a ⊗ 1 - 1 ⊗ a)^n`.  The antidiagonal indexing avoids truncated subtraction.-/
def descentPolynomial (a : K) (n : ℕ) : Polynomial H :=
  ∑ m ∈ Finset.antidiagonal n,
    Polynomial.monomial m.1
      (n.choose m.1 • scalarRetraction H K ((-a) ^ m.2))

/-- The coefficient at degree `n` is one and all other antidiagonal terms have
smaller degree.-/
theorem descentPolynomial_monic (a : K) (n : ℕ) :
    (descentPolynomial H K a n).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
  · unfold descentPolynomial
    apply Polynomial.natDegree_le_of_degree_le
    apply (Polynomial.degree_sum_le _ _).trans
    apply Finset.sup_le
    intro m hm
    exact Polynomial.degree_le_of_natDegree_le
      ((Polynomial.natDegree_monomial_le _).trans
        (Nat.le.intro (Finset.mem_antidiagonal.mp hm)))
  · classical
    simp only [descentPolynomial, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single (n, 0)]
    · simp
    · intro m hm hne
      have hi : m.1 ≠ n := by
        intro hi
        apply hne
        apply Prod.ext hi
        have hs := Finset.mem_antidiagonal.mp hm
        omega
      simp [Polynomial.coeff_monomial, hi]
    · simp [Finset.mem_antidiagonal]

/-- Evaluation is the contraction of the corresponding tensor binomial sum.-/
theorem eval_descentPolynomial (a : K) (n : ℕ) :
    (descentPolynomial H K a n).eval₂ (algebraMap H K) a =
      contractRight H K
        ((a ⊗ₜ[H] (1 : K) - (1 : K) ⊗ₜ[H] a) ^ n) := by
  rw [sub_eq_add_neg, (Commute.all (a ⊗ₜ[H] (1 : K)) (-((1 : K) ⊗ₜ[H] a))).add_pow']
  rw [← TensorProduct.tmul_neg]
  simp only [descentPolynomial, map_sum, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_monomial]
  apply Finset.sum_congr rfl
  intro m hm
  rcases m with ⟨i, j⟩
  rw [(contractRight H K).map_smul_of_tower (n.choose i)]
  simp only [Algebra.TensorProduct.tmul_pow, one_pow,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    contractRight_tmul, Algebra.smul_def, map_mul]
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- If `a ⊗ 1 - 1 ⊗ a` is nilpotent, then `a` is algebraic over the base
field.  No algebraicity or characteristic hypothesis is assumed.-/
theorem exists_monic_annihilator_of_tensorDifference_pow_eq_zero (a : K) (n : ℕ)
    (hpow : (a ⊗ₜ[H] (1 : K) - (1 : K) ⊗ₜ[H] a) ^ n = 0) :
    ∃ p : Polynomial H, p.Monic ∧ Polynomial.aeval a p = 0 := by
  refine ⟨descentPolynomial H K a n,
    descentPolynomial_monic H K a n, ?_⟩
  rw [Polynomial.aeval_def, eval_descentPolynomial H K a n, hpow, map_zero]

end AlbertLean.Generic.TensorDifferenceAlgebraicity
