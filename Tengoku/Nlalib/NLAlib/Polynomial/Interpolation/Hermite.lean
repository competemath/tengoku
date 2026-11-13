import Tengoku.Seed.LinearAlgebra.Lagrange
import Tengoku.Seed.Analysis.Calculus.Deriv.Polynomial
import Tengoku.Seed.Tactic.ComputeDegree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Finite Hermite interpolation with double nodes

The explicit cardinal formula matches a value and first derivative at every distinct
node. It is the algebraic interpolant (AQ3) used by the derivative remainder of Gauss
quadrature, and is independent of probability measures or matrix representations.
-/

noncomputable section
open Polynomial Finset Set

namespace Lagrange

variable {ι : Type*} [DecidableEq ι]

/-- The cardinal polynomial for a function value in double-node Hermite interpolation:
`(1−2ℓᵢ′(vᵢ)(X−vᵢ))ℓᵢ²`. Source: finite Hermite formula (AQ3).-/
def hermiteValueBasis (s : Finset ι) (v : ι → ℝ) (i : ι) : ℝ[X] :=
  (1 - C (2 * (Lagrange.basis s v i).derivative.eval (v i)) * (X - C (v i))) *
    Lagrange.basis s v i ^ 2

/-- The cardinal polynomial for a first derivative in double-node Hermite interpolation:
`(X−vᵢ)ℓᵢ²`. Source: finite Hermite formula (AQ3).-/
def hermiteDerivativeBasis (s : Finset ι) (v : ι → ℝ) (i : ι) : ℝ[X] :=
  (X - C (v i)) * Lagrange.basis s v i ^ 2

/-- The explicit finite Hermite interpolant matching values `yᵢ` and derivatives `dᵢ`
at the distinct nodes `vᵢ`. It is zero for an empty interpolation set.
Source: operator derivations, (AQ3).-/
def hermiteInterpolate (s : Finset ι) (v y d : ι → ℝ) : ℝ[X] :=
  ∑ i ∈ s, (C (y i) * hermiteValueBasis s v i + C (d i) * hermiteDerivativeBasis s v i)

/-- Every term in the finite Hermite formula has degree at most twice the number of
nodes minus one. Source: operator derivations, (AQ3).
@isnad1 id=le.2h6v.s7.f1a9636ddaa2 from=translated src=- shape=05743c2f vocab=470ea911
-/
theorem natDegree_hermite_term_le {s : Finset ι} {v : ι → ℝ} (hv : InjOn v s)
    (y d : ι → ℝ) {i : ι} (hi : i ∈ s) :
    (C (y i) * hermiteValueBasis s v i + C (d i) * hermiteDerivativeBasis s v i).natDegree ≤
      2 * s.card - 1 := by
  have hs : 0 < s.card := card_pos.mpr ⟨i, hi⟩
  have hb := natDegree_basis hv hi
  have hv₁ : (1 - C (2 * (Lagrange.basis s v i).derivative.eval (v i)) *
      (X - C (v i)) : ℝ[X]).natDegree ≤ 1 := by compute_degree
  have hv₂ : (X - C (v i) : ℝ[X]).natDegree ≤ 1 := by compute_degree
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_C_mul_le _ _).trans
    apply (natDegree_mul_le.trans (Nat.add_le_add_right hv₁ _)).trans
    rw [natDegree_pow, hb]
    omega
  · apply (natDegree_C_mul_le _ _).trans
    apply (natDegree_mul_le.trans (Nat.add_le_add_right hv₂ _)).trans
    rw [natDegree_pow, hb]
    omega

/-- A finite Hermite interpolant on a nonempty distinct-node family has degree strictly
below twice the number of nodes. Source: operator derivations, (AQ3).
@isnad1 id=lt.2h5v.s6.df3bb3610f14 from=translated src=- shape=13633061 vocab=54af496c
-/
theorem degree_hermiteInterpolate_lt {s : Finset ι} (hs : s.Nonempty) {v : ι → ℝ}
    (hv : InjOn v s) (y d : ι → ℝ) :
    (hermiteInterpolate s v y d).degree < (2 * s.card : ℕ) := by
  unfold hermiteInterpolate
  apply (degree_sum_le _ _).trans_lt
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro i hi
  apply (degree_le_natDegree).trans_lt
  exact_mod_cast (lt_of_le_of_lt (natDegree_hermite_term_le hv y d hi)
    (by have := hs.card_pos; omega : 2 * s.card - 1 < 2 * s.card))

/-- A Hermite value cardinal polynomial is one at its own node and zero at the others.
@isnad1 id=eq.3h5v.s6.0aec907a9f81 from=translated src=- shape=84ce08bc vocab=1b4ab2fb
-/
theorem eval_hermiteValueBasis {s : Finset ι} {v : ι → ℝ} (hv : InjOn v s)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    (hermiteValueBasis s v i).eval (v j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [hermiteValueBasis, eval_basis_self hv hi]
  · simp [hermiteValueBasis, hij, eval_basis_of_ne hij hj]

/-- A Hermite derivative cardinal polynomial vanishes at every node.
@isnad1 id=eq.3h5v.s6.91ea879776c8 from=translated src=- shape=bd14d99d vocab=875d32c0
-/
theorem eval_hermiteDerivativeBasis {s : Finset ι} {v : ι → ℝ} (hv : InjOn v s)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    (hermiteDerivativeBasis s v i).eval (v j) = 0 := by
  by_cases hij : i = j
  · subst j
    simp [hermiteDerivativeBasis, eval_basis_self hv hi]
  · simp [hermiteDerivativeBasis, eval_basis_of_ne hij hj]

/-- The derivative of a Hermite value cardinal polynomial vanishes at every node.
@isnad1 id=eq.3h5v.s7.b216aa8bdd3d from=translated src=- shape=37ef9c2f vocab=9c1a64a0
-/
theorem eval_derivative_hermiteValueBasis {s : Finset ι} {v : ι → ℝ} (hv : InjOn v s)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    (hermiteValueBasis s v i).derivative.eval (v j) = 0 := by
  by_cases hij : i = j
  · subst j
    simp [hermiteValueBasis, derivative_mul, derivative_sub, derivative_pow,
      eval_basis_self hv hi]
  · simp [hermiteValueBasis, derivative_mul, derivative_sub, derivative_pow,
      eval_basis_of_ne hij hj]

/-- A Hermite derivative cardinal polynomial has derivative one at its own node and
zero at every other node.
@isnad1 id=eq.3h5v.s7.541e93671e9f from=translated src=- shape=a6b82157 vocab=b3108d7c
-/
theorem eval_derivative_hermiteDerivativeBasis {s : Finset ι} {v : ι → ℝ} (hv : InjOn v s)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    (hermiteDerivativeBasis s v i).derivative.eval (v j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [hermiteDerivativeBasis, derivative_mul, derivative_sub, derivative_pow,
      eval_basis_self hv hi]
  · simp [hermiteDerivativeBasis, derivative_mul, derivative_sub, derivative_pow,
      hij, eval_basis_of_ne hij hj]

/-- The explicit finite Hermite interpolant matches all specified function values.
@isnad1 id=eq.2h6v.s6.dd4d7fe7726f from=translated src=- shape=ff9fc099 vocab=48b857bd
-/
theorem eval_hermiteInterpolate_at_node {s : Finset ι} {v : ι → ℝ} (hv : InjOn v s)
    (y d : ι → ℝ) {j : ι} (hj : j ∈ s) :
    (hermiteInterpolate s v y d).eval (v j) = y j := by
  simp only [hermiteInterpolate, eval_finsetSum, eval_add, eval_mul, eval_C]
  rw [sum_eq_single j]
  · rw [eval_hermiteValueBasis hv hj hj, eval_hermiteDerivativeBasis hv hj hj]
    simp
  · intro i hi hij
    rw [eval_hermiteValueBasis hv hi hj, eval_hermiteDerivativeBasis hv hi hj, ite_eq_right hij]
    simp
  · exact fun h => (h hj).elim

/-- The explicit finite Hermite interpolant matches all specified first derivatives.
@isnad1 id=eq.2h6v.s7.a86e794230b4 from=translated src=- shape=eb485766 vocab=d35a557a
-/
theorem eval_derivative_hermiteInterpolate_at_node {s : Finset ι} {v : ι → ℝ}
    (hv : InjOn v s) (y d : ι → ℝ) {j : ι} (hj : j ∈ s) :
    (hermiteInterpolate s v y d).derivative.eval (v j) = d j := by
  simp only [hermiteInterpolate, derivative_sum, derivative_add, derivative_C_mul,
    eval_finsetSum, eval_add, eval_mul, eval_C]
  rw [sum_eq_single j]
  · rw [eval_derivative_hermiteValueBasis hv hj hj,
      eval_derivative_hermiteDerivativeBasis hv hj hj]
    simp
  · intro i hi hij
    rw [eval_derivative_hermiteValueBasis hv hi hj,
      eval_derivative_hermiteDerivativeBasis hv hi hj, ite_eq_right hij]
    simp
  · exact fun h => (h hj).elim

end Lagrange
