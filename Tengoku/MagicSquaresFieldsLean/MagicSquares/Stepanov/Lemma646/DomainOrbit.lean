import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.DomainInvariant
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
import Tengoku.Seed.Algebra.Polynomial.BigOperators
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

/-!
# Root-of-unity orbit products over an integral domain

This is the polynomial-coefficient version of the orbit construction on
LN97 p. 302.  The eventual application is `R = F_q[X]`.
-/

variable {R : Type*} [CommRing R] [IsDomain R]

noncomputable def domainOrbitFactor
    (zeta : R) (A : Polynomial R) (j : ℕ) : Polynomial R :=
  A.comp (C (zeta ^ j) * X)

noncomputable def domainOrbitProduct
    (m : ℕ) (zeta : R) (A : Polynomial R) : Polynomial R :=
  ∏ j ∈ Finset.range m, domainOrbitFactor zeta A j

omit [IsDomain R] in
/--
@isnad1 id=eq.0h3v.s5.4daa242786b5 from=translated src=- shape=26e5eae9 vocab=bb9095e2
-/
@[simp]
theorem domainOrbitFactor_zero (zeta : R) (A : Polynomial R) :
    domainOrbitFactor zeta A 0 = A := by
  simp [domainOrbitFactor]

omit [IsDomain R] in
/--
@isnad1 id=eq.0h4v.s7.01a9c08611ea from=translated src=- shape=7b73ce7f vocab=1fdd5a4a
-/
theorem domainOrbitFactor_comp_scale
    (zeta : R) (A : Polynomial R) (j : ℕ) :
    (domainOrbitFactor zeta A j).comp (C zeta * X) =
      domainOrbitFactor zeta A (j + 1) := by
  simp [domainOrbitFactor, Polynomial.comp_assoc, pow_succ]
  ring_nf

omit [IsDomain R] in
/--
@isnad1 id=eq.1h4v.s5.efb69b43d004 from=translated src=- shape=86f5c142 vocab=caea5cc5
-/
theorem domainOrbitFactor_period
    {m : ℕ} {zeta : R}
    (hzeta : IsPrimitiveRoot zeta m)
    (A : Polynomial R) :
    domainOrbitFactor zeta A m = domainOrbitFactor zeta A 0 := by
  simp [domainOrbitFactor, hzeta.pow_eq_one]

/--
@isnad1 id=eq.2h3v.s6.de5e3bce627d from=translated src=- shape=82e269aa vocab=825b8f9f
-/
theorem domain_prod_range_shift_eq
    {M : Type*} [CommMonoidWithZero M] [IsRightCancelMulZero M]
    (m : ℕ) (f : ℕ → M)
    (h0 : f 0 ≠ 0)
    (hperiod : f m = f 0) :
    (∏ j ∈ Finset.range m, f (j + 1)) =
      ∏ j ∈ Finset.range m, f j := by
  have hsucc := Finset.prod_range_succ f m
  have hsucc' := Finset.prod_range_succ' f m
  have hmul :
      (∏ j ∈ Finset.range m, f (j + 1)) * f 0 =
        (∏ j ∈ Finset.range m, f j) * f 0 := by
    calc
      (∏ j ∈ Finset.range m, f (j + 1)) * f 0 =
          ∏ j ∈ Finset.range (m + 1), f j := hsucc'.symm
      _ = (∏ j ∈ Finset.range m, f j) * f m := hsucc
      _ = (∏ j ∈ Finset.range m, f j) * f 0 := by rw [hperiod]
  exact mul_right_cancel₀ h0 hmul

/--
@isnad1 id=eq.1h4v.s7.d2d59b270e4e from=translated src=- shape=9ed9ff9a vocab=9e183f87
-/
theorem domainOrbitProduct_scale_invariant
    {m : ℕ} {zeta : R}
    (hzeta : IsPrimitiveRoot zeta m)
    (A : Polynomial R) :
    (domainOrbitProduct m zeta A).comp (C zeta * X) =
      domainOrbitProduct m zeta A := by
  by_cases hA : A = 0
  · subst A
    simp [domainOrbitProduct, domainOrbitFactor]
  · rw [domainOrbitProduct, Polynomial.prod_comp]
    have hshift :
        (∏ j ∈ Finset.range m, domainOrbitFactor zeta A (j + 1)) =
          ∏ j ∈ Finset.range m, domainOrbitFactor zeta A j := by
      apply domain_prod_range_shift_eq
      · simpa using hA
      · exact domainOrbitFactor_period hzeta A
    calc
      (∏ j ∈ Finset.range m,
          (domainOrbitFactor zeta A j).comp (C zeta * X)) =
          ∏ j ∈ Finset.range m, domainOrbitFactor zeta A (j + 1) := by
            apply Finset.prod_congr rfl
            intro j hj
            exact domainOrbitFactor_comp_scale zeta A j
      _ = ∏ j ∈ Finset.range m, domainOrbitFactor zeta A j := hshift

/--
@isnad1 id=ex.2h4v.s7.76a62d58a379 from=translated src=- shape=930bb92f vocab=791b47f4
-/
theorem domainOrbitProduct_exists_comp_X_pow
    {m : ℕ} {zeta : R}
    (hm : 0 < m)
    (hzeta : IsPrimitiveRoot zeta m)
    (A : Polynomial R) :
    ∃ G : Polynomial R,
      domainOrbitProduct m zeta A = G.comp (X ^ m) := by
  exact exists_comp_X_pow_of_primitiveRoot_scale_invariant_domain
    (R := R) hm hzeta
      (domainOrbitProduct_scale_invariant hzeta A)

/--
@isnad1 id=le.0h4v.s5.3a64f0e8371e from=translated src=- shape=f87ce68b vocab=f97f5b62
-/
theorem domainOrbitProduct_natDegree_le
    (m : ℕ) (zeta : R) (A : Polynomial R) :
    (domainOrbitProduct m zeta A).natDegree ≤ m * A.natDegree := by
  unfold domainOrbitProduct
  calc
    (∏ j ∈ Finset.range m, domainOrbitFactor zeta A j).natDegree
        ≤ ∑ j ∈ Finset.range m, (domainOrbitFactor zeta A j).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _j ∈ Finset.range m, A.natDegree := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        (domainOrbitFactor zeta A j).natDegree =
            (A.comp (C (zeta ^ j) * X)).natDegree := rfl
        _ ≤ A.natDegree * (C (zeta ^ j) * X).natDegree :=
          Polynomial.natDegree_comp_le
        _ ≤ A.natDegree * 1 := by
          apply Nat.mul_le_mul_left
          simpa using
            Polynomial.natDegree_C_mul_le (zeta ^ j) (X : Polynomial R)
        _ = A.natDegree := by simp
    _ = m * A.natDegree := by simp

end LN97
end MagicSquares
