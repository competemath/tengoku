/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Valuation.ValuationRing
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.ErrorPowers

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# the finite minimum coefficient

The coefficientwise proof of Hensel's lemma chooses, among the finitely many
coefficients of `f - g₀h₀` and `ag₀ + bh₀ - 1`, one coefficient of minimum
valuation and calls it `π`.  In a valuation ring this is the same algebraic
input as choosing one coefficient that divides all coefficients in the finite
set.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- finite divisibility minimum in a valuation ring: every
nonempty finite set has an element that divides all elements of the set.-/
theorem henselFactorization_exists_mem_finset_dvd_all
    {R : Type*} [Monoid R] [PreValuationRing R] {s : Finset R}
    (hs : s.Nonempty) :
    ∃ π ∈ s, ∀ x ∈ s, π ∣ x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rcases hs with ⟨x, hx⟩
      exact (Finset.notMem_empty x hx).elim
  | @insert a s ha ih =>
      by_cases hs' : s.Nonempty
      · rcases ih hs' with ⟨π, hπs, hπall⟩
        rcases ValuationRing.dvd_total π a with hπa | haπ
        · refine ⟨π, Finset.mem_insert_of_mem hπs, ?_⟩
          intro x hx
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hxs
          · exact hπa
          · exact hπall x hxs
        · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
          intro x hx
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hxs
          · exact dvd_refl _
          · exact dvd_trans haπ (hπall x hxs)
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hxs
        · exact dvd_refl _
        · exact False.elim (hs' ⟨x, hxs⟩)

/-- the finite set of coefficients of two polynomials from
which the construction chooses the minimum-value coefficient.-/
def henselFactorization_twoPolynomialCoeffFinset
    {R : Type*} [Semiring R] (P Q : R[X]) : Finset R := by
  classical
  exact P.support.image (fun n => P.coeff n) ∪
    Q.support.image (fun n => Q.coeff n)

/-- A coefficient supported in the left polynomial belongs to the two-polynomial
coefficient set.-/
theorem henselFactorization_mem_twoPolynomialCoeffFinset_left
    {R : Type*} [Semiring R] {P Q : R[X]} {n : ℕ}
    (hn : n ∈ P.support) :
    P.coeff n ∈ henselFactorization_twoPolynomialCoeffFinset P Q := by
  classical
  unfold henselFactorization_twoPolynomialCoeffFinset
  exact Finset.mem_union.mpr
    (Or.inl (Finset.mem_image.mpr ⟨n, hn, rfl⟩))

/-- A coefficient supported in the right polynomial belongs to the
two-polynomial coefficient set.-/
theorem henselFactorization_mem_twoPolynomialCoeffFinset_right
    {R : Type*} [Semiring R] {P Q : R[X]} {n : ℕ}
    (hn : n ∈ Q.support) :
    Q.coeff n ∈ henselFactorization_twoPolynomialCoeffFinset P Q := by
  classical
  unfold henselFactorization_twoPolynomialCoeffFinset
  exact Finset.mem_union.mpr
    (Or.inr (Finset.mem_image.mpr ⟨n, hn, rfl⟩))

/-- if the two-polynomial coefficient set is nonempty, one of
its coefficients divides every coefficient of both polynomials.-/
theorem henselFactorization_exists_coeff_dvd_all_two_polynomials
    {R : Type*} [CommRing R] [PreValuationRing R] {P Q : R[X]}
    (hs : (henselFactorization_twoPolynomialCoeffFinset P Q).Nonempty) :
    ∃ π ∈ henselFactorization_twoPolynomialCoeffFinset P Q,
      (∀ n : ℕ, π ∣ P.coeff n) ∧
        (∀ n : ℕ, π ∣ Q.coeff n) := by
  classical
  rcases henselFactorization_exists_mem_finset_dvd_all
      (R := R) (s := henselFactorization_twoPolynomialCoeffFinset P Q) hs with
    ⟨π, hπ, hπall⟩
  refine ⟨π, hπ, ?_, ?_⟩
  · intro n
    by_cases hn : n ∈ P.support
    · exact hπall (P.coeff n)
        (henselFactorization_mem_twoPolynomialCoeffFinset_left
          (P := P) (Q := Q) hn)
    · rw [Polynomial.notMem_support_iff.mp hn]
      exact dvd_zero π
  · intro n
    by_cases hn : n ∈ Q.support
    · exact hπall (Q.coeff n)
        (henselFactorization_mem_twoPolynomialCoeffFinset_right
          (P := P) (Q := Q) hn)
    · rw [Polynomial.notMem_support_iff.mp hn]
      exact dvd_zero π

/-- if the two polynomials have coefficients in an ideal, the
chosen finite-minimum coefficient lies in the same ideal.-/
theorem henselFactorization_exists_coeff_mem_ideal_dvd_all_two_polynomials
    {R : Type*} [CommRing R] [PreValuationRing R] {I : Ideal R}
    {P Q : R[X]}
    (hP : ∀ n : ℕ, P.coeff n ∈ I)
    (hQ : ∀ n : ℕ, Q.coeff n ∈ I)
    (hs : (henselFactorization_twoPolynomialCoeffFinset P Q).Nonempty) :
    ∃ π ∈ I,
      π ∈ henselFactorization_twoPolynomialCoeffFinset P Q ∧
        (∀ n : ℕ, π ∣ P.coeff n) ∧
          (∀ n : ℕ, π ∣ Q.coeff n) := by
  classical
  rcases henselFactorization_exists_coeff_dvd_all_two_polynomials
      (R := R) (P := P) (Q := Q) hs with
    ⟨π, hπcoeff, hπP, hπQ⟩
  have hπI : π ∈ I := by
    unfold henselFactorization_twoPolynomialCoeffFinset at hπcoeff
    rw [Finset.mem_union] at hπcoeff
    rcases hπcoeff with hπleft | hπright
    · rcases Finset.mem_image.mp hπleft with ⟨n, _hn, hnπ⟩
      rw [← hnπ]
      exact hP n
    · rcases Finset.mem_image.mp hπright with ⟨n, _hn, hnπ⟩
      rw [← hnπ]
      exact hQ n
  exact ⟨π, hπI, hπcoeff, hπP, hπQ⟩

end Valuations
end AlgebraicNumberTheory

end
