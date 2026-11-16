/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Tengoku.Seed.Analysis.Polynomial.Order
public import Tengoku.Seed.Analysis.Real.Sqrt
public import Tengoku.Seed.FieldTheory.IsRealClosed.Basic
import Tengoku.Seed.Algebra.Polynomial.SpecificDegree
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A real-closed model and polynomial boundary cases

The real numbers satisfy the real-closed-field class independently of any
algebraic-closure claim about quadratic algebras. The odd-degree-root clause
follows from the asymptotic-sign and intermediate-value results for real
polynomials. The quadratic and quartic examples show sharpness and the need
for irreducibility.

## References

* Mathlib, `Analysis.Polynomial.Order`
  (`Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg` and
  `Polynomial.zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg`),
  `Analysis.Real.Sqrt` (`Real.isSquare_iff`), and
  `FieldTheory.IsRealClosed.Basic` (`IsRealClosed.of_linearOrderedField`).
-/

@[expose] public section

open Polynomial

namespace QuadraticAlgebrasTest

private theorem oddDegreeRealPolynomial_hasRoot {p : ℝ[X]} (hodd : Odd p.natDegree) :
    ∃ x : ℝ, p.IsRoot x := by
  have contradiction_of_no_roots (q : ℝ[X]) (hq : Odd q.natDegree)
      (hnq : ∀ x : ℝ, ¬ q.IsRoot x) (hlc : 0 ≤ q.leadingCoeff) : False := by
    have hpos : 0 < q.eval 0 :=
      Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
        (fun x hx ↦ (hnq x hx).elim) hlc
    have hneg : 0 < Int.negOnePow q.natDegree * q.eval 0 :=
      Polynomial.zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg
        (fun x hx ↦ (hnq x hx).elim) hlc
    have hneg' : q.eval 0 < 0 := by
      have hq_int : Odd (q.natDegree : ℤ) := by simpa using hq
      have h : 0 < -(q.eval 0) := by
        simpa [Int.negOnePow_odd _ hq_int] using hneg
      exact neg_pos.mp h
    exact (lt_asymm hpos) hneg'
  by_contra! hn
  rcases le_total 0 p.leadingCoeff with hlc | hlc
  · exact contradiction_of_no_roots p hodd hn hlc
  · apply contradiction_of_no_roots (-p) (by simpa using hodd) ?_ (by simpa using hlc)
    intro x hx
    exact hn x (by simpa [Polynomial.IsRoot] using hx)

/-- The real numbers give a concrete model of Mathlib's unordered
`IsRealClosed` class. This uses Mathlib's `IsRealClosed.of_linearOrderedField`
from `FieldTheory.IsRealClosed.Basic`, `Real.isSquare_iff` from
`Analysis.Real.Sqrt`, and
`Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg` and
`Polynomial.zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg`
from `Analysis.Polynomial.Order` for the odd-degree-root clause.
@isnad1 id=isrealcl.0h0v.s1.46ab8920515e from=translated src=- shape=49959d42 vocab=b9d4b176
-/
theorem realIsRealClosed : IsRealClosed ℝ := by
  apply IsRealClosed.of_linearOrderedField
  · intro x hx
    exact Real.isSquare_iff.mpr hx
  · intro p hp
    exact oddDegreeRealPolynomial_hasRoot hp

/-- The irreducible polynomial `X² + 1` has the maximal allowed degree over
the real-closed model. Its root-free property follows from square nonnegativity,
not from algebraic closedness of a quadratic extension.
@isnad1 id=and.0h0v.s7.96a0f165937e from=translated src=- shape=024ac048 vocab=bde7e7b7
-/
theorem sharpGaussian :
    (X ^ 2 + 1 : ℝ[X]).natDegree = 2 ∧ Irreducible (X ^ 2 + 1 : ℝ[X]) := by
  have hdegree : (X ^ 2 + 1 : ℝ[X]).natDegree = 2 := by
    simpa only [Polynomial.C_1] using
      (Polynomial.natDegree_X_pow_add_C (r := (1 : ℝ)) (n := 2))
  refine ⟨hdegree, ?_⟩
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [hdegree]
    decide
  · intro x hx
    have hsquare : x ^ 2 = -1 := by
      simpa [Polynomial.IsRoot, add_eq_zero_iff_eq_neg] using hx
    have hnonneg : (0 : ℝ) ≤ -1 := by
      rw [← hsquare]
      exact sq_nonneg x
    norm_num at hnonneg

private theorem powSubOne_reducible (degree : ℕ) (hdegree : degree ≠ 1) :
    ¬ Irreducible (X ^ degree - 1 : ℝ[X]) := by
  intro hirr
  have hpdegree : (X ^ degree - 1 : ℝ[X]).natDegree = degree := by
    simpa only [Polynomial.C_1] using
      (Polynomial.natDegree_X_pow_sub_C (r := (1 : ℝ)) (n := degree))
  have hroot : (X ^ degree - 1 : ℝ[X]).IsRoot 1 := by
    simp [Polynomial.IsRoot]
  exact (hirr.not_isRoot_of_natDegree_ne_one (by simpa [hpdegree] using hdegree)) hroot

/-- Degree two alone does not imply irreducibility, nor can the degree bound
hold for arbitrary reducible polynomials: `X⁴ - 1` has degree four.
@isnad1 id=and.0h0v.s7.3bca5f297878 from=translated src=- shape=96f381c4 vocab=37608607
-/
theorem reducibleBoundaries :
    (¬ Irreducible (X ^ 2 - 1 : ℝ[X])) ∧
      (X ^ 4 - 1 : ℝ[X]).natDegree = 4 ∧
      ¬ Irreducible (X ^ 4 - 1 : ℝ[X]) := by
  refine ⟨powSubOne_reducible 2 (by decide), ?_, powSubOne_reducible 4 (by decide)⟩
  simpa only [Polynomial.C_1] using
    (Polynomial.natDegree_X_pow_sub_C (r := (1 : ℝ)) (n := 4))

end QuadraticAlgebrasTest
