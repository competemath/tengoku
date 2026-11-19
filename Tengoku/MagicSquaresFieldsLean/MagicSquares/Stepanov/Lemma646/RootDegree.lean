import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.Core
import Tengoku.Seed.RingTheory.PowerBasis
import Tengoku.Seed.FieldTheory.Minpoly.Field

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

/-!
# LN97 Lemma 6.46: the degree-m root step

The final paragraph of the `f(0) ≠ 0` case of Lemma 6.46 reaches a
relation

    e₀ Y^(m-1) + e₁ Y^(m-2) + ... + e_{m-1} = 0

over the rational function field, where `Y` has degree `m` over that
field.  The book then concludes that all coefficients vanish.

This file formalizes exactly that field-theoretic step in a reusable
form.  It is independent of the symmetric-polynomial argument used
earlier in the proof to manufacture the relation.
-/

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The powers below the degree of the minimal polynomial are linearly
independent.  This packages mathlib's `linearIndependent_pow` into the
finite-sum form used in LN97 6.46.-/
theorem coefficients_zero_of_relation_below_minpoly
    (Y : L)
    (a : Fin (minpoly K Y).natDegree → K)
    (hrel :
      ∑ i : Fin (minpoly K Y).natDegree,
        algebraMap K L (a i) * Y ^ (i : ℕ) = 0) :
    ∀ i, a i = 0 := by
  have hlin :
      LinearIndependent K
        (fun i : Fin (minpoly K Y).natDegree => Y ^ (i : ℕ)) :=
    linearIndependent_pow Y
  rw [Fintype.linearIndependent_iff] at hlin
  apply hlin a
  simpa [Algebra.smul_def] using hrel

/-- If the minimal polynomial of `Y` has degree exactly `m`, then
`1,Y,...,Y^(m-1)` are linearly independent.-/
theorem coefficients_zero_of_relation_of_minpoly_degree
    (Y : L) (m : ℕ)
    (hdeg : (minpoly K Y).natDegree = m)
    (a : Fin m → K)
    (hrel :
      ∑ i : Fin m, algebraMap K L (a i) * Y ^ (i : ℕ) = 0) :
    ∀ i, a i = 0 := by
  subst m
  exact coefficients_zero_of_relation_below_minpoly Y a hrel

/-- Equivalent polynomial formulation: no nonzero polynomial of degree
strictly less than the degree of `Y` can vanish at `Y`.

This is particularly convenient for the polynomial obtained after LN97
multiplies `A(ζ_i Y⁻¹)` by `Y^(m-1)`.-/
theorem polynomial_eq_zero_of_aeval_eq_zero_of_natDegree_lt_minpoly
    (Y : L) (P : Polynomial K)
    (hdeg : P.natDegree < (minpoly K Y).natDegree)
    (hroot : (Polynomial.aeval Y) P = 0) :
    P = 0 := by
  exact Polynomial.eq_zero_of_dvd_of_natDegree_lt
    (minpoly.dvd K Y hroot) hdeg

/-- A version with the degree `m` named explicitly, matching the wording
"Y is of degree m over K" in LN97.-/
theorem polynomial_eq_zero_of_aeval_eq_zero_of_natDegree_lt_degree
    (Y : L) (m : ℕ)
    (hYdeg : (minpoly K Y).natDegree = m)
    (P : Polynomial K)
    (hPdeg : P.natDegree < m)
    (hroot : (Polynomial.aeval Y) P = 0) :
    P = 0 := by
  apply polynomial_eq_zero_of_aeval_eq_zero_of_natDegree_lt_minpoly Y P
  · simpa [hYdeg] using hPdeg
  · exact hroot

end LN97
end MagicSquares
