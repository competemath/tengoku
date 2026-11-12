import Tengoku.AbelFormalization.AbelFormalization.FiniteCommonDenominator
import Tengoku.AbelFormalization.AbelFormalization.MvPolynomialDenominatorClearing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Clearing finitely many coordinate denominators in a polynomial family

This combines the product common denominator with the literal homogenized
multivariate-polynomial evaluation.  One total-degree bound clears every row
of a finite polynomial family, and all cleared rows remain in any function
subalgebra containing their finite coefficient and coordinate data.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Literal polynomial value after replacing individual rational coordinates
by numerators over one product common denominator.-/
def finiteCommonDenominatorMvPolynomialEval
    {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    [Fintype σ] [DecidableEq σ]
    (D : ℕ) (c : R →+* S)
    (denominator numerator : σ → S)
    (P : MvPolynomial σ R) : S :=
  denominatorClearedMvPolynomialEval D c
    (finiteCommonDenominator denominator)
    (finiteCommonClearedNumerator denominator numerator) P

/-- A product common denominator clears a polynomial whenever each variable
has its stated individual denominator identity.
@isnad1 id=eq.2h9v.s7.826c5bee7073 from=translated src=- shape=04623314 vocab=988357f8
-/
theorem finiteCommonDenominator_pow_mul_eval₂_eq
    {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    [Fintype σ] [DecidableEq σ]
    (D : ℕ) (c : R →+* S)
    (denominator numerator old : σ → S)
    (P : MvPolynomial σ R) (hD : P.totalDegree ≤ D)
    (hcoordinate : ∀ i, denominator i * old i = numerator i) :
    finiteCommonDenominator denominator ^ D * MvPolynomial.eval₂ c old P =
      finiteCommonDenominatorMvPolynomialEval D c denominator numerator P := by
  exact pow_mul_eval₂_eq_denominatorClearedMvPolynomialEval
    D c (finiteCommonDenominator denominator) old
    (finiteCommonClearedNumerator denominator numerator) P hD
    (finiteCommonDenominator_mul_eq_clearedNumerator
      denominator numerator old hcoordinate)

/-- The cleared polynomial is in a function subalgebra when its supported
coefficients and all individual denominator/numerator data are in it.
@isnad1 id=mem.3h9v.s9.5ba7c1e4d139 from=translated src=- shape=19af282a vocab=6a59fd24
-/
theorem finiteCommonDenominatorMvPolynomialEval_mem_subalgebra
    {X R σ : Type*} [CommSemiring R]
    [Fintype σ] [DecidableEq σ]
    (B : Subalgebra ℝ (X → ℝ))
    (D : ℕ) (c : R →+* (X → ℝ))
    (denominator numerator : σ → X → ℝ)
    (P : MvPolynomial σ R)
    (hc : ∀ d, d ∈ P.support → c (P.coeff d) ∈ B)
    (hdenominator : ∀ i, denominator i ∈ B)
    (hnumerator : ∀ i, numerator i ∈ B) :
    finiteCommonDenominatorMvPolynomialEval D c denominator numerator P ∈ B := by
  apply denominatorClearedMvPolynomialEval_mem_subalgebra B D c
    (finiteCommonDenominator denominator)
    (finiteCommonClearedNumerator denominator numerator) P hc
  · exact finiteCommonDenominator_mem_subalgebra B denominator hdenominator
  · intro d hd i hi
    exact finiteCommonClearedNumerator_mem_subalgebra B
      denominator numerator hdenominator hnumerator i

/-- Clear every row in a finite polynomial family using its common maximum
total degree.-/
def finiteCommonDenominatorMvPolynomialFamilyEval
    {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    [Fintype σ] [DecidableEq σ] {n : ℕ}
    (c : R →+* S) (denominator numerator : σ → S)
    (Q : Fin n → MvPolynomial σ R) (i : Fin n) : S :=
  finiteCommonDenominatorMvPolynomialEval
    (mvPolynomialFamilyTotalDegree Q) c denominator numerator (Q i)

/--
@isnad1 id=eq.1h10v.s7.f9b180a914ca from=translated src=- shape=cc2b2d4d vocab=6ec6294f
-/
theorem finiteCommonDenominator_family_pow_mul_eval₂_eq
    {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    [Fintype σ] [DecidableEq σ] {n : ℕ}
    (c : R →+* S) (denominator numerator old : σ → S)
    (Q : Fin n → MvPolynomial σ R)
    (hcoordinate : ∀ i, denominator i * old i = numerator i)
    (row : Fin n) :
    finiteCommonDenominator denominator ^ mvPolynomialFamilyTotalDegree Q *
        MvPolynomial.eval₂ c old (Q row) =
      finiteCommonDenominatorMvPolynomialFamilyEval
        c denominator numerator Q row := by
  exact finiteCommonDenominator_pow_mul_eval₂_eq
    (mvPolynomialFamilyTotalDegree Q) c denominator numerator old (Q row)
    (mvPolynomial_totalDegree_le_familyTotalDegree Q row) hcoordinate

/--
@isnad1 id=mem.3h10v.s9.8ad1dbc5c15a from=translated src=- shape=d2f8a72b vocab=89c3deff
-/
theorem finiteCommonDenominatorMvPolynomialFamilyEval_mem_subalgebra
    {X R σ : Type*} [CommSemiring R]
    [Fintype σ] [DecidableEq σ] {n : ℕ}
    (B : Subalgebra ℝ (X → ℝ))
    (c : R →+* (X → ℝ))
    (denominator numerator : σ → X → ℝ)
    (Q : Fin n → MvPolynomial σ R)
    (hc : ∀ row d, d ∈ (Q row).support → c ((Q row).coeff d) ∈ B)
    (hdenominator : ∀ i, denominator i ∈ B)
    (hnumerator : ∀ i, numerator i ∈ B)
    (row : Fin n) :
    finiteCommonDenominatorMvPolynomialFamilyEval
      c denominator numerator Q row ∈ B := by
  exact finiteCommonDenominatorMvPolynomialEval_mem_subalgebra B
    (mvPolynomialFamilyTotalDegree Q) c denominator numerator (Q row)
    (hc row) hdenominator hnumerator

end AbelFormalization
