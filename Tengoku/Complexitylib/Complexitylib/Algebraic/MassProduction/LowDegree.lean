/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku

/-!
# Low-degree affine-line recovery

This file formalizes the polynomial identity used by the local-recovery
gadget in the
[Boolean mass-production manuscript](https://github.com/SamuelSchlesinger/boolean-mass-production).
A multivariate polynomial of total degree below `|K| - 1` is recoverable at
the center of every affine line from its values at all nonzero line
parameters. In characteristic two, the recovery operation is a sum.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction

open scoped BigOperators

/-- The affine-linear polynomial substituted for coordinate `index` when
restricting a multivariate polynomial to the line through `center` in
direction `direction`. -/
noncomputable def lineCoordinate
    {K Coordinate : Type*}
    [CommRing K]
    (center direction : Coordinate -> K)
    (index : Coordinate) : Polynomial K :=
  Polynomial.C (center index) +
    Polynomial.C (direction index) * Polynomial.X

/-- Restrict a multivariate polynomial to an affine line. -/
noncomputable def lineRestriction
    {K Coordinate : Type*}
    [CommRing K]
    (polynomial : MvPolynomial Coordinate K)
    (center direction : Coordinate -> K) : Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C
    (lineCoordinate center direction) polynomial

/-- A univariate polynomial of degree below `|K| - 1` has evaluation sum
zero over the finite field `K`.
@isnad1 id=eq.1h2v.s6.bb12c0467307 from=translated src=- shape=ad960f9c vocab=c013fd25
-/
theorem polynomial_sum_eval_eq_zero
    {K : Type*}
    [Fintype K] [Field K]
    (polynomial : Polynomial K)
    (degree : polynomial.natDegree < Fintype.card K - 1) :
    ∑ value : K, polynomial.eval value = 0 := by
  classical
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro exponent inSupport
  rw [← Finset.mul_sum]
  rw [FiniteField.sum_pow_lt_card_sub_one K exponent]
  · simp
  · exact lt_of_le_of_lt
      (Polynomial.le_natDegree_of_mem_supp exponent inSupport) degree

/-- Isolating the zero evaluation gives the punctured-field identity.
@isnad1 id=eq.1h2v.s7.9a5c8330dbd8 from=translated src=- shape=3d438b36 vocab=bb565fd8
-/
theorem polynomial_line_identity
    {K : Type*}
    [Fintype K] [Field K] [DecidableEq K]
    (polynomial : Polynomial K)
    (degree : polynomial.natDegree < Fintype.card K - 1) :
    polynomial.eval 0 =
      -∑ value ∈ (Finset.univ.erase (0 : K)), polynomial.eval value := by
  have total := polynomial_sum_eval_eq_zero polynomial degree
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : K))] at total
  exact eq_neg_of_add_eq_zero_right total

/-- Every substituted affine coordinate has degree at most one.
@isnad1 id=le.0h5v.s5.ae7d259d9b80 from=translated src=- shape=f643b09f vocab=17d721a3
-/
theorem natDegree_lineCoordinate_le
    {K Coordinate : Type*}
    [CommRing K]
    (center direction : Coordinate -> K)
    (index : Coordinate) :
    (lineCoordinate center direction index).natDegree <= 1 := by
  unfold lineCoordinate
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simp
  · simpa only [pow_one] using
      (Polynomial.natDegree_C_mul_X_pow_le (direction index) 1)

/-- Evaluating a line restriction has the expected affine-line semantics.
@isnad1 id=eq.0h6v.s7.dded74f9cf8a from=translated src=- shape=7828c866 vocab=c404f76c
-/
theorem lineRestriction_eval
    {K Coordinate : Type*}
    [CommRing K]
    (polynomial : MvPolynomial Coordinate K)
    (center direction : Coordinate -> K)
    (parameter : K) :
    (lineRestriction polynomial center direction).eval parameter =
      MvPolynomial.eval
        (fun index => center index + direction index * parameter)
        polynomial := by
  change Polynomial.evalRingHom parameter
      (lineRestriction polynomial center direction) = _
  rw [lineRestriction, MvPolynomial.map_eval₂Hom]
  apply MvPolynomial.eval₂Hom_congr
  · ext value
    simp
  · funext index
    simp [lineCoordinate]
  · rfl

/-- The line restriction of a monomial has degree at most its total
exponent.
@isnad1 id=le.0h6v.s8.5b4d4de9459f from=translated src=- shape=6b63ef26 vocab=4b376f45
-/
theorem natDegree_lineMonomial_le
    {K Coordinate : Type*}
    [CommRing K]
    (center direction : Coordinate -> K)
    (degrees : Coordinate →₀ Nat)
    (coefficient : K) :
    (MvPolynomial.eval₂Hom Polynomial.C (lineCoordinate center direction)
      (MvPolynomial.monomial degrees coefficient)).natDegree <=
        degrees.sum (fun _ exponent => exponent) := by
  rw [MvPolynomial.eval₂Hom_monomial]
  apply (Polynomial.natDegree_C_mul_le coefficient _).trans
  unfold Finsupp.prod
  apply (Polynomial.natDegree_prod_le degrees.support
    (fun index => lineCoordinate center direction index ^ degrees index)).trans
  apply Finset.sum_le_sum
  intro index _
  exact (Polynomial.natDegree_pow_le_of_le (degrees index)
    (natDegree_lineCoordinate_le center direction index)).trans (by simp)

/-- Restriction to an affine line cannot increase total degree.
@isnad1 id=le.0h5v.s5.261e6e15f8a9 from=translated src=- shape=688ef75c vocab=1fe56b51
-/
theorem natDegree_lineRestriction_le
    {K Coordinate : Type*}
    [CommRing K]
    (polynomial : MvPolynomial Coordinate K)
    (center direction : Coordinate -> K) :
    (lineRestriction polynomial center direction).natDegree <=
      polynomial.totalDegree := by
  unfold lineRestriction
  conv_lhs => rw [polynomial.as_sum]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro degrees inSupport
  exact (natDegree_lineMonomial_le center direction degrees
    (polynomial.coeff degrees)).trans
      (MvPolynomial.le_totalDegree inSupport)

/-- Low total degree gives recovery from the punctured affine line.
@isnad1 id=eq.1h5v.s8.3b303d4a4f70 from=translated src=- shape=2afc246c vocab=0f40ea39
-/
theorem affineLine_identity
    {K Coordinate : Type*}
    [Fintype K] [Field K] [DecidableEq K]
    (polynomial : MvPolynomial Coordinate K)
    (degree : polynomial.totalDegree < Fintype.card K - 1)
    (center direction : Coordinate -> K) :
    MvPolynomial.eval center polynomial =
      -∑ parameter ∈ (Finset.univ.erase (0 : K)),
        MvPolynomial.eval
          (fun index => center index + direction index * parameter)
          polynomial := by
  have lineIdentity := polynomial_line_identity
    (lineRestriction polynomial center direction)
    ((natDegree_lineRestriction_le polynomial center direction).trans_lt degree)
  simpa only [lineRestriction_eval, mul_zero, add_zero] using lineIdentity

/-- In a ring of characteristic two, every element is its own negation.
@isnad1 id=eq.0h2v.s5.cc89ac52d720 from=translated src=- shape=9a36db2e vocab=6ffee733
-/
theorem neg_eq_self_of_char_two
    {K : Type*}
    [Ring K] [CharP K 2]
    (value : K) :
    -value = value := by
  have twoIsZero : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have selfAdd : value + value = 0 := by
    rw [← two_mul, twoIsZero, zero_mul]
  exact (eq_neg_of_add_eq_zero_left selfAdd).symm

/-- In characteristic two, punctured-line recovery is the sum of the other
line values.
@isnad1 id=eq.1h5v.s8.6d251d568abd from=translated src=- shape=d871ca68 vocab=bce0ab1f
-/
theorem affineLine_identity_charTwo
    {K Coordinate : Type*}
    [Fintype K] [Field K] [DecidableEq K] [CharP K 2]
    (polynomial : MvPolynomial Coordinate K)
    (degree : polynomial.totalDegree < Fintype.card K - 1)
    (center direction : Coordinate -> K) :
    MvPolynomial.eval center polynomial =
      ∑ parameter ∈ (Finset.univ.erase (0 : K)),
        MvPolynomial.eval
          (fun index => center index + direction index * parameter)
          polynomial := by
  rw [affineLine_identity polynomial degree center direction,
    neg_eq_self_of_char_two]

end MassProduction
end Algebraic
