/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
import Tengoku.Seed.Algebra.Polynomial.Degree.Units
import Tengoku.Seed.RingTheory.Localization.FractionRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Denominator certificates for the variable-leading quadratic argument

The remaining denominator step in the variable-leading quadratic case can be
separated from its valuation bookkeeping.  After putting all summands over a
common prime-power denominator, it is enough to show that exactly one numerator
summand is nonzero modulo the chosen irreducible factor.  The common numerator
is then not divisible by that factor, so the resulting fraction cannot belong
to the base ring.

This file packages that argument without choosing a particular factorization or
valuation API.  The final theorem is intended to be fed by the exact-order
calculation in Step 5, while
`isUnit_denominator_of_unit_fraction_mem_base` is the abstract Step 6 endpoint.
-/

noncomputable section

open scoped BigOperators

namespace JacobianTwo.QuadraticDenominator

/-- If all but one summand are divisible by `p` and the exceptional summand is
not, then the whole finite sum is not divisible by `p`.

This is the divisibility form of the unique-lowest-valuation principle: after
clearing a common denominator, the lowest-order term is precisely the unique
term which survives modulo `p`.-/
theorem not_dvd_sum_of_unique_survivor
    {R ι : Type*} [CommRing R] [DecidableEq ι]
    {s : Finset ι} {i₀ : ι} {p : R} {a : ι → R}
    (hi₀ : i₀ ∈ s)
    (hexceptional : ¬p ∣ a i₀)
    (hothers : ∀ i ∈ s, i ≠ i₀ → p ∣ a i) :
    ¬p ∣ ∑ i ∈ s, a i := by
  intro hsum
  have hrest : p ∣ ∑ i ∈ s.erase i₀, a i := by
    refine Finset.dvd_sum fun i hi ↦ ?_
    exact hothers i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
  apply hexceptional
  have hdifference : p ∣ (∑ i ∈ s, a i) - ∑ i ∈ s.erase i₀, a i :=
    hsum.sub hrest
  simpa only [← Finset.sum_erase_add _ _ hi₀, add_sub_cancel_left] using hdifference

/-- A fraction represented by `numerator / denominator` can come from the base
ring only if `denominator` divides `numerator` in the base ring.

The statement is independent of the chosen model of the fraction field.-/
theorem denominator_dvd_of_div_mem_base
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {numerator denominator : R}
    (hdenominator : denominator ≠ 0)
    (hmem : algebraMap R K numerator / algebraMap R K denominator ∈
      Set.range (algebraMap R K)) :
    denominator ∣ numerator := by
  obtain ⟨r, hr⟩ := hmem
  have hinjective : Function.Injective (algebraMap R K) :=
    IsFractionRing.injective R K
  have hdenominatorMap : algebraMap R K denominator ≠ 0 := by
    simpa only [map_zero] using hinjective.ne hdenominator
  refine ⟨r, ?_⟩
  apply hinjective
  rw [map_mul]
  simpa only [mul_comm] using (div_eq_iff hdenominatorMap).mp hr.symm

/-- A non-cancelling denominator prevents a fraction from belonging to the
embedded base ring.-/
theorem div_not_mem_base_of_not_dvd
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {numerator denominator : R}
    (hdenominator : denominator ≠ 0)
    (hnotDvd : ¬denominator ∣ numerator) :
    algebraMap R K numerator / algebraMap R K denominator ∉
      Set.range (algebraMap R K) := by
  intro hmem
  exact hnotDvd (denominator_dvd_of_div_mem_base hdenominator hmem)

/-- Flexible common-denominator form of the unique-lowest-valuation
obstruction.  The denominator may contain factors besides `p`; it is enough
that `p` divides it.-/
theorem unique_survivor_fraction_not_mem_base_of_dvd_denominator
    {R K ι : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [DecidableEq ι]
    {s : Finset ι} {i₀ : ι} {p denominator : R} {a : ι → R}
    (hi₀ : i₀ ∈ s)
    (hdenominator : denominator ≠ 0)
    (hpDvd : p ∣ denominator)
    (hexceptional : ¬p ∣ a i₀)
    (hothers : ∀ i ∈ s, i ≠ i₀ → p ∣ a i) :
    algebraMap R K (∑ i ∈ s, a i) / algebraMap R K denominator ∉
      Set.range (algebraMap R K) := by
  apply div_not_mem_base_of_not_dvd hdenominator
  intro hdenominatorDvd
  exact not_dvd_sum_of_unique_survivor hi₀ hexceptional hothers
    (hpDvd.trans hdenominatorDvd)

/-- Common-denominator form of the unique-lowest-valuation obstruction.

Suppose the common denominator is the positive power `p ^ exponent`.  If one
numerator summand is not divisible by `p` and every other summand is, then the
fraction is not an element of the base ring.  Primality of `p` is deliberately
not required: it belongs in the preceding valuation/order calculation, not in
this final denominator certificate.-/
theorem unique_survivor_fraction_not_mem_base
    {R K ι : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [DecidableEq ι]
    {s : Finset ι} {i₀ : ι} {p : R} {a : ι → R} {exponent : ℕ}
    (hi₀ : i₀ ∈ s)
    (hp : p ≠ 0)
    (hexponent : exponent ≠ 0)
    (hexceptional : ¬p ∣ a i₀)
    (hothers : ∀ i ∈ s, i ≠ i₀ → p ∣ a i) :
    algebraMap R K (∑ i ∈ s, a i) / algebraMap R K (p ^ exponent) ∉
      Set.range (algebraMap R K) := by
  exact unique_survivor_fraction_not_mem_base_of_dvd_denominator
    hi₀ (pow_ne_zero exponent hp) (dvd_pow_self p hexponent)
    hexceptional hothers

/-- If a fraction with unit numerator belongs to the base ring, then its
denominator is a unit.  For Step 6, the numerator is the nonzero scalar
polynomial `C k`, so this turns polynomiality of `k / h` directly into the
conclusion that `h` is constant and nonzero.-/
theorem isUnit_denominator_of_unit_fraction_mem_base
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {numerator denominator : R}
    (hdenominator : denominator ≠ 0)
    (hnumerator : IsUnit numerator)
    (hmem : algebraMap R K numerator / algebraMap R K denominator ∈
      Set.range (algebraMap R K)) :
    IsUnit denominator :=
  isUnit_of_dvd_unit
    (denominator_dvd_of_div_mem_base hdenominator hmem) hnumerator

/-- Polynomial specialization of the Step 6 endpoint: if `k ≠ 0` and `k / h`
is a polynomial, then the polynomial denominator `h` is a unit.-/
theorem isUnit_polynomial_denominator_of_scalar_fraction_mem_base
    {F : Type*} [Field F] {k : F} {h : Polynomial F}
    (hh : h ≠ 0)
    (hk : k ≠ 0)
    (hmem : algebraMap (Polynomial F) (FractionRing (Polynomial F)) (Polynomial.C k) /
        algebraMap (Polynomial F) (FractionRing (Polynomial F)) h ∈
      Set.range (algebraMap (Polynomial F) (FractionRing (Polynomial F)))) :
    IsUnit h := by
  exact isUnit_denominator_of_unit_fraction_mem_base
    (R := Polynomial F) (K := FractionRing (Polynomial F)) hh
    (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hk)) hmem

end JacobianTwo.QuadraticDenominator
