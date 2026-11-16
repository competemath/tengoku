/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.JacobianTwo.JacobianTwo.QuadraticDenominator
import Tengoku.Seed.Algebra.Polynomial.Eval.Degree
import Tengoku.Seed.RingTheory.Coprime.Lemmas
import Tengoku.Seed.Tactic.FieldSimp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cleared polynomial evaluation

This file packages the denominator calculation used after the quadratic
recurrence.  If `C` has degree at most `n`, then evaluating `C` at
`N / q^2` has common denominator `q^(2*n)`.  The corresponding numerator is
`clearedEval C N q n`.

When `C` has exact degree `m`, its leading summand is the unique term in this
numerator without a positive power of `q`.  Coprimality therefore prevents
that numerator, even after multiplication by another coprime factor, from
being divisible by a nonunit `q`.
-/

noncomputable section

open scoped BigOperators
open Polynomial

namespace JacobianTwo.QuadraticClearedEval

/-- The numerator obtained by evaluating `C` at `N / q^2` and clearing the
common denominator `q^(2*n)`.-/
def clearedEval
    {K R : Type*} [CommSemiring K] [CommSemiring R] [Algebra K R]
    (C : K[X]) (N q : R) (n : ℕ) : R :=
  ∑ i ∈ Finset.range (n + 1),
    algebraMap K R (C.coeff i) * N ^ i * q ^ (2 * (n - i))

/-- Mapping a cleared evaluation to a fraction field and dividing by the
common denominator recovers evaluation at `N / q^2`.-/
theorem map_clearedEval_div_pow
    {K R L : Type*} [Field K] [CommRing R] [IsDomain R] [Field L]
    [Algebra K R] [Algebra R L] [Algebra K L] [IsScalarTower K R L]
    [IsFractionRing R L]
    (C : K[X]) (N q : R) (n : ℕ)
    (hdegree : C.natDegree ≤ n) (hq : q ≠ 0) :
    algebraMap R L (clearedEval C N q n) /
        algebraMap R L q ^ (2 * n) =
      (C.map (algebraMap K L)).eval
        (algebraMap R L N / algebraMap R L q ^ 2) := by
  rw [eval_map, eval₂_eq_sum_range'
    (f := algebraMap K L) (Nat.lt_succ_of_le hdegree)]
  simp only [clearedEval, map_sum, map_mul, map_pow,
    IsScalarTower.algebraMap_apply K R L]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hqMap : algebraMap R L q ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective R L).ne hq
  rw [div_pow]
  field_simp [hqMap]
  have hexponent : 2 * (n - i) + 2 * i = 2 * n := by omega
  rw [← pow_mul, mul_assoc, ← pow_add, hexponent]

/-- The leading summand of a cleared evaluation cannot cancel modulo a
nonunit denominator.  The hypotheses say that both the external factor `z`
and the residual numerator `N` are coprime to `q`.-/
theorem not_dvd_mul_clearedEval
    {K R : Type*} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    (C : K[X]) (N q z : R) (m : ℕ)
    (hqNonunit : ¬ IsUnit q)
    (hzq : IsCoprime z q) (hNq : IsCoprime N q)
    (hdegree : C.natDegree = m) (hlead : C.leadingCoeff ≠ 0) :
    ¬ q ∣ z * clearedEval C N q m := by
  rw [clearedEval, Finset.mul_sum]
  apply QuadraticDenominator.not_dvd_sum_of_unique_survivor
      (i₀ := m)
  · simp
  · have hcoeff : C.coeff m = C.leadingCoeff := by
      rw [← hdegree, coeff_natDegree]
    simp only [hcoeff, Nat.sub_self, mul_zero, pow_zero, mul_one]
    have hscalar : IsUnit (algebraMap K R C.leadingCoeff) :=
      (isUnit_iff_ne_zero.mpr hlead).map (algebraMap K R)
    have hscalarCoprime : IsCoprime (algebraMap K R C.leadingCoeff) q := by
      simpa using
        (isCoprime_mul_unit_left_left hscalar 1 q).mpr isCoprime_one_left
    have hcoprime :
        IsCoprime (z * (algebraMap K R C.leadingCoeff * N ^ m)) q := by
      simpa only [mul_assoc] using hzq.mul_left (hscalarCoprime.mul_left hNq.pow_left)
    intro hdvd
    exact hqNonunit (hcoprime.symm.isUnit_of_dvd hdvd)
  · intro i hi him
    have hi_lt : i < m := by
      have hi_le : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact lt_of_le_of_ne hi_le him
    have hexponent : 2 * (m - i) ≠ 0 := by omega
    simpa only [mul_assoc] using
      (dvd_mul_of_dvd_right (dvd_pow_self q hexponent)
        (z * (algebraMap K R (C.coeff i) * N ^ i)))

end JacobianTwo.QuadraticClearedEval
