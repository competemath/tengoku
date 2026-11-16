/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.JacobianTwo.JacobianTwo.QuadraticClearedEval
import Tengoku.Seed.Algebra.Polynomial.AlgebraMap
import Tengoku.Seed.Tactic.FieldSimp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Valuation-free denominator descent

This file assembles the coefficientwise cleared-evaluation certificates for a
polynomial over a fraction field.  After putting every coefficient over the
common denominator `q^(2*m)` and multiplying by `z / q`, the whole expression
has denominator `q^(2*m+1)`.  Exactly one numerator summand survives modulo
`q`, so the expression cannot belong to the base ring.

No factorization, primality, or valuation is used.
-/

noncomputable section

open scoped BigOperators
open Polynomial

namespace JacobianTwo.QuadraticDenominatorDescent

open JacobianTwo.QuadraticClearedEval

/-- The `j`th numerator contribution after moving all coefficient evaluations
to the common denominator `q^(2*m+1)`.-/
def denominatorDescentTerm
    {K R : Type*} [CommSemiring K] [CommSemiring R] [Algebra K R]
    (C : ℕ → K[X]) (N q z f : R) (m j : ℕ) : R :=
  z * f ^ j * q ^ (2 * j) * clearedEval (C j) N q (m - j)

/-- Assemble the coefficientwise cleared evaluations into one common
fraction.  This is the exact algebraic identity behind the denominator
descent.-/
theorem mul_eval_eq_common_denominator
    {K R L : Type*} [Field K] [CommRing R] [IsDomain R] [Field L]
    [Algebra K R] [Algebra R L] [Algebra K L] [IsScalarTower K R L]
    [IsFractionRing R L]
    (q z N f : R) (B : L[X]) (m : ℕ) (C : ℕ → K[X])
    (hq : q ≠ 0) (hBdegree : B.natDegree ≤ m)
    (hcoeff : ∀ j ≤ m,
      B.coeff j = aeval
        (algebraMap R L N / algebraMap R L q ^ 2) (C j))
    (hCdegree : ∀ j ≤ m, (C j).natDegree ≤ m - j) :
    (algebraMap R L z / algebraMap R L q) *
        B.eval (algebraMap R L f) =
      algebraMap R L
          (∑ j ∈ Finset.range (m + 1),
            denominatorDescentTerm C N q z f m j) /
        algebraMap R L q ^ (2 * m + 1) := by
  rw [B.eval_eq_sum_range' (Nat.lt_succ_of_le hBdegree), Finset.mul_sum]
  simp only [map_sum, denominatorDescentTerm, map_mul, map_pow]
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hj_le : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hcoefficient :
      B.coeff j =
        algebraMap R L (clearedEval (C j) N q (m - j)) /
          algebraMap R L q ^ (2 * (m - j)) := by
    rw [hcoeff j hj_le, aeval_def, eval₂_eq_eval_map]
    exact (map_clearedEval_div_pow (K := K) (R := R) (L := L)
      (C j) N q (m - j) (hCdegree j hj_le) hq).symm
  rw [hcoefficient]
  have hqMap : algebraMap R L q ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R L).ne hq
  field_simp [hqMap]
  have hexponent : 1 + 2 * (m - j) + 2 * j = 2 * m + 1 := by omega
  have hqpow :
      algebraMap R L q ^ (2 * m + 1) =
        algebraMap R L q * algebraMap R L q ^ (2 * (m - j)) *
          algebraMap R L q ^ (2 * j) := by
    rw [← hexponent, pow_add, pow_add, pow_one]
  rw [hqpow]
  ring

/-- Valuation-free Step 5.

Each coefficient of `B` is represented by a polynomial in `N / q^2` whose
degree is exactly the amount needed for the common-denominator calculation.
The `j = 0` summand has a numerator coprime to the nonunit `q`; every positive
`j` summand contains `q^(2*j)`.  Hence `(z/q) * B(f)` is not in the embedded
base ring.-/
theorem mul_eval_not_mem_base
    {K R L : Type*} [Field K] [CommRing R] [IsDomain R] [Field L]
    [Algebra K R] [Algebra R L] [Algebra K L] [IsScalarTower K R L]
    [IsFractionRing R L]
    (q z N f : R) (B : L[X]) (m : ℕ) (C : ℕ → K[X])
    (hq : q ≠ 0) (hqNonunit : ¬ IsUnit q)
    (hzq : IsCoprime z q) (hNq : IsCoprime N q)
    (hBdegree : B.natDegree = m)
    (hcoeff : ∀ j ≤ m,
      B.coeff j = aeval
        (algebraMap R L N / algebraMap R L q ^ 2) (C j))
    (hCdegree : ∀ j ≤ m, (C j).natDegree = m - j)
    (hClead : ∀ j ≤ m, (C j).leadingCoeff ≠ 0) :
    (algebraMap R L z / algebraMap R L q) *
        B.eval (algebraMap R L f) ∉ Set.range (algebraMap R L) := by
  rw [mul_eval_eq_common_denominator q z N f B m C hq
    hBdegree.le hcoeff (fun j hj ↦ (hCdegree j hj).le)]
  rw [← map_pow]
  apply JacobianTwo.QuadraticDenominator.unique_survivor_fraction_not_mem_base
      (i₀ := 0)
  · simp
  · exact hq
  · omega
  · simp only [denominatorDescentTerm, mul_zero, pow_zero, mul_one, Nat.sub_zero]
    exact not_dvd_mul_clearedEval (C 0) N q z m hqNonunit hzq hNq
      (hCdegree 0 (Nat.zero_le m)) (hClead 0 (Nat.zero_le m))
  · intro j hj hj0
    have hexponent : 2 * j ≠ 0 := by
      have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      omega
    exact (dvd_mul_of_dvd_right (dvd_pow_self q hexponent)
      (z * f ^ j)).mul_right _

/-- Existential-witness form of `mul_eval_not_mem_base`.  This matches the
output shape of the coefficient recurrence: a witness polynomial may be
chosen independently for each coefficient.-/
theorem mul_eval_not_mem_base_of_exists
    {K R L : Type*} [Field K] [CommRing R] [IsDomain R] [Field L]
    [Algebra K R] [Algebra R L] [Algebra K L] [IsScalarTower K R L]
    [IsFractionRing R L]
    (q z N f : R) (B : L[X]) (m : ℕ)
    (hq : q ≠ 0) (hqNonunit : ¬ IsUnit q)
    (hzq : IsCoprime z q) (hNq : IsCoprime N q)
    (hBdegree : B.natDegree = m)
    (hwitness : ∀ j ≤ m, ∃ Cj : K[X],
      B.coeff j = aeval
          (algebraMap R L N / algebraMap R L q ^ 2) Cj ∧
        Cj.natDegree = m - j ∧ Cj.leadingCoeff ≠ 0) :
    (algebraMap R L z / algebraMap R L q) *
        B.eval (algebraMap R L f) ∉ Set.range (algebraMap R L) := by
  classical
  let C : ℕ → K[X] := fun j ↦
    if hj : j ≤ m then Classical.choose (hwitness j hj) else 0
  have hspec (j : ℕ) (hj : j ≤ m) :
      B.coeff j = aeval
          (algebraMap R L N / algebraMap R L q ^ 2) (C j) ∧
        (C j).natDegree = m - j ∧ (C j).leadingCoeff ≠ 0 := by
    simp only [C, dite_eq_left hj]
    exact Classical.choose_spec (hwitness j hj)
  exact mul_eval_not_mem_base q z N f B m C hq hqNonunit hzq hNq
    hBdegree (fun j hj ↦ (hspec j hj).1)
    (fun j hj ↦ (hspec j hj).2.1) (fun j hj ↦ (hspec j hj).2.2)

end JacobianTwo.QuadraticDenominatorDescent
