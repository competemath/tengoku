/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang

Ideal factorization and primality results for ℤ[√-5].
Ported from the ANT project.
-/
import Tengoku.QuadraticNumberFields.QuadraticNumberFields.Zsqrtd.Ideals

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ideal Factorization in ℤ[√-5]

This file proves the ideal factorization identities and primality results
for the non-UFD ring `ℤ[√-5]`, demonstrating the general theory of
quadratic number fields on a concrete example.

## Main Results

* `factorization_of_two`: `(2) = (2, 1+√-5)²`
* `factorization_of_three`: `(3) = (3, 1+√-5) · (3, 1-√-5)`
* `factorization_of_one_plus_sqrtd`: `(1+√-5) = (2, 1+√-5) · (3, 1+√-5)`
* `factorization_of_one_minus_sqrtd`: `(1-√-5) = (2, 1-√-5) · (3, 1-√-5)`
* `isPrime_span_two_one_plus_sqrtd`: `(2, 1+√-5)` is prime
* `isPrime_span_three_one_plus_sqrtd`: `(3, 1+√-5)` is prime
* `isPrime_span_three_one_minus_sqrtd`: `(3, 1-√-5)` is prime
-/
namespace Tengoku.QuadraticNumberFields end Tengoku.QuadraticNumberFields open Tengoku.QuadraticNumberFields
local notation "ℚ√" d => Qsqrtd d

open Ideal

open scoped QuadraticAlgebra

namespace QuadraticNumberFields.Examples.SqrtNeg5

/-- The working quadratic integer ring `ℤ[√-5]` used in this file.-/
abbrev R := Zsqrtd (-5)

local notation "sqrtd" => Zsqrtd.sqrtd

instance : Fact ((-5 : ℤ) < 0) := ⟨by decide⟩

/-! ## Arithmetic conditions for d = -5 -/

/-- Arithmetic input for the prime `2` in `ℤ[√-5]`: `2 ∣ (-5 - 1)`.
@isnad1 id=dvd.0h0v.s4.94dbe62026b9 from=translated src=- shape=192de4b8 vocab=ab9a9576
-/
lemma neg5_dvd_two : 2 ∣ ((-5 : ℤ) - 1) := ⟨-3, by norm_num⟩

/-- Arithmetic input for the prime `3` in `ℤ[√-5]`: `3 ∣ (-5 - 1)`.
@isnad1 id=dvd.0h0v.s4.c1e46b754ae6 from=translated src=- shape=192de4b8 vocab=ab9a9576
-/
lemma neg5_dvd_three : 3 ∣ ((-5 : ℤ) - 1) := ⟨-2, by norm_num⟩

/-! ## Helper lemmas for factorization proofs -/

private lemma in_span_of_eq
  {x y : R} (h : x = y) (hy : y ∈ (I : Ideal R)) :
  x ∈ I :=
by simpa [h] using hy

/-! ## Ideal factorizations (specific to d = -5) -/

/--
@isnad1 id=eq.0h0v.s9.49d39ca6e1a4 from=translated src=- shape=6be6c4b3 vocab=6de8264e
-/
theorem factorization_of_two :
    span {(2 : R)} = (span {2, 1 + sqrtd}) ^ 2 :=
  -- Instance of the general ramified factorization at `p = 2` (since `-5 ≡ 3 mod 4`).
  Zsqrtd.Ideal.span_two_eq_sq (by decide)

/--
@isnad1 id=eq.0h0v.s9.6ff5eae245c7 from=translated src=- shape=890ae32e vocab=6720f472
-/
theorem factorization_of_three :
    span {(3 : R)} = (span {3, 1 + sqrtd}) * (span {3, 1 - sqrtd}) := by
  -- Instance of the general odd-prime split factorization at `p = 3` (since `3 ∣ -5 - 1`).
  simpa using Zsqrtd.Ideal.span_p_eq_span_mul_span 3 (by decide) neg5_dvd_three

/--
@isnad1 id=eq.0h0v.s9.25e5a9bf11dd from=translated src=- shape=b146005f vocab=d02ae98f
-/
theorem factorization_of_one_plus_sqrtd :
    span {(1 + sqrtd : R)} = (span {2, 1 + sqrtd}) * (span {3, 1 + sqrtd}) := by
  -- Expand the ideal product into the span of four pairwise products
  rw [Ideal.span_pair_mul_span_pair]
  apply _root_.le_antisymm
  · -- Forward inclusion ⟨1+√-5⟩ ⊆ product:
    --   1+√-5 = (1+√-5)·3 - 2·(1+√-5)  (i.e., 3x - 2x = x)
    rw [Ideal.span_singleton_le_iff_mem]
    have one_plus_sqrtd_eq :
        (1 + sqrtd : R) = (1 + sqrtd) * 3 - 2 * (1 + sqrtd) := by ring
    exact in_span_of_eq one_plus_sqrtd_eq
      ((span _).sub_mem (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)))
  · -- Reverse inclusion: each of the four generators is divisible by (1+√-5)
    apply Ideal.span_le_span_singleton_of_forall_dvd
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · -- 2·3 = 6 = (1+√-5)(1-√-5), so (1+√-5) | 6
      exact ⟨1 - sqrtd, by
        ext <;>
          simp [Zsqrtd.sqrtd, QuadraticAlgebra.re_one,
            QuadraticAlgebra.im_one]⟩
    · -- 2·(1+√-5) = (1+√-5)·2
      simp
    · -- (1+√-5)·3
      simp
    · -- (1+√-5)² = (1+√-5)·(1+√-5)
      simp

/--
@isnad1 id=eq.0h0v.s9.f449155ad234 from=translated src=- shape=b146005f vocab=edf2a013
-/
theorem factorization_of_one_minus_sqrtd :
    span {(1 - sqrtd : R)} = (span {2, 1 - sqrtd}) * (span {3, 1 - sqrtd}) := by
  -- Symmetric to factorization_of_one_plus_sqrtd, replacing √-5 by -√-5
  rw [Ideal.span_pair_mul_span_pair]
  apply _root_.le_antisymm
  · -- Forward inclusion: 1-√-5 = (1-√-5)·3 - 2·(1-√-5)
    rw [Ideal.span_singleton_le_iff_mem]
    have one_mins_sqrtd_eq :
        (1 - sqrtd : R) = (1 - sqrtd) * 3 - 2 * (1 - sqrtd) := by ring
    exact in_span_of_eq one_mins_sqrtd_eq
      ((span _).sub_mem (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)))
  · -- Reverse inclusion: each of the four generators is divisible by (1-√-5)
    apply Ideal.span_le_span_singleton_of_forall_dvd
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · -- 2·3 = 6 = (1-√-5)(1+√-5), so (1-√-5) | 6
      exact ⟨1 + sqrtd, by
        ext <;>
          simp [Zsqrtd.sqrtd, QuadraticAlgebra.re_one,
            QuadraticAlgebra.im_one]⟩
    · simp  -- 2·(1-√-5) = (1-√-5)·2
    · simp  -- (1-√-5)·3
    · simp  -- (1-√-5)² = (1-√-5)·(1-√-5)

/-! ## Primality (instantiated from general theory) -/

/--
@isnad1 id=isprime.0h0v.s7.3ce80e1b8975 from=translated src=- shape=18939c67 vocab=32f19636
-/
theorem isPrime_span_two_one_plus_sqrtd :
    IsPrime (span {2, 1 + sqrtd} : Ideal R) :=
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  Zsqrtd.Ideal.isPrime_span_p_one_plus_sqrtd 2 neg5_dvd_two

/--
@isnad1 id=isprime.0h0v.s7.07215f333f15 from=translated src=- shape=18939c67 vocab=32f19636
-/
theorem isPrime_span_three_one_plus_sqrtd :
    IsPrime (span {3, 1 + sqrtd} : Ideal R) :=
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  Zsqrtd.Ideal.isPrime_span_p_one_plus_sqrtd 3 neg5_dvd_three

/--
@isnad1 id=isprime.0h0v.s7.75acf11397d2 from=translated src=- shape=18939c67 vocab=4745bacf
-/
theorem isPrime_span_three_one_minus_sqrtd :
    IsPrime (span {3, 1 - sqrtd} : Ideal R) :=
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  Zsqrtd.Ideal.isPrime_span_p_one_minus_sqrtd 3 neg5_dvd_three

end QuadraticNumberFields.Examples.SqrtNeg5
-- Tengoku: root names of this library moved to Tengoku.QuadraticNumberFields so they do not collide with other libraries (generated)
