/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Algebra.GroupWithZero.Divisibility
import Tengoku.Seed.Algebra.Polynomial.Coeff
import Tengoku.Seed.Algebra.Polynomial.Degree.Operations
import Tengoku.Seed.Algebra.Polynomial.Monic
import Tengoku.Seed.RingTheory.Ideal.Operations
import Tengoku.Seed.RingTheory.Ideal.Span
import Tengoku.Seed.RingTheory.Polynomial.Eisenstein.Basic
import Tengoku.Seed.RingTheory.Polynomial.GaussLemma

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Eisenstein binomials from a prime parameter

A positive-power binomial `X ^ n - C π` is Eisenstein at the principal
ideal of a prime element. In an integrally closed domain, its image in
the fraction field is therefore irreducible. These inputs require no
valuation, residue-field comparison, or prescribed extension degree.
-/

namespace ValuationTheory.DiscreteValuationField

open Polynomial
open scoped Polynomial

universe u v

variable {R : Type u} [CommRing R] [IsDomain R]

/-- A prime parameter makes a positive-power binomial Eisenstein.
@isnad1 id=iseisens.2h3v.s7.9b8a6acee0e2 from=translated src=- shape=0779f32d vocab=86b969a3
-/
theorem X_pow_sub_C_isEisensteinAt_of_prime_parameter
    (π : R) (hπ : Prime π) (n : ℕ) (hn : 0 < n) :
    (X ^ n - C π).IsEisensteinAt (Ideal.span ({π} : Set R)) := by
  have hP : (Ideal.span ({π} : Set R)).IsPrime :=
    (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  refine (monic_X_pow_sub_C π hn.ne').isEisensteinAt_of_mem_of_notMem
    hP.ne_top ?_ ?_
  · intro i hi
    rw [natDegree_X_pow_sub_C] at hi
    rw [Ideal.mem_span_singleton]
    have hdiv : π ∣ (if i = 0 then π else 0) := by
      split_ifs
      · exact dvd_rfl
      · exact dvd_zero π
    simpa only [coeff_sub, coeff_X_pow, ite_eq_right (Nat.ne_of_lt hi),
      coeff_C, zero_sub, dvd_neg] using hdiv
  · rw [coeff_sub, coeff_X_pow, ite_eq_right (Nat.ne_of_lt hn),
      coeff_C_zero, zero_sub, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, dvd_neg]
    intro hdiv
    have hbad : 2 ≤ 1 :=
      (pow_dvd_pow_iff (a := π) (n := 2) (m := 1)
        hπ.ne_zero hπ.not_isUnit).mp (by simpa only [pow_one] using hdiv)
    exact (by decide : ¬ (2 ≤ 1)) hbad

/-- The Eisenstein binomial is irreducible over the fraction field.
@isnad1 id=irreduci.2h4v.s8.0015d48f6262 from=translated src=- shape=b0a534a3 vocab=a0f6bf9e
-/
theorem X_pow_sub_C_irreducible_of_prime_parameter
    [IsIntegrallyClosed R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Prime π) (n : ℕ) (hn : 0 < n) :
    Irreducible (X ^ n - C (algebraMap R K π)) := by
  have hmonic : (X ^ n - C π).Monic := monic_X_pow_sub_C π hn.ne'
  have hirr : Irreducible (X ^ n - C π) :=
    (X_pow_sub_C_isEisensteinAt_of_prime_parameter π hπ n hn).irreducible
      ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ) hmonic.isPrimitive
      (by rw [natDegree_X_pow_sub_C]; exact hn)
  have hmap : Irreducible ((X ^ n - C π).map (algebraMap R K)) :=
    hmonic.irreducible_iff_irreducible_map_fraction_map.mp hirr
  simpa only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C] using hmap

end ValuationTheory.DiscreteValuationField
