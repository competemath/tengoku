/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Tengoku.LeanPool.LeanPool.LeanPolyABC.Lib.Radical
public import Tengoku.LeanPool.LeanPool.LeanPolyABC.Lib.Wronskian
public import Tengoku

/-!
# LeanPool.LeanPolyABC.Lib.DivRadical
-/

@[expose] public section

/-
On `a.divRadical = a / radical a`. The purpose of this file is to prove our "main lemma" that
`a.divRadical` divides `a'` for any nonzero polynomial `a`.
The proof is based on induction (`UniqueFactorizationMonoid.induction_on_coprime`).
-/
noncomputable section

open scoped Polynomial

open Polynomial UniqueFactorizationMonoid

namespace LeanPolyABC

namespace Polynomial

variable {k : Type _} [Field k] [DecidableEq k]

/--
For a given polynomial `a`, `a.divRadical` is `a` divided by its radical `radical a`.
This is the key to our implementation. -/
def divRadical (a : k[X]) : k[X] :=
  a / radical a

/--
@isnad1 id=eq.0h2v.s7.6d9b3faf965c from=translated src=- shape=d8cdcfc4 vocab=f8065b86
-/
theorem hMul_radical_divRadical (a : k[X]) : radical a * divRadical a = a := by
  rw [divRadical, ← EuclideanDomain.mul_div_assoc _ (radical_dvd_self a)]
  exact mul_div_cancel_left₀ a (radical_ne_zero a)

/--
@isnad1 id=ne.1h2v.s6.8f22371e0b54 from=translated src=- shape=75826e8b vocab=738532e5
-/
theorem divRadical_ne_zero {a : k[X]} (ha : a ≠ 0) : divRadical a ≠ 0 := by
  rw [← hMul_radical_divRadical a] at ha
  exact right_ne_zero_of_mul ha

/--
@isnad1 id=isunit.1h2v.s6.dd1d1f93e0c3 from=translated src=- shape=ec38813f vocab=118b442f
-/
theorem divRadical_isUnit {u : k[X]} (hu : IsUnit u) : IsUnit (divRadical u) := by
  rwa [divRadical, radical_unit_eq_one hu, EuclideanDomain.div_one]

theorem eq_divRadical {a x : k[X]} (h : radical a * x = a) : x = divRadical a := by
  apply EuclideanDomain.eq_div_of_mul_eq_left (radical_ne_zero a)
  rwa [mul_comm]

/--
@isnad1 id=eq.1h3v.s7.f94b76b7e640 from=translated src=- shape=6a18f0e9 vocab=e9e5ad8a
-/
theorem divRadical_hMul {a b : k[X]} (hc : IsCoprime a b) :
    divRadical (a * b) = divRadical a * divRadical b := by
  by_cases ha : a = 0
  · rw [ha, MulZeroClass.zero_mul, divRadical, EuclideanDomain.zero_div, MulZeroClass.zero_mul]
  by_cases hb : b = 0
  · rw [hb, MulZeroClass.mul_zero, divRadical, EuclideanDomain.zero_div, MulZeroClass.mul_zero]
  symm; apply eq_divRadical
  rw [radical_hMul hc]
  rw [mul_mul_mul_comm, hMul_radical_divRadical, hMul_radical_divRadical]

/--
@isnad1 id=dvd.0h2v.s6.daa960698caf from=translated src=- shape=e3c4a321 vocab=4176c57b
-/
theorem divRadical_dvd_self (a : k[X]) : divRadical a ∣ a := by
  rw [divRadical]
  exact EuclideanDomain.div_dvd_of_dvd (radical_dvd_self a)

/- Main lemma: a / rad(a) ∣ a'.
Proof uses `induction_on_coprime` of `UniqueFactorizationMonoid`.
-/

/--
@isnad1 id=dvd.0h2v.s8.1a11c6d78f54 from=translated src=- shape=0f37e49f vocab=19ed9b19
-/
theorem divRadical_dvd_derivative (a : k[X]) : divRadical a ∣ derivative a := by
  induction a using induction_on_coprime with
  | h0 =>
    simp_all
  | @h1 a ha =>
    exact (divRadical_isUnit ha).dvd
  | @hpr p i hp =>
    cases i with
    | zero =>
      simp_all
    | succ i =>
      rw [← mul_dvd_mul_iff_left (radical_ne_zero (p ^ i.succ)), hMul_radical_divRadical,
        radical_prime_pow hp i.succ_pos, derivative_pow_succ, ← mul_assoc]
      apply dvd_mul_of_dvd_left
      rw [mul_comm, mul_assoc]
      apply dvd_mul_of_dvd_right
      rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero i hp.ne_zero), dvd_normalize_iff]
  | @hcp x y hpxy hx hy =>
    -- If it holds for coprime pair a and b, then it also holds for a * b.
    have hc : IsCoprime x y :=
      EuclideanDomain.isCoprime_of_dvd
        (fun ⟨hx, hy⟩ => not_isUnit_zero (hpxy (zero_dvd_iff.mpr hx) (zero_dvd_iff.mpr hy)))
        fun p hp _ hpx hpy => hp (hpxy hpx hpy)
    rw [divRadical_hMul hc, derivative_mul]
    exact dvd_add (mul_dvd_mul hx (divRadical_dvd_self y))
      (mul_dvd_mul (divRadical_dvd_self x) hy)

/--
@isnad1 id=dvd.0h3v.s6.43338d7518a3 from=translated src=- shape=bce38726 vocab=8bef674d
-/
theorem divRadical_dvd_wronskian_left (a b : k[X]) : divRadical a ∣ wronskian a b := by
  rw [wronskian]
  exact dvd_sub (dvd_mul_of_dvd_left (divRadical_dvd_self a) _)
    (dvd_mul_of_dvd_left (divRadical_dvd_derivative a) _)

/--
@isnad1 id=dvd.0h3v.s6.d8f5e4a39a61 from=translated src=- shape=1edd5f04 vocab=8bef674d
-/
theorem divRadical_dvd_wronskian_right (a b : k[X]) : divRadical b ∣ wronskian a b := by
  rw [wronskian_anticomm, dvd_neg]
  exact divRadical_dvd_wronskian_left b a

end Polynomial

end LeanPolyABC
