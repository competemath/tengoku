/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Tengoku

/-!
# LeanPool.LeanPolyABC.Lib.Wronskian
-/

@[expose] public section

noncomputable section

open scoped Polynomial

open Polynomial

namespace LeanPolyABC

variable {R : Type _} [CommRing R]

/-- Wronskian: W(a, b) = ab' - a'b. -/
def wronskian (a b : R[X]) : R[X] :=
  a * derivative b - derivative a * b

/--
@isnad1 id=eq.0h2v.s6.6797ec34cd1e from=translated src=- shape=4f58ea2b vocab=8276a951
-/
@[simp]
theorem wronskian_zero_left (a : R[X]) : wronskian 0 a = 0 := by
  simp_rw [wronskian]; simp only [MulZeroClass.zero_mul, derivative_zero, sub_self]

/--
@isnad1 id=eq.0h2v.s6.bd161fee62eb from=translated src=- shape=8390963c vocab=8276a951
-/
@[simp]
theorem wronskian_zero_right (a : R[X]) : wronskian a 0 = 0 := by
  simp_rw [wronskian]; simp only [derivative_zero, MulZeroClass.mul_zero, sub_self]

/--
@isnad1 id=eq.0h3v.s6.feaa4b82ca28 from=translated src=- shape=1f35273a vocab=326bccab
-/
theorem wronskian_neg_left (a b : R[X]) : wronskian (-a) b = -wronskian a b := by
  simp_rw [wronskian, derivative_neg]; ring

/--
@isnad1 id=eq.0h3v.s6.195d96c5e72d from=translated src=- shape=718d20ab vocab=326bccab
-/
theorem wronskian_neg_right (a b : R[X]) : wronskian a (-b) = -wronskian a b := by
  simp_rw [wronskian, derivative_neg]; ring

/--
@isnad1 id=eq.0h4v.s6.56a313ce8cb9 from=translated src=- shape=34cbfea2 vocab=71948c9f
-/
theorem wronskian_add_right (a b c : R[X]) :
    wronskian a (b + c) = wronskian a b + wronskian a c := by
  simp_rw [wronskian, derivative_add]; ring

/--
@isnad1 id=eq.0h2v.s5.a37b98b4132d from=translated src=- shape=fd3b89a8 vocab=8276a951
-/
theorem wronskian_self (a : R[X]) : wronskian a a = 0 := by rw [wronskian, mul_comm, sub_self]

/--
@isnad1 id=eq.0h3v.s5.de14be1228c3 from=translated src=- shape=24fc31b9 vocab=326bccab
-/
theorem wronskian_anticomm (a b : R[X]) : wronskian a b = -wronskian b a := by
  rw [wronskian, wronskian]; ring

/--
@isnad1 id=eq.1h4v.s7.8e09d51f69db from=translated src=- shape=1704543e vocab=71948c9f
-/
theorem wronskian_eq_of_sum_zero {a b c : R[X]} (h : a + b + c = 0) :
    wronskian a b = wronskian b c := by
  rw [← neg_eq_iff_add_eq_zero] at h
  rw [← h, wronskian_neg_right, wronskian_add_right, wronskian_self, add_zero, ← wronskian_anticomm]

private theorem degree_ne_bot {a : R[X]} (ha : a ≠ 0) : a.degree ≠ ⊥ := by
  intro h; rw [Polynomial.degree_eq_bot] at h; exact ha h

namespace wronskian

/--
@isnad1 id=lt.2h3v.s7.08cf81b9d00a from=translated src=- shape=fdc3df87 vocab=8a78c537
-/
theorem degree_lt_add {a b : R[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    (wronskian a b).degree < a.degree + b.degree := by
  calc
    (wronskian a b).degree ≤ max (a * derivative b).degree (derivative a * b).degree :=
      Polynomial.degree_sub_le _ _
    _ < a.degree + b.degree := by
      refine max_lt_iff.mpr ⟨?_, ?_⟩
      · refine lt_of_le_of_lt (degree_mul_le a (derivative b)) ?_
        rw [WithBot.add_lt_add_iff_left (degree_ne_bot ha)]
        exact Polynomial.degree_derivative_lt hb
      · refine lt_of_le_of_lt (degree_mul_le (derivative a) b) ?_
        rw [WithBot.add_lt_add_iff_right (degree_ne_bot hb)]
        exact Polynomial.degree_derivative_lt ha

-- Note: the following is false!
-- Counterexample: b = a = 1 →
-- (wronskian a b).natDegree = a.natDegree = b.natDegree = 0
/--
@isnad1 id=lt.1h3v.s6.e012586fbc07 from=translated src=- shape=ed2504b4 vocab=b8d28d57
-/
theorem natDegree_lt_add {a b : R[X]} (hw : wronskian a b ≠ 0) :
    (wronskian a b).natDegree < a.natDegree + b.natDegree := by
  have ha : a ≠ 0 := by intro h; subst h; rw [wronskian_zero_left] at hw; exact hw rfl
  have hb : b ≠ 0 := by intro h; subst h; rw [wronskian_zero_right] at hw; exact hw rfl
  have h := wronskian.degree_lt_add ha hb
  rw [Polynomial.degree_eq_natDegree hw, Polynomial.degree_eq_natDegree ha,
    Polynomial.degree_eq_natDegree hb] at h
  exact_mod_cast h

end wronskian

end LeanPolyABC
