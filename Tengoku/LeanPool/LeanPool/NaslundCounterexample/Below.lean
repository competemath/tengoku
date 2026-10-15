/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import Tengoku.LeanPool.LeanPool.NaslundCounterexample.Polynomials

/-!
# Degree below `m`, internally

The public statements bound degrees with `natDegree f < n`, a comparison of natural numbers. That
formulation cannot express `P_{3,0} = {0}`, because the zero polynomial has natural degree `0`;
and the recursion of the construction starts exactly there. So internally a polynomial has
*degree below `m`* when `degree f < m` in `WithBot ℕ`, where `m = 0` says `f = 0` and no separate
base case is needed. The two agree for `m ≥ 1`, which is where the public statements live.

This file is the toolkit: the coefficient characterisation, the passage to `natDegree`, closure
under the operations the lift performs, and the two multiplication bounds for `P` and `Q`.
-/

@[expose] public section

namespace NaslundCounterexample

open Polynomial

/-- `f` has degree below `m`: membership in `P_{3,m}`, the polynomials of degree less than `m`.
For `m = 0` this says `f = 0`, since `degree 0 = ⊥`. -/
def Below (m : ℕ) (f : (ZMod 3)[X]) : Prop := f.degree < m

/-- Every element of `B` has degree below `m`, that is, `B ⊆ P_{3,m}`. -/
def AllBelow (m : ℕ) (B : Finset (ZMod 3)[X]) : Prop := ∀ f ∈ B, Below m f

/-- Degree below `m` read off the coefficients: all coefficients from `T^m` on vanish.
@isnad1 id=iff.0h2v.s7.f89dd5ad25a2 from=translated src=- shape=bd5f058c vocab=42faa4a4
-/
theorem below_iff_coeff (m : ℕ) (f : (ZMod 3)[X]) : Below m f ↔ ∀ i, m ≤ i → f.coeff i = 0 :=
  degree_lt_iff_coeff_zero f m

/-- The coefficients of a polynomial of degree below `m` vanish from `T^m` on.
@isnad1 id=eq.2h3v.s7.4b837d8a477a from=translated src=- shape=647106aa vocab=42faa4a4
-/
theorem Below.coeff_eq_zero {m : ℕ} {f : (ZMod 3)[X]} (h : Below m f) {i : ℕ} (hi : m ≤ i) :
    f.coeff i = 0 := (below_iff_coeff m f).mp h i hi

/-- `P_{3,0} = {0}`: degree below `0` is exactly being the zero polynomial.
@isnad1 id=iff.0h1v.s7.e80a7f417e10 from=translated src=- shape=c3faff48 vocab=17da9ac8
-/
theorem below_zero_iff (f : (ZMod 3)[X]) : Below 0 f ↔ f = 0 := by
  simp only [Below, Nat.cast_zero, ← degree_eq_bot, Nat.WithBot.lt_zero_iff]

/-- For `m ≥ 1`, degree below `m` is the public bound `natDegree f < m`.
@isnad1 id=iff.1h2v.s6.8edc776a791c from=translated src=- shape=380a6803 vocab=b1ee800e
-/
theorem below_iff_natDegree_lt (m : ℕ) (f : (ZMod 3)[X]) (hm : 1 ≤ m) :
    Below m f ↔ f.natDegree < m := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp only [Below, degree_zero, natDegree_zero]
    exact iff_of_true (WithBot.bot_lt_coe m) hm
  · exact (natDegree_lt_iff_degree_lt hf).symm

/-- For `m ≥ 1`, the internal and the public degree bounds on a finite set agree.
@isnad1 id=iff.1h2v.s5.5410e38ca0fd from=translated src=- shape=68d4eaab vocab=f31c91b2
-/
theorem allBelow_iff_degreeBelow (m : ℕ) (B : Finset (ZMod 3)[X]) (hm : 1 ≤ m) :
    AllBelow m B ↔ DegreeBelow m B :=
  ⟨fun h f hf => (below_iff_natDegree_lt m f hm).mp (h f hf),
    fun h f hf => (below_iff_natDegree_lt m f hm).mpr (h f hf)⟩

/-- A degree bound may be weakened.
@isnad1 id=below.2h3v.s5.2545f278f209 from=translated src=- shape=c3424249 vocab=850342d1
-/
theorem Below.mono {m m' : ℕ} (h : m ≤ m') {f : (ZMod 3)[X]} (hf : Below m f) : Below m' f :=
  lt_of_lt_of_le hf (by exact_mod_cast h)

/-- Degree below `m + 1` is natural degree at most `m`.
@isnad1 id=le.1h2v.s6.3fe8dcc1cb8c from=translated src=- shape=6040a6b3 vocab=345cf52a
-/
theorem Below.natDegree_le {m : ℕ} {f : (ZMod 3)[X]} (h : Below (m + 1) f) : f.natDegree ≤ m :=
  Nat.lt_succ_iff.mp ((below_iff_natDegree_lt (m + 1) f (Nat.succ_le_succ (Nat.zero_le m))).mp h)

/-- The zero polynomial has degree below every `m`, including `m = 0`.
@isnad1 id=below.0h1v.s6.ecb90c537102 from=translated src=- shape=f235a0a0 vocab=17da9ac8
-/
theorem below_zero (m : ℕ) : Below m (0 : (ZMod 3)[X]) := by
  simp only [Below, degree_zero]
  exact WithBot.bot_lt_coe m

/-- Degree at most `m` is degree below `m + 1`.
@isnad1 id=below.1h2v.s6.e73800b7db50 from=translated src=- shape=65801418 vocab=d2acaf7e
-/
theorem below_of_degree_le {m : ℕ} {f : (ZMod 3)[X]} (h : f.degree ≤ m) : Below (m + 1) f :=
  lt_of_le_of_lt h (by exact_mod_cast Nat.lt_succ_self m)

/-- A sum of polynomials of degree below `m` has degree below `m`.
@isnad1 id=below.2h3v.s8.37d9d165dd23 from=translated src=- shape=e97072e7 vocab=fff52168
-/
theorem Below.add {m : ℕ} {f g : (ZMod 3)[X]} (hf : Below m f) (hg : Below m g) :
    Below m (f + g) := lt_of_le_of_lt (degree_add_le f g) (max_lt hf hg)

/-- Negation preserves the degree bound.
@isnad1 id=below.1h2v.s6.16d56c1fc0d5 from=translated src=- shape=491c627f vocab=19e8dc6a
-/
theorem Below.neg {m : ℕ} {f : (ZMod 3)[X]} (hf : Below m f) : Below m (-f) := by
  simpa only [Below, degree_neg] using hf

/-- A difference of polynomials of degree below `m` has degree below `m`.
@isnad1 id=below.2h3v.s8.12953c66db9b from=translated src=- shape=e97072e7 vocab=8385399b
-/
theorem Below.sub {m : ℕ} {f g : (ZMod 3)[X]} (hf : Below m f) (hg : Below m g) :
    Below m (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- A single term `a T^i` with `i < m` has degree below `m`.
@isnad1 id=below.1h3v.s9.61ec1b64cd98 from=translated src=- shape=9b1e3949 vocab=1387a85d
-/
theorem below_C_mul_X_pow (a : ZMod 3) (i m : ℕ) (h : i < m) : Below m (C a * X ^ i) :=
  lt_of_le_of_lt (degree_C_mul_X_pow_le i a) (by exact_mod_cast h)

/-- Multiplying by `P` raises the degree bound by `3`.
@isnad1 id=below.1h2v.s7.293a482f2185 from=translated src=- shape=55cdc9f5 vocab=13f224e3
-/
theorem Below.P_mul {m : ℕ} {f : (ZMod 3)[X]} (h : Below m f) : Below (m + 3) (P * f) := by
  simp only [Below, degree_mul, degree_P]
  rw [show ((m + 3 : ℕ) : WithBot ℕ) = 3 + (m : WithBot ℕ) by push_cast; ring]
  exact WithBot.add_lt_add_left (by decide) h

/-- Multiplying by `Q` raises the degree bound by `6`.
@isnad1 id=below.1h2v.s7.66055b27acd1 from=translated src=- shape=55cdc9f5 vocab=f2810906
-/
theorem Below.Q_mul {m : ℕ} {f : (ZMod 3)[X]} (h : Below m f) : Below (m + 6) (Q * f) := by
  simp only [Below, degree_mul, degree_Q]
  rw [show ((m + 6 : ℕ) : WithBot ℕ) = 6 + (m : WithBot ℕ) by push_cast; ring]
  exact WithBot.add_lt_add_left (by decide) h

end NaslundCounterexample
