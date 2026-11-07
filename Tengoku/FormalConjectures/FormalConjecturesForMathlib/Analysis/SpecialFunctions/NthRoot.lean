/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Tengoku

@[expose] public section

/-!
# nth root operations

This file provides `Real.nthRoot n` to compute `ⁿ√`,
which operates as expected on negative values when `n` is odd.
The trap this avoids is that using `rpow`, `(-8 : ℝ) ^ (1/3 : ℝ) = 1`.

This is being upstreamed to Mathlib in leanprover-community/mathlib4#26935.
-/

namespace Real

noncomputable def nthRoot (n : ℕ) (r : ℝ) : ℝ :=
  if Even n then r ^ (n⁻¹ : ℝ) else SignType.sign r ^ n * abs r ^ (n⁻¹ : ℝ)

/--
@isnad1 id=eq.1h2v.s4.ff9008d0a7a3 from=translated src=- shape=ee12417a vocab=99eda140
-/
theorem nthRoot_of_even {n : ℕ} (hn : Even n) (r : ℝ) : nthRoot n r = r ^ (n⁻¹ : ℝ) :=
  ite_eq_left hn

/--
@isnad1 id=eq.1h2v.s6.dddeb35a3604 from=translated src=- shape=95a9aa20 vocab=59666bc7
-/
theorem nthRoot_of_odd {n : ℕ} (hn : Odd n) (r : ℝ) :
    nthRoot n r = SignType.sign r ^ n * abs r ^ (n⁻¹ : ℝ) :=
  ite_eq_right <| Nat.not_even_iff_odd.mpr hn

/--
@isnad1 id=eq.2h2v.s6.9effefce6df4 from=translated src=- shape=7efd2f3c vocab=fb48f0b8
-/
theorem nthRoot_of_odd_of_nonpos {n : ℕ} (hn : Odd n) {r : ℝ} (hr : r ≤ 0) :
    nthRoot n r = (-1) ^ n * (-r) ^ (n⁻¹ : ℝ) := by
  rw [nthRoot_of_odd hn]
  obtain rfl | hr := hr.eq_or_lt
  · simp
    have hn0 : n ≠ 0 := Nat.ne_of_odd_add hn
    rw [zero_pow hn0, zero_rpow (inv_ne_zero <| mod_cast hn0)]
    right
    rfl
  · rw [abs_of_neg hr, _root_.sign_neg hr]
    simp

/--
@isnad1 id=eq.1h2v.s5.389e5569113a from=translated src=- shape=d443ba7c vocab=174426f3
-/
theorem nthRoot_of_nonneg {n : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    nthRoot n r = r ^ (n⁻¹ : ℝ) := by
  cases Nat.even_or_odd n with
  | inl he =>
    rw [nthRoot_of_even he]
  | inr ho =>
    have hn0 : n ≠ 0 := Nat.ne_of_odd_add ho
    rw [nthRoot_of_odd ho, abs_of_nonneg hr]
    obtain rfl | hr := hr.eq_or_lt
    · simp [hn0]
    rw [_root_.sign_pos hr]
    simp

/--
@isnad1 id=eq.1h2v.s4.0649dba0d17e from=translated src=- shape=dd8a354a vocab=7b9ffe74
-/
@[simp]
theorem nthRoot_neg_of_odd {n : ℕ} (hn : Odd n) {r : ℝ} :
    nthRoot n (-r) = -nthRoot n r := by
  obtain hr | hr := le_total r 0
  · rw [nthRoot_of_odd_of_nonpos hn hr, hn.neg_one_pow, neg_one_mul, neg_neg,
      nthRoot_of_nonneg (neg_nonneg.mpr hr)]
  · rw [nthRoot_of_odd_of_nonpos hn (neg_nonpos.mpr hr), hn.neg_one_pow, neg_one_mul, neg_neg,
      nthRoot_of_nonneg hr]

/--
@isnad1 id=eq.1h2v.s5.5b7df5aa5e6a from=translated src=- shape=b1ee2ec5 vocab=fab6a5c7
-/
theorem pow_nthRoot {n : ℕ} (r : ℝ) (h : (n ≠ 0 ∧ 0 ≤ r) ∨ Odd n) : nthRoot n r ^ n = r := by
  cases Nat.even_or_odd n with
  | inl he =>
    obtain ⟨hn, hr⟩ := h.resolve_right (Nat.not_odd_iff_even.mpr he)
    rw [nthRoot_of_even he, rpow_inv_natCast_pow hr hn]
  | inr ho =>
    have hn : n ≠ 0 := by exact Nat.ne_of_odd_add ho
    rw [nthRoot_of_odd ho, mul_pow, ←pow_mul, rpow_inv_natCast_pow (abs_nonneg _) hn,
      ←SignType.coe_pow, SignType.pow_odd, sign_mul_abs]
    exact ho.mul ho

/--
@isnad1 id=eq.1h2v.s5.00111663a323 from=translated src=- shape=8377d191 vocab=fab6a5c7
-/
theorem nthRoot_pow {n : ℕ} (r : ℝ) (h : (n ≠ 0 ∧ 0 ≤ r) ∨ Odd n) : nthRoot n (r ^ n) = r := by
  cases Nat.even_or_odd n with
  | inl he =>
    obtain ⟨hn, hr⟩ := h.resolve_right (Nat.not_odd_iff_even.mpr he)
    rw [nthRoot_of_even he, pow_rpow_inv_natCast hr hn]
  | inr ho =>
    have hn : n ≠ 0 := Nat.ne_of_odd_add ho
    rw [nthRoot_of_odd ho, abs_pow, pow_rpow_inv_natCast (abs_nonneg _) hn,
      ←SignType.coe_pow, sign_pow, ← pow_mul, SignType.pow_odd, sign_mul_abs]
    exact ho.mul ho

/--
@isnad1 id=eq.3h3v.s5.eebad790e135 from=translated src=- shape=b9be81c9 vocab=c09ef118
-/
theorem nthRoot_mul_of_even_of_nonneg {n : ℕ} {a b : ℝ} (hn : Even n)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.nthRoot n (a * b) = Real.nthRoot n a * Real.nthRoot n b := by
  simp only [Real.nthRoot_of_even hn, Real.mul_rpow ha hb]

/--
@isnad1 id=eq.1h3v.s5.53b9440fdf25 from=translated src=- shape=b6215fda vocab=389b88ca
-/
theorem nthRoot_mul_of_odd {n : ℕ} {a b : ℝ} (hn : Odd n) :
    nthRoot n (a * b) = nthRoot n a * nthRoot n b := by
  simp [Real.nthRoot_of_odd hn, sign_mul, SignType.coe_mul, abs_mul,
  Real.mul_rpow (abs_nonneg a) (abs_nonneg b)]
  ring

end Real
