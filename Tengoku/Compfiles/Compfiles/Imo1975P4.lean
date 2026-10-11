/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Constantin Seebach
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1975, Problem 4

When $4444^{4444}$ is written in decimal notation, the sum of its digits is $A$.
Let $B$ be the sum of the digits of $A$.
Find the sum of the digits of $B$. ($A$ and $B$ are written in decimal notation.)
-/

namespace Imo1975P4

def A : ℕ := (Nat.digits 10 (4444^4444)).sum

def B : ℕ := (Nat.digits 10 A).sum

abbrev sum_digits_B : ℕ := 7

/-!
We follow the proof from https://prase.cz/kalva/imo/isoln/isoln754.html
-/

/-!
I'd love to have the following theorems in Mathlib :)
-/

/--
@isnad1 id=iff.1h3v.s4.8a7b9d24ac4d from=translated src=- shape=fb8f399f vocab=d1fa3928
-/
theorem Nat.mod_eq_iff_eq {n a b : ℕ} (h : a < n) :
    a % n = b ↔ a = b := by
  rw [(Nat.mod_eq_iff_lt _).mpr h]
  exact Nat.ne_zero_of_lt h

/--
@isnad1 id=iff.2h3v.s4.753bcfd76da3 from=translated src=- shape=225806f1 vocab=745abe38
-/
theorem Nat.modEq_iff_eq_lt (n : ℕ) {a b : ℕ} (ha : a < n) (hb : b < n) :
    a ≡ b [MOD n] ↔ a = b := by
  rw [Nat.ModEq]
  rw [(Nat.mod_eq_iff_lt _).mpr hb]
  · exact mod_eq_iff_eq ha
  · exact Nat.ne_zero_of_lt hb

/--
@isnad1 id=le.1h2v.s5.244542d2b15a from=translated src=- shape=602e474b vocab=75b2cac2
-/
theorem Nat.digits_sum_le_mul_digits_length (n b : ℕ) (hb : 1 < b) : (Nat.digits b n).sum ≤ (Nat.digits b n).length * (b-1) := by
  apply List.sum_le_card_nsmul
  intro x xh
  rw [Nat.le_sub_one_iff_lt (Nat.zero_lt_of_lt hb)]
  apply Nat.digits_lt_base hb xh

/--
@isnad1 id=le.2h2v.s6.03494358bb65 from=translated src=- shape=706a9db8 vocab=d6a8673e
-/
theorem Nat.digits_sum_le_log (n b : ℕ) (hn : n ≠ 0) (hb : 1 < b) : (Nat.digits b n).sum ≤ (Nat.log b n + 1) * (b-1) := by
  rw [← Nat.length_digits _ _ hb hn]
  exact digits_sum_le_mul_digits_length n b hb

/--
@isnad1 id=le.2h3v.s6.5ea3f7e94cb1 from=translated src=- shape=fffb18dd vocab=50b86885
-/
theorem Nat.digits_sum_le_of_le (n b u : ℕ) (hb : 1 < b) (hn : n ≤ u) : (Nat.digits b n).sum ≤ (Nat.clog b u + 1) * (b-1) := by
  by_cases nz : n = 0
  · subst n
    simp
  trans (Nat.log b n + 1) * (b-1)
  · apply Nat.digits_sum_le_log _ _ nz hb
  · rw [mul_le_mul_iff_left₀ (by lia), add_le_add_iff_right]
    apply le_trans (Nat.log_le_clog _ _)
    apply Nat.clog_mono_right _ hn

/--
@isnad1 id=le.1h3v.s5.b39e629e0c3d from=translated src=- shape=8565325f vocab=ebd22af3
-/
theorem Nat.clog_pow_le_clog_mul (a b c : ℕ) (hb : 1 < b) : Nat.clog b (a ^ c) ≤ Nat.clog b a * c := by
  by_cases hc : c = 0
  · subst c
    simp
  rw [Nat.clog_le_iff_le_pow hb, pow_mul, Nat.pow_le_pow_iff_left hc]
  apply Nat.le_pow_clog hb

end Imo1975P4
