/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh, Ilmārs Cīrulis
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1997, Problem 5

Determine all pairs of integers 1 ≤ a,b that satisfy a ^ (b ^ 2) = b ^ a.
-/

namespace Imo1997P5

/--
@isnad1 id=lt.2h2v.s5.cbdb67cfb89d from=translated src=- shape=cf862199 vocab=33c613ef
-/
lemma ineq₁ {n b : ℕ} (hb : 2 ≤ b) (hn : 5 ≤ n) : n < b ^ (n - 2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num; linarith [Nat.pow_le_pow_left hb 3]
  | succ n hn iH => rw [show n + 1 - 2 = n - 2 + 1 by lia, Nat.pow_succ]; nlinarith

/--
@isnad1 id=lt.2h2v.s6.2cddf6feecb4 from=translated src=- shape=cdb3192a vocab=2a3f5b88
-/
lemma ineq₂ {n b : ℕ} (hb : 2 ≤ b) (hn : 5 ≤ n) : n * b ^ 2 < b ^ n := by
  nth_rw 2 [show n = n - 2 + 2 by lia]
  rw [Nat.pow_add]
  nlinarith [ineq₁ hb hn]

/--
@isnad1 id=lt.2h3v.s5.d9e1827cedff from=translated src=- shape=b6df5b40 vocab=3f16b8dd
-/
lemma ineq₃ {x y b : ℕ} (hb : 2 ≤ b) (hxy : x < y) : b + x < b ^ 2 * y := by
  induction b, hb using Nat.le_induction <;> nlinarith

/--
@isnad1 id=lt.1h2v.s5.c5b41adc2389 from=translated src=- shape=75fb9856 vocab=2a3f5b88
-/
lemma ineq₄ {b : ℕ} (n : ℕ) (hb : 2 ≤ b) : b * n < (b ^ n) ^ 2 := by
  induction n with
  | zero => simp
  | succ n iH => ring_nf at *; exact ineq₃ hb iH

/--
@isnad1 id=or.1h2v.s6.c7f619a76225 from=translated src=- shape=4dce3f40 vocab=45880164
-/
lemma aux₁ {n b : ℕ} (h : n * b ^ 2 = b ^ n) : b ≤ 1 ∨ n ≤ 4 := by grind [ineq₂]

/--
@isnad1 id=le.1h2v.s5.dfee3d6213a7 from=translated src=- shape=2afbac45 vocab=45880164
-/
lemma aux₂ {n b : ℕ} (h : b * n = (b ^ n) ^ 2) : b ≤ 1 := by grind [ineq₄]

/--
@isnad1 id=dvd.2h5v.s6.c5f038ddc41c from=translated src=- shape=c3ec4d2d vocab=c60b803b
-/
lemma aux₃ {n a b c d : ℕ} (hb : b ≠ 0) (h : c ^ b = d ^ b * n ^ a) : d ∣ c :=
  (Nat.pow_dvd_pow_iff hb).mp (Dvd.intro (n ^ a) h.symm)

abbrev solution_set : Set (ℕ × ℕ) := {(1, 1), (16, 2), (27, 3)}

end Imo1997P5
