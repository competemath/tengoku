/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Tengoku

/-!
# Lemmas on `Int.natAbs`
-/

@[expose] public section

/--
@isnad1 id=le.0h2v.s4.acc8d5b07c3b from=translated src=- shape=a7d54e89 vocab=a6cfba4f
-/
lemma Int.sub_le_add_natAbs {a b : ℤ} : a.natAbs - b.natAbs ≤ (a + b).natAbs := by lia

/--
@isnad1 id=eq.1h2v.s5.bebec89f5379 from=translated src=- shape=21c1836e vocab=b0cd59fa
-/
lemma Int.natAbs_add_of_mul_nonneg {a b : ℤ} (h : 0 ≤ a * b) :
    (a + b).natAbs = a.natAbs + b.natAbs := by
  obtain h | h := Int.mul_nonneg_iff.mp h
  · exact Int.natAbs_add_of_nonneg h.1 h.2
  · exact Int.natAbs_add_of_nonpos h.1 h.2
