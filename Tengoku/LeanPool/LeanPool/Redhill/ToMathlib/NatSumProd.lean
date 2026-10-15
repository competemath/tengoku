/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Tengoku

/-!
# Lemmas on when sums of natural numbers are less than their products

These are used when proving the subsum condition in the odd case.
-/

@[expose] public section

namespace Nat

/-- The sum of three natural numbers is strictly less than their product
if they are lower-bounded by 3, 3, 1 respectively.
@isnad1 id=lt.3h3v.s6.13e76c6fef4f from=translated src=- shape=5a144c5c vocab=923b6325
-/
lemma add3_lt_mul3 {a b c : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 1 ≤ c) : a + b + c < a * b * c := by
  induction a, ha using le_induction <;> induction b, hb using le_induction <;> lia

end Nat
