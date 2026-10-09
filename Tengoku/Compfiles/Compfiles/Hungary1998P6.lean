/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

module

public import Tengoku

@[expose] public section

/-!
# Hungarian Mathematical Olympiad 1998, Problem 6

Let x, y, z be integers with z > 1. Show that

 (x + 1)² + (x + 2)² + ... + (x + 99)² ≠ yᶻ.
-/

namespace Hungary1998P6

/--
@isnad1 id=eq.0h1v.s6.ff4fbaaee3d7 from=translated src=- shape=82ec0875 vocab=fa4996af
-/
lemma sum_range_square_mul_six (n : ℕ) :
    (∑i ∈ Finset.range n, (i + 1)^2) * 6 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    ring

/--
@isnad1 id=eq.0h1v.s6.7c62b79ab53a from=translated src=- shape=650e1a43 vocab=0c81a662
-/
lemma sum_range_square (n : ℕ) :
    ∑i ∈ Finset.range n, (i + 1)^2 = n * (n + 1) * (2 * n + 1)/6 :=
  by rw [← sum_range_square_mul_six n, Nat.mul_div_cancel]
     norm_num

/--
@isnad1 id=eq.0h1v.s6.54b0799eb2a7 from=translated src=- shape=11e43f23 vocab=49556e09
-/
lemma cast_sum_square (n : ℕ) :
  ∑i ∈ Finset.range n, ((i:ℤ)+1)^2 =
   (((∑i ∈ Finset.range n, (i+1)^2) : ℕ) : ℤ) := by norm_cast

end Hungary1998P6
