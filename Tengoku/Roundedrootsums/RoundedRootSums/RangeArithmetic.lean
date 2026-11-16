/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Arithmetic lemmas for finite sums

Auxiliary identities for finite arithmetic sums that are used throughout
the project, including formulas for constant sums, odd numbers,
and sums of squares.
-/

namespace RoundedRootSums

/--
The sum of a constant over `Finset.range n`.
@isnad1 id=eq.0h2v.s4.4052b7136845 from=translated src=- shape=6f868893 vocab=2a31acb5
-/
theorem sum_const
    (n c : Nat) :
    Finset.sum (Finset.range n) (fun _ => c) = n * c := by
  simp

/--
The sum of the integers from `0` through `n - 1`.
@isnad1 id=eq.0h1v.s5.2a8798830f95 from=translated src=- shape=48599de8 vocab=2cb4d71d
-/
theorem sum_id_range
    (n : Nat) :
    Finset.sum (Finset.range n) (fun i => i) =
      n * (n - 1) / 2 := by
  exact Finset.sum_range_id n

/--
The cardinality of `Finset.range n`.
@isnad1 id=eq.0h1v.s3.e4d71354edd2 from=translated src=- shape=9baae94e vocab=9c161d82
-/
theorem card_range
    (n : Nat) :
    (Finset.range n).card = n := by
  simp

/--
The sum of the first `n` odd positive integers.
@isnad1 id=eq.0h1v.s5.3ad4d12df1b7 from=translated src=- shape=7dab34ef vocab=fa4996af
-/
theorem sum_odd_range
    (n : Nat) :
    Finset.sum (Finset.range n)
        (fun i => 2 * i + 1) =
      n ^ 2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      simp [ih]
      ring

/--
Splitting the sum of squares at the final term.
@isnad1 id=eq.0h1v.s6.8ee6cb27a0db from=translated src=- shape=48be231d vocab=3e949ef4
-/
theorem sum_squares_range_succ
    (n : Nat) :
    Finset.sum (Finset.range (n + 1))
        (fun i => i ^ 2) =
      Finset.sum (Finset.range n)
        (fun i => i ^ 2) + n ^ 2 := by
  rw [Finset.sum_range_succ]

/--
Multiplying the sum of squares by six yields the classical polynomial.
@isnad1 id=eq.0h1v.s6.2af8f4231d4e from=translated src=- shape=ad693e16 vocab=fa4996af
-/
theorem six_mul_sum_squares_range_succ
    (n : Nat) :
    6 * Finset.sum (Finset.range (n + 1))
        (fun i => i ^ 2) =
      n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [Nat.mul_add]
      rw [ih]
      ring

/--
Closed formula for the sum of squares over `Finset.range (n + 1)`.
@isnad1 id=eq.0h1v.s6.67bace1e4bcd from=translated src=- shape=59e17e8f vocab=0c81a662
-/
theorem sum_squares_range_closed
    (n : Nat) :
    Finset.sum (Finset.range (n + 1))
        (fun i => i ^ 2) =
      n * (n + 1) * (2 * n + 1) / 6 := by
  apply Nat.eq_div_of_mul_eq_right
  · norm_num
  · exact six_mul_sum_squares_range_succ n

/--
The sum of squares from `1` through `r` equals the corresponding sum over
`Finset.range (r + 1)`, since the additional term is `0 ^ 2`.
@isnad1 id=eq.0h1v.s6.d4d01b90d257 from=translated src=- shape=eae0691b vocab=87234601
-/
theorem sum_squares_Icc_eq_range
    (r : Nat) :
    Finset.sum (Finset.Icc 1 r)
        (fun i => i ^ 2) =
      Finset.sum (Finset.range (r + 1))
        (fun i => i ^ 2) := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [Finset.sum_range_succ]
      rw [ih]

/--
Closed formula for the sum of squares from `1` through `r`.
@isnad1 id=eq.0h1v.s6.2c4075d96553 from=translated src=- shape=1c3c70c0 vocab=a859d66e
-/
theorem sum_squares_Icc_one
    (r : Nat) :
    Finset.sum (Finset.Icc 1 r)
        (fun i => i ^ 2) =
      r * (r + 1) * (2 * r + 1) / 6 := by
  rw [sum_squares_Icc_eq_range]
  exact sum_squares_range_closed r

end RoundedRootSums
