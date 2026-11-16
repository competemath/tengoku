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
The sum of a constant over `Finset.range n`.-/
theorem sum_const
    (n c : Nat) :
    Finset.sum (Finset.range n) (fun _ => c) = n * c := by
  simp

/--
The sum of the integers from `0` through `n - 1`.-/
theorem sum_id_range
    (n : Nat) :
    Finset.sum (Finset.range n) (fun i => i) =
      n * (n - 1) / 2 := by
  exact Finset.sum_range_id n

/--
The cardinality of `Finset.range n`.-/
theorem card_range
    (n : Nat) :
    (Finset.range n).card = n := by
  simp

/--
The sum of the first `n` odd positive integers.-/
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
Splitting the sum of squares at the final term.-/
theorem sum_squares_range_succ
    (n : Nat) :
    Finset.sum (Finset.range (n + 1))
        (fun i => i ^ 2) =
      Finset.sum (Finset.range n)
        (fun i => i ^ 2) + n ^ 2 := by
  rw [Finset.sum_range_succ]

/--
Multiplying the sum of squares by six yields the classical polynomial.-/
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
Closed formula for the sum of squares over `Finset.range (n + 1)`.-/
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
`Finset.range (r + 1)`, since the additional term is `0 ^ 2`.-/
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
Closed formula for the sum of squares from `1` through `r`.-/
theorem sum_squares_Icc_one
    (r : Nat) :
    Finset.sum (Finset.Icc 1 r)
        (fun i => i ^ 2) =
      r * (r + 1) * (2 * r + 1) / 6 := by
  rw [sum_squares_Icc_eq_range]
  exact sum_squares_range_closed r

end RoundedRootSums
