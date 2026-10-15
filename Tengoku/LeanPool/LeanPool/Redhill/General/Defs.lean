/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Tengoku.LeanPool.LeanPool.Redhill.Common.VWPair
public import Tengoku

/-!
# Definitions for the general case

In this section `h` is the variable such that `tup n F h ∈ factorFreeTuples F (n + 6)`
for sufficiently large `h`.

The lower bound `s` for `primeChain` in `U` was originally `200 * Y F ^ 6`.
-/

@[expose] public section

namespace GeneralCase

open Nat Fin Finset

variable (n : ℕ) (F : Finset ℕ) (h : ℕ)

/-- An optimised version of the paper's `y`. -/
def Y : ℕ := 33330 * (F.erase 0).prod id

/-- `x` in the paper, but using the optimised `y`. -/
def X : ℕ := (Y F + 1) ^ h !

/--
@isnad1 id=le.0h1v.s3.86b84d67e9c4 from=translated src=- shape=b29cab32 vocab=d8affe80
-/
lemma Y_lower_bound {F} : 33330 ≤ Y F := by
  rw [← mul_one 33330]
  exact _root_.mul_le_mul_right (one_le_prod (by grind)) _

/--
@isnad1 id=lt.0h1v.s3.071b32dce1c2 from=translated src=- shape=b29cab32 vocab=814446a3
-/
lemma Y_pos {F} : 0 < Y F := by grind [Y_lower_bound]

/--
@isnad1 id=lt.0h2v.s3.0b817f5fe737 from=translated src=- shape=5066d022 vocab=0bdcdc7b
-/
lemma Y_lt_X {F h} : Y F < X F h :=
  (lt_add_one _).trans_le (le_self_pow (factorial_ne_zero h) _)

/-- The sum of `tup` over all indices save `n` and `n + 1`, i.e. the input `u` to `VWPair`. -/
def U : ℕ := (100 * Y F - 2) * Y F ^ 5 + ∑ i ∈ range n, primeChain (100 * Y F ^ 6) i

/--
@isnad1 id=le.0h2v.s6.eeeac213375e from=translated src=- shape=0a34227f vocab=c49f78e9
-/
lemma U_lower_bound {n F} : (100 * 33330 - 2) * 33330 ^ 5 ≤ U n F := by
  apply (Nat.le_add_right ..).trans'
  gcongr <;> exact Y_lower_bound

/--
@isnad1 id=lt.0h2v.s4.abc37139486a from=translated src=- shape=f8de4f81 vocab=3f12aab0
-/
lemma U_pos {n F} : 0 < U n F := by grind [U_lower_bound]

/-- The `VWPair` generated from the inputs `u = m = U n F`. -/
def VW : VWPair (U n F) (U n F) := .of ..

/-- The sequence of `(n + 6)`-tuples whose tail is in `factorFreeTuples`
and has quality tending to `5 / 4`. -/
def tup (i : Fin (n + 6)) : ℤ :=
  i.addCases (primeChain (100 * Y F ^ 6) ·.1) fun
    | 0 => (VW n F).v
    | 1 => -(VW n F).w
    | 2 => (X F h ^ 2 + 10 * Y F ^ 3) ^ 2
    | 3 => (10 * Y F - 1) * X F h ^ 4
    | 4 => (X F h - Y F) ^ 5
    | 5 => -(X F h + Y F) ^ 5

variable {n F h}

-- Not `@[simp]`: with `Fin.castAdd_to_castSucc` from another pool project in the global
-- simp set, the left-hand side `i.castAdd 6` is rewritten to a `Fin.castSucc` chain, so this
-- lemma's left-hand side is no longer in simp normal form. All call sites invoke it explicitly.
/--
@isnad1 id=eq.0h4v.s5.fd16d7fa06d0 from=translated src=- shape=669a2ed1 vocab=8f93ef3c
-/
lemma tup_castAdd {i : Fin n} :
    tup n F h (i.castAdd 6) = primeChain (100 * Y F ^ 6) i.1 := by
  simp [tup]

/--
@isnad1 id=eq.0h3v.s5.fdb137ec8cad from=translated src=- shape=55cfd974 vocab=16af2ec3
-/
@[simp] lemma tup_natAdd_zero : tup n F h (natAdd n 0) = (VW n F).v := by simp [tup]

/--
@isnad1 id=eq.0h3v.s5.10488863f85c from=translated src=- shape=b64148dc vocab=1ece69ab
-/
@[simp] lemma tup_natAdd_one : tup n F h (natAdd n 1) = -(VW n F).w := by simp [tup]

/--
@isnad1 id=eq.0h3v.s6.b8e39307093a from=translated src=- shape=d4227b37 vocab=3129d3d8
-/
@[simp] lemma tup_natAdd_two : tup n F h (natAdd n 2) = (X F h ^ 2 + 10 * Y F ^ 3) ^ 2 := by
  simp [tup]

/--
@isnad1 id=eq.0h3v.s6.d1f4c4d48465 from=translated src=- shape=f85d3c45 vocab=0925e72e
-/
@[simp] lemma tup_natAdd_three : tup n F h (natAdd n 3) = (10 * Y F - 1) * X F h ^ 4 := by
  simp [tup]

/--
@isnad1 id=eq.0h3v.s6.5d772be8ee77 from=translated src=- shape=5d3ec208 vocab=071bf542
-/
@[simp] lemma tup_natAdd_four : tup n F h (natAdd n 4) = (X F h - Y F) ^ 5 := by simp [tup]

/--
@isnad1 id=eq.0h3v.s6.63f9d960b864 from=translated src=- shape=1b100fb2 vocab=0be9ea32
-/
@[simp] lemma tup_natAdd_five : tup n F h (natAdd n 5) = -(X F h + Y F) ^ 5 := by simp [tup]

/--
@isnad1 id=eq.0h3v.s6.006e544af6d1 from=translated src=- shape=2f68dbfc vocab=ad1c4bf7
-/
lemma sum_tup : ∑ i, tup n F h i = 0 := by
  simp only [tup, sum_univ_add, addCases_left, addCases_right, sum_univ_six, add_assoc]
  set x := X F h
  set y := Y F
  rw [show (x ^ 2 + 10 * y ^ 3) ^ 2 + ((10 * y - 1 : ℤ) * x ^ 4 + ((x - y) ^ 5 + -(x + y) ^ 5)) =
    (100 * y - 2) * y ^ 5 by ring, ← add_assoc _ _ (_ * _), (VW n F).eq_add, cast_add, neg_add,
    add_add_neg_cancel'_right, sum_univ_eq_sum_range fun i ↦ (primeChain _ i : ℤ), ← cast_sum]
  grind [U]

section Factors

variable {f : ℕ} (mf : f ∈ F)

/--
@isnad1 id=dvd.1h2v.s5.2d2f9c95276f from=translated src=- shape=4305f424 vocab=6b401a90
-/
lemma dvd_Y_of_mem_F (mf : f ∈ F.erase 0) : f ∣ Y F := (dvd_prod_of_mem _ mf).mul_left _

include mf

/--
@isnad1 id=modeq.2h3v.s5.891ea4214d82 from=translated src=- shape=a021c624 vocab=fe52144a
-/
lemma X_modEq_one_of_mem_F (lf : 3 ≤ f) : X F h ≡ 1 [MOD f] := by
  unfold X
  nth_rw 2 [← one_pow (h !)]
  apply ModEq.pow
  rw [add_modEq_right_iff]
  exact dvd_Y_of_mem_F (by grind)

end Factors

end GeneralCase
