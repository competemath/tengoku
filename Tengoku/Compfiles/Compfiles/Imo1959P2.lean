/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1959, Problem 2

For what real values of x is

 √(x+√(2x-1)) + √(x-√(2x-1)) = A,

given:
  (a) A = √2
  (b) A = 1
  (c) A = 2,
where only non-negative real numbers are admitted for square roots?
-/

open Set Real

namespace Imo1959P2

def IsGood (x A : ℝ) : Prop :=
  sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) = A ∧ 0 ≤ 2 * x - 1 ∧
    0 ≤ x + sqrt (2 * x - 1) ∧ 0 ≤ x - sqrt (2 * x - 1)

variable {x A : ℝ}

/-
We follow second solution from the
[Art of Problem Solving](https://artofproblemsolving.com/wiki/index.php/1959_IMO_Problems/Problem_2)
website.
Namely, we rewrite the equation as $\sqrt{2x-1}+1+|\sqrt{2x-1}-1|=A\sqrt{2}$,
then consider the cases $\sqrt{2x-1}\le 1$ and $1 < \sqrt{2x-1}$ separately.
-/

/--
@isnad1 id=iff.0h2v.s7.d0bd6f8ccd58 from=translated src=- shape=dcba2e58 vocab=e7da3664
-/
theorem isGood_iff : IsGood x A ↔
    sqrt (2 * x - 1) + 1 + |sqrt (2 * x - 1) - 1| = A * sqrt 2 ∧ 1 / 2 ≤ x := by
  cases le_or_gt (1 / 2) x with
  | inl hx =>
    have hx' : 0 ≤ 2 * x - 1 := by linarith
    have h₁ : x + sqrt (2 * x - 1) = (sqrt (2 * x - 1) + 1) ^ 2 / 2 := by
      rw [add_sq, sq_sqrt hx']; field_simp; ring
    have h₂ : x - sqrt (2 * x - 1) = (sqrt (2 * x - 1) - 1) ^ 2 / 2 := by
      rw [sub_sq, sq_sqrt hx']; field_simp; ring
    simp only [IsGood, *, div_nonneg (sq_nonneg _) (zero_le_two (α := ℝ)), sqrt_div (sq_nonneg _),
      and_true]
    rw [sqrt_sq, sqrt_sq_eq_abs] <;> [skip; positivity]
    field_simp
  | inr hx =>
    have : 2 * x - 1 < 0 := by linarith
    simp only [IsGood, this.not_ge, hx.not_ge]; simp

/--
@isnad1 id=le.1h2v.s5.278f1a341fc3 from=translated src=- shape=e79d142a vocab=7d18e212
-/
theorem IsGood.one_half_le (h : IsGood x A) : 1 / 2 ≤ x := (isGood_iff.1 h).2

/--
@isnad1 id=iff.0h1v.s5.5eed8c5cb1a6 from=translated src=- shape=53ed7fa1 vocab=840cf164
-/
theorem sqrt_two_mul_sub_one_le_one : sqrt (2 * x - 1) ≤ 1 ↔ x ≤ 1 := by
  simp [sqrt_le_iff, ← two_mul]

/--
@isnad1 id=iff.1h2v.s5.36f8c40652fd from=translated src=- shape=6248ac2a vocab=170e0458
-/
theorem isGood_iff_eq_sqrt_two (hx : x ∈ Icc (1 / 2) 1) : IsGood x A ↔ A = sqrt 2 := by
  have : sqrt (2 * x - 1) ≤ 1 := sqrt_two_mul_sub_one_le_one.2 hx.2
  simp only [isGood_iff, hx.1, abs_sub_comm _ (1 : ℝ), abs_of_nonneg (sub_nonneg.2 this), and_true]
  suffices 2 = A * sqrt 2 ↔ A = sqrt 2 by convert this using 2; ring
  rw [← div_eq_iff, div_sqrt, eq_comm]
  positivity

/--
@isnad1 id=iff.1h2v.s5.d32f71ac6773 from=translated src=- shape=000ecb96 vocab=928d8963
-/
theorem isGood_iff_eq_sqrt (hx : 1 < x) : IsGood x A ↔ A = sqrt (4 * x - 2) := by
  have h₁ : 1 < sqrt (2 * x - 1) := by simpa only [← not_le, sqrt_two_mul_sub_one_le_one] using hx
  have h₂ : 1 / 2 ≤ x := by linarith
  simp only [isGood_iff, h₂, abs_of_pos (sub_pos.2 h₁), add_add_sub_cancel, and_true]
  rw [← mul_two, ← div_eq_iff (by positivity), mul_div_assoc, div_sqrt, ← sqrt_mul' _ zero_le_two,
    eq_comm]
  ring_nf

/--
@isnad1 id=lt.2h2v.s5.e93829214b15 from=translated src=- shape=1ea7e90b vocab=88634b22
-/
theorem IsGood.sqrt_two_lt_of_one_lt (h : IsGood x A) (hx : 1 < x) : sqrt 2 < A := by
  rw [(isGood_iff_eq_sqrt hx).1 h]
  refine sqrt_lt_sqrt zero_le_two ?_
  linarith

theorem IsGood.eq_sqrt_two_iff_le_one (h : IsGood x A) : A = sqrt 2 ↔ x ≤ 1 :=
  ⟨fun hA ↦ not_lt.1 fun hx ↦ (h.sqrt_two_lt_of_one_lt hx).ne' hA, fun hx ↦
    (isGood_iff_eq_sqrt_two ⟨h.one_half_le, hx⟩).1 h⟩

/--
@isnad1 id=iff.1h2v.s5.20f129ebf5db from=translated src=- shape=7bade32d vocab=88634b22
-/
theorem IsGood.sqrt_two_lt_iff_one_lt (h : IsGood x A) : sqrt 2 < A ↔ 1 < x :=
  ⟨fun hA ↦ not_le.1 fun hx ↦ hA.ne' <| h.eq_sqrt_two_iff_le_one.2 hx, h.sqrt_two_lt_of_one_lt⟩

/--
@isnad1 id=le.1h2v.s4.1017863725e0 from=translated src=- shape=e1192eca vocab=db4d4ff0
-/
theorem IsGood.sqrt_two_le (h : IsGood x A) : sqrt 2 ≤ A :=
  (le_or_gt x 1).elim (fun hx ↦ (h.eq_sqrt_two_iff_le_one.2 hx).ge) fun hx ↦
    (h.sqrt_two_lt_of_one_lt hx).le

/--
@isnad1 id=iff.1h2v.s6.a2f2a4abc89f from=translated src=- shape=540ff19f vocab=db454dbe
-/
theorem isGood_iff_of_sqrt_two_lt (hA : sqrt 2 < A) : IsGood x A ↔ x = (A / 2) ^ 2 + 1 / 2 := by
  have : 0 < A := lt_trans (by simp) hA
  constructor
  · intro h
    have hx : 1 < x := by rwa [h.sqrt_two_lt_iff_one_lt] at hA
    rw [isGood_iff_eq_sqrt hx, eq_comm, sqrt_eq_iff_eq_sq] at h <;> linarith
  · rintro rfl
    rw [isGood_iff_eq_sqrt]
    · conv_lhs => rw [← sqrt_sq this.le]
      ring_nf
    · rw [sqrt_lt' this] at hA
      linarith

abbrev solution_set_sqrt2 : Set ℝ := Icc (1 / 2) 1

abbrev solution_set_one : Set ℝ := ∅

abbrev solution_set_two : Set ℝ := { 3 / 2 }

end Imo1959P2
