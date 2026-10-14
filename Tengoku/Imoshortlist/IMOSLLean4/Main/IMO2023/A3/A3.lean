/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku

/-!
# IMO 2023 A3 (P4)

Let $F$ be a totally ordered field and $N$ be a positive integer.
Let $x_1, x_2, …, x_N ∈ F$ be distinct positive elements
  such that for each $n$, there exists $a_n ∈ ℕ$ with
$$ a_n^2 = \left(\sum_{i = 1}^n x_i\right) \left(\sum_{i = 1}^n \frac{1}{x_i}\right). $$
Prove that $a_N ≥ ⌊3N/2⌋$.
-/

@[expose] public section

namespace IMOSL
namespace IMO2023A3

open Finset

structure goodSeq (N : ℕ) (F) [Field F] [LinearOrder F] where
  x : ℕ → F
  a : ℕ → ℕ
  x_pos' : ∀ i < N, 0 < x i
  x_inj' : ∀ i < N, ∀ j < N, x i = x j → i = j
  spec' : ∀ i ≤ N, (a i : F) ^ 2 = (range i).sum x * (range i).sum λ i ↦ (x i)⁻¹

namespace goodSeq

variable {N : ℕ} {F} [Field F] [LinearOrder F] (X : goodSeq N F)

/--
@isnad1 id=lt.1h4v.s5.d9d6fcb79d86 from=translated src=- shape=0979cf81 vocab=5debe989
-/
lemma x_pos (hi : i < N) : 0 < X.x i :=
  X.x_pos' i hi

/--
@isnad1 id=eq.3h5v.s5.bb61e7c65261 from=translated src=- shape=b2d3b7ff vocab=5debe989
-/
lemma x_inj (hi : i < N) (hj : j < N) (h : X.x i = X.x j) : i = j :=
  X.x_inj' i hi j hj h

/--
@isnad1 id=iff.2h5v.s5.f7741254be60 from=translated src=- shape=7cf8db57 vocab=5debe989
-/
lemma x_inj_iff (hi : i < N) (hj : j < N) : X.x i = X.x j ↔ i = j :=
  ⟨X.x_inj hi hj, λ h ↦ h ▸ rfl⟩

/--
@isnad1 id=eq.1h4v.s7.8c651c52bc54 from=translated src=- shape=4c04df0c vocab=718dfa2b
-/
lemma spec (hi : i ≤ N) :
    (X.a i : F) ^ 2 = (range i).sum X.x * (range i).sum λ i ↦ (X.x i)⁻¹ :=
  X.spec' i hi

/--
@isnad1 id=ne.1h4v.s5.742a6690fc00 from=translated src=- shape=ddb01211 vocab=5debe989
-/
lemma x_ne_zero (hi : i < N) : X.x i ≠ 0 :=
  (X.x_pos hi).ne.symm

/--
@isnad1 id=le.1h4v.s5.6db133d91b9f from=translated src=- shape=05e02a1f vocab=1d0aa19b
-/
lemma x_nonneg (hi : i < N) : 0 ≤ X.x i :=
  (X.x_pos hi).le

/--
@isnad1 id=ne.1h4v.s6.79d1a53e61f8 from=translated src=- shape=90068fe0 vocab=8920f6f9
-/
lemma x_inv_ne_zero (hi : i < N) : (X.x i)⁻¹ ≠ 0 :=
  inv_ne_zero (X.x_ne_zero hi)

/--
@isnad1 id=eq.1h4v.s6.418d0e626607 from=translated src=- shape=853d718d vocab=da31cc7f
-/
lemma x_mul_inv (h : i < N) : X.x i * (X.x i)⁻¹ = 1 :=
  mul_inv_cancel₀ (X.x_ne_zero h)

variable [IsStrictOrderedRing F]

/--
@isnad1 id=lt.1h4v.s6.a188311676eb from=translated src=- shape=d11f1cd3 vocab=7c07d460
-/
lemma x_inv_pos (hi : i < N) : 0 < (X.x i)⁻¹ :=
  inv_pos.mpr (X.x_pos hi)

/--
@isnad1 id=le.1h4v.s6.ef82d5247e55 from=translated src=- shape=e91280b4 vocab=180b1c06
-/
lemma x_inv_nonneg (hi : i < N) : 0 ≤ (X.x i)⁻¹ :=
  (X.x_inv_pos hi).le

/--
@isnad1 id=eq.0h3v.s5.021f028b5daf from=translated src=- shape=6ed6215a vocab=11a0f5de
-/
lemma a_zero_eq_zero : X.a 0 = 0 := by
  have h := X.spec N.zero_le
  rwa [sum_range_zero, zero_mul, sq_eq_zero_iff, Nat.cast_eq_zero] at h

/--
@isnad1 id=eq.1h3v.s5.4b8cc34445ca from=translated src=- shape=c9efba92 vocab=d4008da4
-/
lemma a_one_eq_one (h : 0 < N) : X.a 1 = 1 := by
  have h0 := X.spec h
  rwa [sum_range_one, sum_range_one, X.x_mul_inv h, ← Nat.cast_pow,
    Nat.cast_eq_one, sq, Nat.mul_self_inj (n := 1)] at h0

omit [IsStrictOrderedRing F] in
/--
@isnad1 id=eq.1h4v.s8.3a30d80416e7 from=translated src=- shape=03c45aeb vocab=78a8462b
-/
lemma special_formula1 (h : i + 1 ≤ N) :
    (X.a (i + 1) : F) ^ 2 - (X.a i + 1) ^ 2
      = (X.x i)⁻¹ * (range i).sum X.x
        + X.x i * (range i).sum (λ j ↦ (X.x j)⁻¹) - 2 * X.a i := calc
  _ = (range (i + 1)).sum X.x * (range (i + 1)).sum (λ j ↦ (X.x j)⁻¹)
      - ((range i).sum X.x * (range i).sum (λ j ↦ (X.x j)⁻¹) + 1 + 2 * X.a i) := by
    rw [X.spec h, sum_range_succ, sum_range_succ, add_sq',
      X.spec (Nat.le_of_succ_le h), one_pow, mul_one]
  _ = (range i).sum X.x * (range i).sum (λ j ↦ (X.x j)⁻¹)
      + (range i).sum X.x * (X.x i)⁻¹ + (X.x i * (range i).sum (λ j ↦ (X.x j)⁻¹) + 1)
      - ((range i).sum X.x * (range i).sum (λ j ↦ (X.x j)⁻¹) + 1 + 2 * X.a i) := by
    rw [sub_left_inj, sum_range_succ, sum_range_succ,
      add_mul, mul_add, mul_add, X.x_mul_inv h]
  _ = _ := by rw [add_comm _ 1, add_add_add_comm, add_sub_add_left_eq_sub, mul_comm]

omit [IsStrictOrderedRing F] in
/--
@isnad1 id=eq.1h4v.s8.f329053f3e99 from=translated src=- shape=5a16f348 vocab=7daf37f1
-/
lemma special_formula2 (h : i < N) :
    ((X.x i)⁻¹ * (range i).sum X.x + X.x i * (range i).sum (λ j ↦ (X.x j)⁻¹)) ^ 2
      = ((X.x i)⁻¹ * (range i).sum X.x - X.x i * (range i).sum (λ j ↦ (X.x j)⁻¹)) ^ 2
        + (2 * X.a i) ^ 2 := by
  rw [← sub_eq_iff_eq_add', sq_sub_sq, add_add_sub_cancel, add_sub_sub_cancel,
    ← two_mul, ← two_mul, mul_mul_mul_comm, ← sq, mul_pow, X.spec (Nat.le_of_succ_le h),
    mul_mul_mul_comm, mul_comm _ (X.x i), X.x_mul_inv h, one_mul]

/--
@isnad1 id=le.1h4v.s6.e9a1eb260a1e from=translated src=- shape=3c3c5471 vocab=82c4beaf
-/
lemma a_add_one_le_a_succ (h : i + 1 ≤ N) : X.a i + 1 ≤ X.a (i + 1) := by
  rw [← Nat.mul_self_le_mul_self_iff, ← sq, ← sq, ← Nat.cast_le (α := F), Nat.cast_pow,
    Nat.cast_pow, Nat.cast_succ, ← sub_nonneg, X.special_formula1 h, sub_nonneg]
  refine le_of_pow_le_pow_left₀ (Nat.succ_ne_zero 1) ?_
    ((le_add_of_nonneg_left (sq_nonneg _)).trans_eq (X.special_formula2 h).symm)
  refine add_nonneg (mul_nonneg (inv_nonneg.mpr (X.x_nonneg h)) (sum_nonneg λ j h1 ↦ ?_))
    (mul_nonneg (X.x_nonneg h) (sum_nonneg λ j h1 ↦ inv_nonneg.mpr ?_))
  all_goals exact X.x_nonneg ((mem_range.mp h1).trans h)

/--
@isnad1 id=iff.1h4v.s7.6163fbcfc295 from=translated src=- shape=5f5a2bd6 vocab=66aaf731
-/
lemma a_succ_eq_a_add_one_iff (h : i + 1 ≤ N) :
    X.a (i + 1) = X.a i + 1 ↔
      (range i).sum X.x = X.x i ^ 2 * (range i).sum λ j ↦ (X.x j)⁻¹ := calc
  _ ↔ (X.a (i + 1) : F) ^ 2 - (X.a i + 1) ^ 2 = 0 := by
    rw [← Nat.cast_succ, ← Nat.cast_pow, ← Nat.cast_pow,
      sub_eq_zero, Nat.cast_inj, sq, sq, Nat.mul_self_inj]
  _ ↔ (X.x i)⁻¹ * (range i).sum X.x + X.x i * (range i).sum (λ j ↦ (X.x j)⁻¹)
      = 2 * X.a i := by rw [X.special_formula1 h, sub_eq_zero]
  _ ↔ ((X.x i)⁻¹ * (range i).sum X.x + X.x i * (range i).sum (λ j ↦ (X.x j)⁻¹)) ^ 2
      = (2 * X.a i) ^ 2 := by
    refine (sq_eq_sq₀ ?_ (mul_nonneg zero_le_two (X.a i).cast_nonneg)).symm
    have h0 : 0 ≤ X.x i := X.x_nonneg h
    refine add_nonneg (mul_nonneg (inv_nonneg.mpr h0) (sum_nonneg λ j h1 ↦ ?_))
      (mul_nonneg h0 (sum_nonneg λ j h1 ↦ inv_nonneg.mpr ?_))
    all_goals exact X.x_nonneg ((mem_range.mp h1).trans h)
  _ ↔ (X.x i)⁻¹ * (range i).sum X.x = X.x i * (range i).sum (λ j ↦ (X.x j)⁻¹) := by
    rw [X.special_formula2 h, add_eq_right, sq_eq_zero_iff, sub_eq_zero]
  _ ↔ _ := by rw [inv_mul_eq_iff_eq_mul₀ (X.x_ne_zero h), sq, mul_assoc]

/--
@isnad1 id=le.1h4v.s6.0178c9c1519c from=translated src=- shape=3c3c5471 vocab=82c4beaf
-/
lemma three_add_a_le_a_add_two (h : i + 2 ≤ N) : X.a i + 3 ≤ X.a (i + 2) := by
  have h' : i + 1 ≤ N := Nat.le_of_succ_le h
  ---- We are done if `a_{i + 2} ≥ a_{i + 1} + 2` or `a_{i + 1} ≥ a_i + 1`
  obtain h0 | h0 : X.a i + 2 ≤ X.a (i + 1) ∨ X.a i + 1 = X.a (i + 1) :=
    (Nat.eq_or_lt_of_le (X.a_add_one_le_a_succ h')).symm
  · exact (Nat.succ_le_succ h0).trans (X.a_add_one_le_a_succ h)
  obtain h1 | h1 : X.a (i + 1) + 2 ≤ X.a (i + 2) ∨ X.a (i + 1) + 1 = X.a (i + 2) :=
    (Nat.eq_or_lt_of_le (X.a_add_one_le_a_succ h)).symm
  · rwa [← h0] at h1
  ---- Now assume that `a_{i + 2} = a_{i + 1} + 1 = a_i + 2` and get contradiction
  rw [eq_comm, X.a_succ_eq_a_add_one_iff (by assumption)] at h0 h1
  rw [sum_range_succ, h0, sum_range_succ, sq, mul_assoc, ← mul_add_one,
    ← X.x_mul_inv h', ← mul_add, ← mul_assoc, ← sq, mul_eq_mul_right_iff] at h1
  replace h1 : X.x i ^ 2 = X.x (i + 1) ^ 2 := by
    refine h1.resolve_right (add_pos_of_nonneg_of_pos ?_ (X.x_inv_pos h')).ne.symm
    exact sum_nonneg λ j hj ↦ X.x_inv_nonneg ((mem_range.mp hj).trans h')
  rw [sq_eq_sq₀ (X.x_nonneg h') (X.x_nonneg h), X.x_inj_iff h' h] at h1
  exact absurd i.lt_succ_self h1.not_lt

/--
@isnad1 id=le.1h4v.s6.e268cb77b721 from=translated src=- shape=b5517f7e vocab=ae8f032c
-/
theorem general_a_bound : ∀ {i}, i ≤ N → 3 * i / 2 ≤ X.a i
  | 0 => λ _ ↦ Nat.zero_le _
  | 1 => λ h ↦ (X.a_one_eq_one h).ge
  | n + 2 => λ h ↦ calc 3 * (n + 2) / 2
      _ = 3 * n / 2 + 3 := by rw [Nat.mul_add, Nat.add_mul_div_right _ _ Nat.two_pos]
      _ ≤ X.a n + 3 := Nat.add_le_add_right (general_a_bound (Nat.le_of_add_right_le h)) _
      _ ≤ X.a (n + 2) := X.three_add_a_le_a_add_two h

end goodSeq

/-- Final solution
@isnad1 id=le.0h3v.s6.24f0e08042ea from=translated src=- shape=513f44de vocab=ae8f032c
-/
theorem final_solution [Field F] [LinearOrder F] [IsStrictOrderedRing F] (X : goodSeq N F) : 3 * N / 2 ≤ X.a N :=
  X.general_a_bound N.le_refl
