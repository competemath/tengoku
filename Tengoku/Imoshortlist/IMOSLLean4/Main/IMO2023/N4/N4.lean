/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku

/-!
# IMO 2023 N4

Let $a_0, a_1, …, a_{n - 1}, b_0, b_1, …, b_{n - 1} ∈ ℕ^+$ and
  $D$ be a positive integer such that for each $i ≤ n$,
$$ b_0 b_1 … b_i a_{i + 1} … a_{n - 1} = b_0 b_1 … b_{i - 1} a_i … a_{n - 1} + D. $$
Determine the smallest possible value of $D$.
-/

@[expose] public section

namespace IMOSL
namespace IMO2023N4

open Finset

/-! ### Extra lemmas -/

/--
@isnad1 id=eq.0h1v.s5.5bf7739e4156 from=translated src=- shape=e8e5f273 vocab=d804f259
-/
theorem prod_range_add_two (n : ℕ) : ∏ x ∈ range n, (x + 2) = (n + 1).factorial := by
  rw [← prod_range_add_one_eq_factorial, prod_range_succ', Nat.mul_one]

/--
@isnad1 id=eq.1h2v.s6.1ad09108dd9b from=translated src=- shape=0b561368 vocab=3e9482a8
-/
theorem prod_range_add_two_mul_Ico_succ (h : i ≤ n) :
    (range i).prod (· + 2) * (Ico i n).prod Nat.succ = (i + 1) * n.factorial := by
  rw [← prod_range_add_one_eq_factorial, prod_range_add_two, Nat.factorial_succ,
    Nat.mul_assoc,  ← prod_range_add_one_eq_factorial, prod_range_mul_prod_Ico _ h]

/-! ### Start of the problem -/

structure goodSeq (n : ℕ) where
  a : ℕ → ℕ
  a_pos : ∀ i, 0 < a i
  b : ℕ → ℕ
  b_pos : ∀ i, 0 < b i
  D : ℕ
  D_pos : 0 < D
  spec : ∀ i < n, (range (i + 1)).prod b * (Ico (i + 1) n).prod a
    = (range i).prod b * (Ico i n).prod a + D

def linear_goodSeq (n : ℕ) : goodSeq n where
  a := Nat.succ
  a_pos := Nat.succ_pos
  b := (· + 2)
  b_pos := (Nat.add_pos_right · Nat.two_pos)
  D := n.factorial
  D_pos := n.factorial_pos
  spec := λ i hi ↦ by rw [prod_range_add_two_mul_Ico_succ hi.le,
      prod_range_add_two_mul_Ico_succ hi, Nat.succ_mul]

namespace goodSeq

variable (X : goodSeq n)

/--
@isnad1 id=lt.1h3v.s4.6ae7c20c727f from=translated src=- shape=7d7a913b vocab=74001d08
-/
lemma a_lt_b (h : i < n) : X.a i < X.b i := by
  have h0 := (Nat.lt_add_of_pos_right X.D_pos).trans_eq (X.spec i h).symm
  rw [prod_range_succ, prod_eq_prod_Ico_succ_bot h, Nat.mul_assoc] at h0
  exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_mul_lt_mul_left h0)

/--
@isnad1 id=lt.1h3v.s5.e0602b649ce0 from=translated src=- shape=c5836091 vocab=1991d0e9
-/
lemma b_sub_a_pos (h : i < n) : 0 < X.b i - X.a i :=
  Nat.sub_pos_of_lt (X.a_lt_b h)

/--
@isnad1 id=eq.1h3v.s6.cbbbf766a2b2 from=translated src=- shape=c97f6856 vocab=aacd8630
-/
lemma spec_alt (h : i < n) :
    (range i).prod X.b * (Ico (i + 1) n).prod X.a * (X.b i - X.a i) = X.D := by
  rw [Nat.mul_sub]; apply Nat.sub_eq_of_eq_add'
  rw [Nat.mul_right_comm, ← prod_range_succ, X.spec _ h,
    prod_eq_prod_Ico_succ_bot h, Nat.mul_assoc, (X.a i).mul_comm]

/--
@isnad1 id=lt.0h3v.s4.dd8c7ede34e3 from=translated src=- shape=4cac01b5 vocab=3502adfd
-/
lemma prod_a_pos (S : Finset ℕ) : 0 < S.prod X.a :=
  prod_pos λ _ _ ↦ X.a_pos _

/--
@isnad1 id=lt.0h3v.s4.75e9712ab88a from=translated src=- shape=4cac01b5 vocab=51e3721d
-/
lemma prod_b_pos (S : Finset ℕ) : 0 < S.prod X.b :=
  prod_pos λ _ _ ↦ X.b_pos _

/--
@isnad1 id=eq.1h3v.s6.2925592657ff from=translated src=- shape=529d60ca vocab=a26b7690
-/
lemma mul_sub_eq_mul_sub (h : i + 1 < n) :
    X.a (i + 1) * (X.b i - X.a i) = X.b i * (X.b (i + 1) - X.a (i + 1)) := by
  have h0 := (X.spec_alt (Nat.lt_of_succ_lt h)).trans (X.spec_alt h).symm
  rw [prod_range_succ,  prod_eq_prod_Ico_succ_bot h, ← Nat.mul_assoc,
    Nat.mul_right_comm _ (X.a _), Nat.mul_right_comm _ (X.b _),
    Nat.mul_assoc, Nat.mul_assoc _ (X.b _)] at h0
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (X.prod_b_pos _) (X.prod_a_pos _)) h0

/--
@isnad1 id=lt.1h3v.s5.3670afa8b8d8 from=translated src=- shape=17e7018c vocab=e545eb0b
-/
lemma mul_b_sub_a_lt_a (h : i < n) : i * (X.b i - X.a i) < X.a i := by
  induction i with
  | zero => exact (Nat.zero_mul _).trans_lt (X.a_pos 0)
  | succ i i_ih => ?_
  have h0 := Nat.lt_of_succ_lt h
  specialize i_ih h0
  apply Nat.lt_of_mul_lt_mul_left (a := X.b i - X.a i)
  calc
    _ = (i * (X.b i - X.a i) + (X.b i - X.a i)) * (X.b (i + 1) - X.a (i + 1)) := by
      rw [Nat.mul_left_comm, ← Nat.mul_assoc, Nat.succ_mul]
    _ < (X.a i + (X.b i - X.a i)) * (X.b (i + 1) - X.a (i + 1)) :=
      Nat.mul_lt_mul_of_pos_right (Nat.add_lt_add_right i_ih _) (X.b_sub_a_pos h)
    _ = X.b i * (X.b (i + 1) - X.a (i + 1)) := by rw [Nat.add_sub_cancel' (X.a_lt_b h0).le]
    _ = _ := by rw [← X.mul_sub_eq_mul_sub h, Nat.mul_comm]

/--
@isnad1 id=lt.1h3v.s4.5907213d32e4 from=translated src=- shape=342c155b vocab=048a7c02
-/
lemma self_lt_a (h : i < n) : i < X.a i :=
  (Nat.le_mul_of_pos_right i (X.b_sub_a_pos h)).trans_lt (X.mul_b_sub_a_lt_a h)

/--
@isnad1 id=le.1h3v.s4.88b73cf020c8 from=translated src=- shape=b43e2e82 vocab=c18e39d9
-/
lemma succ_le_a (h : i < n) : i.succ ≤ X.a i :=
  X.self_lt_a h

end goodSeq
