/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 2008, Problem 1

Prove that for each positive integer n, there are pairwise relatively prime
integers k₀,k₁,...,kₙ, all strictly greater than 1, such that k₀k₁...kₙ - 1
is a product of two consecutive integers.
-/

namespace Usa2008P1

-- This follows the ad-hoc second solution in
-- https://web.evanchen.cc/exams/USAMO-2008-notes.pdf

-- Define the two main sequences
def kseq (n : ℕ) : ℕ :=
  if n = 0 then 7 else 2 ^ (2 ^ n) - 2 ^ (2 ^ (n - 1)) + 1
def xseq (n : ℕ) : ℕ := 2 ^ (2 ^ n)

/--
@isnad1 id=lt.0h1v.s3.06d8f4d7b27b from=translated src=- shape=8a62b088 vocab=a2c746f3
-/
lemma k_greater_than_one (n : ℕ) : 1 < kseq n := by
  unfold kseq
  split_ifs -- split on n = 0 and n > 0
  · norm_num
  · have : 2^(2^(n-1)) < 2^(2^n) := by gcongr <;> lia
    lia

-- Main identity k₀k₁...kₙ - 1 = xₙ (xₙ + 1)
/--
@isnad1 id=eq.0h1v.s7.fbde6731c662 from=translated src=- shape=035ac87e vocab=6278b6cd
-/
lemma quartic_polynomial_identity (t : ℕ) :
    (t^2 + t + 1) * (t^2 - t + 1) = t^4 + t^2 + 1 := by
  zify [show t ≤ t^2 by nlinarith]
  ring

/--
@isnad1 id=eq.0h1v.s6.b6ecb49d0019 from=translated src=- shape=f1370e09 vocab=975ab669
-/
lemma main_identity (n : ℕ) :
  (∏ i : Fin (n+1), (kseq ↑i)) = (xseq n) ^ 2 + (xseq n) + 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      simp only [kseq, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        add_tsub_cancel_right]
      rw [show 2 ^ 2 ^ (n + 1) = (xseq n)^2 by unfold xseq; ring]
      rw [show xseq (n + 1) = (xseq n)^2 by unfold xseq; ring]
      rw [show 2 ^ 2 ^ n = xseq n from rfl]
      rw [quartic_polynomial_identity (xseq n)]
      ring

-- kₙ₊₁ = xₙ² - xₙ + 1
/--
@isnad1 id=eq.0h1v.s5.a884dfe77428 from=translated src=- shape=ada45dce vocab=967b3f43
-/
lemma kseq_succ_eq (n : ℕ) : kseq (n + 1) = xseq n ^ 2 - xseq n + 1 := by
  unfold kseq xseq
  simp only [Nat.add_sub_cancel, ite_eq_right (Nat.succ_ne_zero n)]
  ring_nf

-- gcd(x² + x + 1, x² - x + 1) = 1
/--
@isnad1 id=eq.0h1v.s6.605be76ad6ee from=translated src=- shape=c372afb4 vocab=1be32ebc
-/
lemma gcd_quad_identity (x : ℤ) :
    Int.gcd (x^2 + x + 1) (x^2 - x + 1) = 1 := by
  -- Apply Euclidean algorithm one step
  rw [show x^2 + x + 1 = 2 * x + (x^2 - x + 1) by ring, Int.gcd_add_self_left, Int.gcd_comm]
  -- Now we need to show x^2-x+1 is coprime to 2x, so we split into two
  have h1 : Int.gcd (x^2 - x + 1) x = 1 := by simp
  have h2 : Int.gcd (x^2 - x + 1) 2 = 1 := by
    have h_odd: (x^2 - x + 1) % 2 = 1 := by
      rcases Int.even_or_odd x with ⟨k, hk⟩ | ⟨k, hk⟩ <;>
      · subst hk; ring_nf; lia
    rw [← Int.gcd_emod, h_odd]
    decide
  rw [Int.gcd_mul_right_right_of_gcd_eq_one h2]
  exact h1

-- we also need an ℕ version of the previous identity
/--
@isnad1 id=eq.0h1v.s6.a68cf4ebadab from=translated src=- shape=f856a722 vocab=8da52961
-/
lemma gcd_quad_identity_nat (x : ℕ) :
    Nat.gcd (x^2 + x + 1) (x^2 - x + 1) = 1 := by
  convert gcd_quad_identity (x : ℤ)
  · have : x ≤ x^2 := by nlinarith
    norm_cast

-- kₙ₊₁ is coprime to the product k₀...kₙ
/--
@isnad1 id=coprime.0h1v.s6.fb474cf16334 from=translated src=- shape=bb1d9a78 vocab=a44dab1a
-/
lemma k_coprime_with_product (n : ℕ) :
    Nat.Coprime (∏ i : Fin (n + 1), kseq ↑i) (kseq (n + 1)) := by
  rw [main_identity, kseq_succ_eq, Nat.coprime_iff_gcd_eq_one]
  apply gcd_quad_identity_nat (xseq n)

-- Show the main coprime lemma
-- Strategy: kⱼ is coprime to product P := k₀...kⱼ₋₁, and kseq i divides that product
/--
@isnad1 id=coprime.1h2v.s3.e4152d701539 from=translated src=- shape=1f63dda6 vocab=1e668b2f
-/
lemma k_are_coprime (i j : ℕ) (hij: i < j) : Nat.Coprime (kseq i) (kseq j) := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by lia⟩
  let P := ∏ k : Fin (n + 1), kseq ↑k  -- the product k₀ ... kₙ
  have hdvd : kseq i ∣ P := by
    apply Finset.dvd_prod_of_mem (fun j : Fin (n+1) => kseq ↑j) (Finset.mem_univ ⟨i, by lia⟩)
  have hcop : Nat.Coprime P (kseq (n + 1)) := k_coprime_with_product n
  exact Nat.Coprime.coprime_dvd_left hdvd hcop

end Usa2008P1
