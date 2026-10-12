/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 1992, Problem 1

Find, as a function of n, the sum of the digits of

     9 × 99 × 9999 × ... × (10^2ⁿ - 1),

where each factor has twice as many digits as the last one.
-/

namespace Usa1992P1

-- TODO add a generalization of this mathlib?
/--
@isnad1 id=eq.0h1v.s5.bcbca4dac34c from=translated src=- shape=7aca2c25 vocab=04d9949a
-/
lemma digits_pow (m : ℕ) : (Nat.digits 10 (10^m)).length = m + 1 := by
  induction' m with m ih
  · simp
  rw [pow_succ, Nat.digits_def' (by norm_num) (by positivity)]
  rw [mul_div_cancel_right₀ _ (by norm_num), List.length_cons]
  rw [ih]

/--
@isnad1 id=lt.1h2v.s5.3965ee0b3282 from=translated src=- shape=ffe3e797 vocab=cdae25f0
-/
lemma lemma2 {m y: ℕ} (hy : y < 10^m) : (Nat.digits 10 y).length < m + 1 := by
  induction m generalizing y with
  | zero => simp [show y = 0 by lia]
  | succ m ih =>
    obtain rfl | hyp := Nat.eq_zero_or_pos y
    · simp
    rw [Nat.digits_def' (by norm_num) hyp]
    rw [List.length_cons, add_lt_add_iff_right]
    have h2 : y / 10 < 10 ^ m := by lia
    exact ih h2

/--
@isnad1 id=eq.0h2v.s5.6cf22693f808 from=translated src=- shape=24e43e55 vocab=2bcf63f3
-/
lemma digits_sum_mul_pow {m x : ℕ} :
    (Nat.digits 10 (x * 10 ^ m)).sum = (Nat.digits 10 x).sum := by
  cases x with
  | zero => simp
  | succ x =>
    rw [mul_comm, Nat.digits_base_pow_mul (by lia) (by lia)]
    simp

/--
@isnad1 id=eq.1h3v.s7.2966ca4b0ee9 from=translated src=- shape=e1062539 vocab=8c248bee
-/
lemma digits_sum (m x y : ℕ)
    (h1 : y < 10^m) :
    (Nat.digits 10 (x * 10^m + y)).sum =
    (Nat.digits 10 (x * 10^m)).sum + (Nat.digits 10 y).sum := by
  cases x with | zero => simp | succ x =>
  -- choose k such that (digits 10 y).length + k = m
  have h3 : (Nat.digits 10 y).length ≤ m := by
    have h4 := lemma2 h1
    exact Nat.le_of_lt_succ h4
  have ⟨k, hk⟩ : ∃ k, (Nat.digits 10 y).length + k = m := Nat.le.dest h3
  nth_rewrite 1 [add_comm, mul_comm]
  nth_rewrite 1 [← hk]
  have one_lt_ten : 1 < 10 := by norm_num
  rw [← Nat.digits_append_zeroes_append_digits one_lt_ten (Nat.zero_lt_succ x)]
  simp only [List.sum_append, List.sum_replicate, smul_eq_mul, mul_zero, add_zero]
  rw [digits_sum_mul_pow]
  ring

/--
@isnad1 id=odd.1h3v.s5.3444d0cc0a51 from=translated src=- shape=3998135e vocab=9931e543
-/
lemma Finset.prod_odd {α : Type} [DecidableEq α] {f : α → ℕ} {s : Finset α}
    (hs : ∀ i ∈ s, Odd (f i)) : Odd (∏ i ∈ s, f i) := by
  revert hs
  induction s using Finset.induction
  case empty => simp
  case insert a s' ha ih =>
    intro hs'
    rw [Finset.prod_insert ha, Nat.odd_mul]
    simp only [Finset.mem_insert, forall_eq_or_imp] at hs'
    specialize ih hs'.2
    exact ⟨hs'.1, ih⟩

example (m : ℕ) (h : ¬m = 0) : (m % 10 :: Nat.digits 10 (m / 10)).sum = (Nat.digits 10 m).sum := by
  rw [Nat.digits_eq_cons_digits_div (by norm_num) (h)]

/--
@isnad1 id=eq.1h1v.s6.110032a18102 from=translated src=- shape=d44f9d97 vocab=8be99540
-/
lemma lemma3 {m : ℕ} (hm : (m % 10) + 1 < 10) :
    (Nat.digits 10 (m + 1)).sum = (Nat.digits 10 m).sum + 1 := by
  rw [Nat.digits_eq_cons_digits_div (by norm_num) (by lia)]
  by_cases h : m = 0
  · simp [h]
  -- strangely `h` cannot be used in place of `by exact h` here.
  nth_rw 2 [Nat.digits_eq_cons_digits_div (by norm_num) (by exact h)]
  simp only [List.sum_cons]
  rw [Nat.add_div_eq_of_add_mod_lt hm, Nat.add_mod_of_add_mod_lt hm]
  lia

/--
@isnad1 id=le.1h3v.s5.cf9feffc4d06 from=translated src=- shape=044354b9 vocab=b70780f5
-/
theorem lemma6 {b : ℕ} {l1 l2 : List ℕ} (hg : List.Forall₂ (· ≤ ·) l1 l2) :
    Nat.ofDigits b l1 ≤ Nat.ofDigits b l2 := by
  induction l1 generalizing l2 with
  | nil => simp_all [Nat.ofDigits]
  | cons hd₁ tl₁ ih₁ =>
    induction l2 generalizing tl₁ with
    | nil => simp_all
    | cons hd₂ tl₂ _ =>
      simp only [Nat.ofDigits_cons]
      have htl : List.Forall₂ (fun x1 x2 ↦ x1 ≤ x2) tl₁ tl₂ := by
        simp_all only [List.forall₂_cons]
      specialize ih₁ htl
      have h1 : hd₁ ≤ hd₂ := by simp_all only [List.forall₂_cons, and_true]
      gcongr

/-- The subtraction of ofDigits of two lists is equal to ofDigits of digit-wise subtraction of them
@isnad1 id=eq.1h3v.s6.03d189ac0e43 from=translated src=- shape=e877e1e0 vocab=74baa489
-/
theorem ofDigits_sub_ofDigits_eq_ofDigits_zipWith {b : ℕ} {l1 l2 : List ℕ}
    (hg : List.Forall₂ (· ≤ ·) l1 l2) :
    Nat.ofDigits b l2 - Nat.ofDigits b l1 =
    Nat.ofDigits b (l2.zipWith (· - ·) l1) := by
  induction l1 generalizing l2 with
  | nil => simp_all [Nat.ofDigits]
  | cons hd₁ tl₁ ih₁ =>
    induction l2 generalizing tl₁ with
    | nil => simp_all
    | cons hd₂ tl₂ ih₂ =>
      simp_all only [Nat.ofDigits_cons, List.zipWith_cons_cons]
      have htl : List.Forall₂ (fun x1 x2 ↦ x1 ≤ x2) tl₁ tl₂ := by
        simp_all only [List.forall₂_cons]
      specialize ih₁ htl
      rw [← ih₁, Nat.mul_sub]
      have h1 : hd₂ ≥ hd₁ := by simp_all only [List.forall₂_cons, and_true]
      have h2 : b * Nat.ofDigits b tl₁ ≤ b * Nat.ofDigits b tl₂ := by
        have : Nat.ofDigits b tl₁ ≤ Nat.ofDigits b tl₂ := lemma6 htl
        gcongr
      lia

/--
@isnad1 id=eq.0h1v.s5.38e171f6c048 from=translated src=- shape=9cb6fc7e vocab=c5b2bddf
-/
lemma lemma8 {n : ℕ} : 10 ^ n - 1 = Nat.ofDigits 10 (List.replicate n 9) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons]
    replace ih : 10 ^ n = Nat.ofDigits 10 (List.replicate n 9) + 1 := by
      have : 1 ≤ 10 ^ n := Nat.one_le_pow' n 9
      lia
    rw [pow_succ, ih]
    lia

/--
@isnad1 id=le.1h2v.s5.7c13d32593f4 from=translated src=- shape=c5498384 vocab=c9a17aec
-/
lemma lemma9 {m n : ℕ} (hm : m < 10^n) : (Nat.digits 10 m).length ≤ n := by
  exact (Nat.digits_length_le_iff (by norm_num) m).mpr hm

def padList (l : List ℕ) (n : ℕ) : List ℕ := l ++ List.replicate (n - l.length) 0

/--
@isnad1 id=eq.0h3v.s5.d5fe02f02724 from=translated src=- shape=824d4e7f vocab=08fd670b
-/
lemma padList_cons {hd n : ℕ} {tl : List ℕ} : padList (hd::tl) (n + 1) = hd :: padList tl n := by
  simp [padList]

def digitsPadded (b m n : ℕ) : List ℕ := padList (Nat.digits b m) n

/--
@isnad1 id=lt.2h4v.s5.ac660ac737e6 from=translated src=- shape=6302efaf vocab=962427de
-/
theorem digitsPadded_lt_base {b m n d : ℕ} (hb : 1 < b)
    (hd : d ∈ digitsPadded b m n) :
    d < b := by
  unfold digitsPadded padList at hd
  simp only [List.mem_append, List.mem_replicate, ne_eq] at hd
  obtain hd | hd := hd
  · exact Nat.digits_lt_base hb hd
  · lia

/--
@isnad1 id=eq.1h3v.s4.300d93b70543 from=translated src=- shape=fe555be6 vocab=2cae20bc
-/
theorem digitsPaddedLength (b m n : ℕ) (hm : (Nat.digits b m).length ≤ n) :
     (digitsPadded b m n).length = n := by
  unfold digitsPadded padList
  simp only [List.length_append, List.length_replicate]
  exact Nat.add_sub_of_le hm

/--
@isnad1 id=ex.0h1v.s5.4f20f1880afe from=translated src=- shape=11dd75ec vocab=f4fc5cf0
-/
theorem exists_prefix (L : List ℕ) :
    ∃ l1 : List ℕ, (∀ hl1 : l1 ≠ [], l1.getLast hl1 ≠ 0) ∧
      ∃ m : ℕ, L = l1 ++ List.replicate m 0 := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨l2, hl20, m, hm⟩ := ih
    by_cases hnil : l2 ≠ []
    · specialize hl20 hnil
      subst hm
      use hd :: l2
      have h5 : ∀ (hl1 : hd :: l2 ≠ []), (hd :: l2).getLast hl1 ≠ 0 := by simp_all
      refine ⟨h5, m, ?_⟩
      simp
    · simp only [ne_eq, Decidable.not_not] at hnil
      subst hnil
      simp only [List.nil_append] at hm
      subst hm
      cases hd with
      | zero =>
        use []
        constructor
        · simp
        · use m + 1
          rw [List.replicate_succ, List.nil_append]
      | succ hd =>
        use [hd + 1]
        constructor
        · simp
        · use m
          simp

/--
@isnad1 id=eq.3h3v.s5.42bb324feb86 from=translated src=- shape=5905e86b vocab=3d9d715c
-/
theorem digitsPadded_ofDigits (b n : ℕ) (h : 1 < b) (L : List ℕ) (w₁ : ∀ l ∈ L, l < b)
    (hn : L.length ≤ n) :
    digitsPadded b (Nat.ofDigits b L) n = padList L n := by
  have ⟨l1, hl1, m, hm⟩ := exists_prefix L
  subst hm
  rw [Nat.ofDigits_append_replicate_zero]
  unfold digitsPadded
  have hl : ∀ l ∈ l1, l < b := by simp_all
  have hl3 : ∀ (h : l1 ≠ []), l1.getLast h ≠ 0 := by simp_all
  rw [Nat.digits_ofDigits b h _ hl hl3]
  simp only [padList, List.length_append, List.length_replicate, List.append_assoc,
             List.replicate_append_replicate, List.append_cancel_left_eq, List.replicate_inj,
             or_true, and_true]
  simp only [List.length_append, List.length_replicate] at hn
  lia

/--
@isnad1 id=eq.0h3v.s4.b5b2c16fea04 from=translated src=- shape=49f783a7 vocab=ce4d08c6
-/
theorem digitsPadded_sum (b m n : ℕ) :
    (digitsPadded b m n).sum = (Nat.digits b m).sum := by
  simp [digitsPadded, padList]

/--
@isnad1 id=eq.0h3v.s5.228f36ea9f5e from=translated src=- shape=70eb3150 vocab=bcc2d6a7
-/
lemma List.map_eq_zip (x : ℕ) (l : List ℕ) (f : ℕ → ℕ → ℕ)
    : (List.map (f x) l) = List.zipWith f (List.replicate l.length x) l := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.length_cons, ih]
    rfl

/--
@isnad1 id=eq.1h2v.s6.33bfa93c14d2 from=translated src=- shape=23142bfe vocab=aaa3b523
-/
lemma lemma5 {m n : ℕ} (hm : m < 10^n) :
    digitsPadded 10 (10^n - 1 - m) n =
    (digitsPadded 10 m n).map (fun d ↦ 9 - d) := by
  let m_digits := Nat.digits 10 m
  let padding := List.replicate (n - m_digits.length) 0
  let m_digits_padded := m_digits ++ padding
  let complement_digits := m_digits_padded.map (λ d ↦ 9 - d)
  have h_length : m_digits_padded.length = n := by
    rw [List.length_append, List.length_replicate]
    have : m_digits.length ≤ n := lemma9 hm
    lia

  have h_sub2 : m = Nat.ofDigits 10 m_digits_padded := by
    unfold m_digits_padded padding m_digits
    rw [Nat.ofDigits_append, Nat.ofDigits_digits, Nat.ofDigits_replicate_zero,
        mul_zero, add_zero]

  have h_length2 : m_digits_padded.length = (List.replicate n 9).length := by
    rw [h_length]
    exact List.length_replicate.symm

  have ha : List.Forall₂ (fun x1 x2 ↦ x1 ≤ x2) m_digits_padded (List.replicate n 9) := by
    unfold m_digits_padded padding
    rw [List.forall₂_iff_get]
    refine ⟨h_length2, ?_⟩
    intro i h1 h2
    simp only [List.get_eq_getElem, List.getElem_replicate]
    obtain hl | hr := Nat.lt_or_ge i m_digits.length
    · rw [List.getElem_append_left hl]
      unfold m_digits
      have h3 : (Nat.digits 10 m)[i] ∈ Nat.digits 10 m := List.getElem_mem hl
      have : (Nat.digits 10 m)[i] < 10 := Nat.digits_lt_base' h3
      exact Nat.le_of_lt_succ this
    · rw [List.getElem_append_right hr]
      simp

  have h_sub : 10^n - 1 - m = Nat.ofDigits 10 complement_digits := by
    have h1 := ofDigits_sub_ofDigits_eq_ofDigits_zipWith (b := 10) ha
    have h2 : List.zipWith (fun x1 x2 ↦ x1 - x2) (List.replicate n 9) m_digits_padded =
           List.map (fun d ↦ 9 - d) m_digits_padded := by
      have h5 := List.map_eq_zip 9 m_digits_padded (fun x y ↦ x - y)
      rw [h5]
      rw [h_length]
    rw [h2] at h1
    unfold complement_digits
    rw [← h1, ← lemma8, h_sub2]
  rw [h_sub]
  have h12 : ∀ l ∈ complement_digits, l < 10 := by
    intro x hx
    simp only [List.map_append, List.mem_append, List.mem_map, complement_digits, m_digits_padded,
               padding, m_digits] at hx
    lia
  have h14 : complement_digits.length ≤ n := by
    simp only [List.map_append, List.length_append, List.length_map, complement_digits,
               m_digits_padded, padding, List.length_replicate, m_digits]
    have : (Nat.digits 10 m).length ≤ n := lemma9 hm
    simp_all
  have h13 := digitsPadded_ofDigits 10 n (by norm_num) complement_digits h12 h14
  rw [h13]

  have h16 : (Nat.digits 10 m).length ≤ n := lemma9 hm
  simp [digitsPadded, padList, List.map_append, List.map_replicate, tsub_zero, complement_digits,
        m_digits_padded, padding, m_digits, h16]

/--
@isnad1 id=and.1h2v.s6.33abbace7b0f from=translated src=- shape=10a059dc vocab=ab2be6b0
-/
lemma List.sum_map_sub_aux (l1 l2 : List ℕ) (h2 : List.Forall₂ (· ≤ ·) l1 l2) :
    (List.zipWith (fun x1 x2 ↦ x1 - x2) l2 l1).sum = l2.sum - l1.sum ∧ l1.sum ≤ l2.sum := by
  match l1, l2 with
  | [], [] => simp
  | [], h :: tl => simp_all
  | h :: tl, [] => simp_all
  | hd1 :: tl1, hd2 :: tl2 =>
    have hp : List.Forall₂ (fun x1 x2 ↦ x1 ≤ x2) tl1 tl2 := by simp_all only [List.forall₂_cons]
    have ih := List.sum_map_sub_aux tl1 tl2 hp
    simp only [List.zipWith_cons_cons, List.sum_cons]
    rw [ih.1]
    have h3 : hd1 ≤ hd2 := (List.forall₂_cons.mp h2).1
    lia

/--
@isnad1 id=eq.1h2v.s6.3633f1ef40d5 from=translated src=- shape=6d8ef2e9 vocab=ab2be6b0
-/
lemma List.sum_map_sub (l1 l2 : List ℕ) (h2 : List.Forall₂ (· ≤ ·) l1 l2) :
    (List.zipWith (fun x1 x2 ↦ x1 - x2) l2 l1).sum = l2.sum - l1.sum :=
  (List.sum_map_sub_aux l1 l2 h2).1

/--
@isnad1 id=eq.1h2v.s6.e38aa58f57c2 from=translated src=- shape=b0ce992e vocab=ac524842
-/
lemma lemma4 {m n : ℕ} (hm : m < 10^n) :
    (Nat.digits 10 (10^n - 1 - m)).sum = 9 * n - (Nat.digits 10 m).sum := by
  rw [← digitsPadded_sum, lemma5 hm]
  have h2 := List.map_eq_zip 9 (digitsPadded 10 m n) (· - ·)
  rw [h2]
  have h5 : List.Forall₂ (· ≤ ·)
              (digitsPadded 10 m n) (List.replicate (digitsPadded 10 m n).length 9) := by
     rw [List.forall₂_iff_get]
     refine ⟨List.length_replicate.symm, fun x1 hx1 hx2 => ?_⟩
     simp only [List.get_eq_getElem, List.getElem_replicate]
     have h7 := digitsPadded_lt_base (show 1 < 10 by norm_num) (List.getElem_mem hx1)
     lia
  have h4 := List.sum_map_sub _ _ h5
  simp only [List.sum_replicate, smul_eq_mul] at h4
  rw [mul_comm]
  have h6 := digitsPaddedLength _ _ _ (lemma9 hm)
  rw [h6] at h4 ⊢
  rw [digitsPadded_sum] at h4
  exact h4

abbrev solution : ℕ → ℕ := fun n ↦ 9 * 2 ^ n

end Usa1992P1
