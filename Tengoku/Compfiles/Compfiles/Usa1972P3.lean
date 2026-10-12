/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shalev Wengrowsky
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 1972, Problem 3

A random number selector can only select one of the nine integers 1, 2, ..., 9,
and it makes these selections with equal probability. Determine the probability
that after n selections, where n > 1, the product of the n numbers selected will
be divisible by 10.
-/

namespace Usa1972P3

abbrev Digit := Fin 9
abbrev DigitSeq (n : ℕ) := Fin n → Digit

noncomputable def unifDistN (n : ℕ) := PMF.uniformOfFintype (DigitSeq n)

def to_nat_digit : Digit → ℕ := fun d ↦ d + 1
def is_good_seq {n : ℕ} (s : DigitSeq n) := 10 ∣ ∏a, to_nat_digit (s a)
def good_seqs {n : ℕ} := {s : DigitSeq n | is_good_seq s}

abbrev HasEven {n : ℕ} (s : DigitSeq n) : Prop := ∃ i, Even (to_nat_digit (s i))
abbrev HasFive {n : ℕ} (s : DigitSeq n) : Prop := ∃ i, to_nat_digit (s i) = 5
abbrev NoEven {n : ℕ} (s : DigitSeq n) : Prop := ∀ i, ¬ Even (to_nat_digit (s i))
abbrev NoFive {n : ℕ} (s : DigitSeq n) : Prop := ∀ i, to_nat_digit (s i) ≠ 5

/--
@isnad1 id=eq.0h2v.s6.ed0a605db045 from=translated src=- shape=cc9192ab vocab=ae3e4840
-/
lemma card_all_digits {n : ℕ} (P : Digit → Prop) [DecidablePred P] :
    Fintype.card {s : DigitSeq n // ∀ i, P (s i)} =
      Fintype.card {d : Digit // P d} ^ n := by
  simpa [DigitSeq, Fintype.card_fun] using
    Fintype.card_congr
      (Equiv.subtypePiEquivPi (β := fun _ : Fin n => Digit) (p := fun _ d => P d))

/--
@isnad1 id=iff.0h1v.s4.3c60169cfd10 from=translated src=- shape=d68478ae vocab=1aa12de3
-/
lemma digit_dvd_five_iff (d : Digit) : 5 ∣ to_nat_digit d ↔ to_nat_digit d = 5 := by
  fin_cases d <;> norm_num [to_nat_digit]

/--
@isnad1 id=eq.0h0v.s5.1c545d2fc36a from=translated src=- shape=2cc15afb vocab=e53169b0
-/
lemma card_digits_noFive :
    Fintype.card {d : Digit // to_nat_digit d ≠ 5} = 8 := by decide

/--
@isnad1 id=eq.0h0v.s5.cb9b81769a4e from=translated src=- shape=696131b6 vocab=afcfb7ae
-/
lemma card_digits_noEven :
    Fintype.card {d : Digit // ¬ Even (to_nat_digit d)} = 5 := by decide

/--
@isnad1 id=eq.0h0v.s6.9acef96ad4f5 from=translated src=- shape=64171118 vocab=afcfb7ae
-/
lemma card_digits_noFive_noEven :
    Fintype.card {d : Digit // to_nat_digit d ≠ 5 ∧ ¬ Even (to_nat_digit d)} = 4 := by decide

/--
@isnad1 id=iff.0h1v.s4.df06f6511936 from=translated src=- shape=0079358d vocab=08c57cc2
-/
lemma ten_dvd_iff_two_and_five (m : ℕ) : 10 ∣ m ↔ 2 ∣ m ∧ 5 ∣ m := by
  exact lcm_dvd_iff (a := 2) (b := 5) (c := m)

/--
@isnad1 id=iff.0h2v.s5.d25fb667f2aa from=translated src=- shape=ead718b3 vocab=7c2f0c77
-/
lemma two_dvd_prod_iff_hasEven {n : ℕ} (s : DigitSeq n) :
    2 ∣ ∏ a, to_nat_digit (s a) ↔ HasEven s := by
  rw [Prime.dvd_finsetProd_iff Nat.prime_two.prime]
  simp [HasEven, even_iff_two_dvd]

/--
@isnad1 id=iff.0h2v.s5.6130efe39199 from=translated src=- shape=ead718b3 vocab=8c855a1d
-/
lemma five_dvd_prod_iff_hasFive {n : ℕ} (s : DigitSeq n) :
    5 ∣ ∏ a, to_nat_digit (s a) ↔ HasFive s := by
  rw [Prime.dvd_finsetProd_iff Nat.prime_five.prime]
  simp [HasFive, digit_dvd_five_iff]

/--
@isnad1 id=iff.0h2v.s4.23e73b1e94dc from=translated src=- shape=05032b5d vocab=13b2445f
-/
lemma is_good_seq_iff_hasEven_hasFive {n : ℕ} (s : DigitSeq n) :
    is_good_seq s ↔ HasEven s ∧ HasFive s := by
  rw [is_good_seq, ten_dvd_iff_two_and_five,
    two_dvd_prod_iff_hasEven, five_dvd_prod_iff_hasFive]

/--
@isnad1 id=eq.0h1v.s6.170acc0d4617 from=translated src=- shape=7104124a vocab=57a17be8
-/
lemma card_all_noFive (n : ℕ) :
    Fintype.card {s : DigitSeq n // NoFive s} = 8 ^ n := by
  simpa only [NoFive, card_digits_noFive] using
    (card_all_digits (n := n) fun d => to_nat_digit d ≠ 5)

/--
@isnad1 id=eq.0h1v.s6.e8c688f4199d from=translated src=- shape=7104124a vocab=61f77b13
-/
lemma card_all_noEven (n : ℕ) :
    Fintype.card {s : DigitSeq n // NoEven s} = 5 ^ n := by
  simpa only [NoEven, card_digits_noEven] using
    (card_all_digits (n := n) fun d => ¬ Even (to_nat_digit d))

/--
@isnad1 id=eq.0h1v.s7.90632dba1eec from=translated src=- shape=d5e3406e vocab=9e12697c
-/
lemma card_all_noFive_noEven (n : ℕ) :
    Fintype.card {s : DigitSeq n // NoFive s ∧ NoEven s} = 4 ^ n := by
  simpa only [NoFive, NoEven, forall_and, card_digits_noFive_noEven] using
    (card_all_digits (n := n)
      fun d => to_nat_digit d ≠ 5 ∧ ¬ Even (to_nat_digit d))

-- Inclusion-exclusion on the bad events.
/--
@isnad1 id=eq.0h1v.s6.8f1fade7b2e5 from=translated src=- shape=c89b8fe8 vocab=2daa2097
-/
lemma card_good_balance (n : ℕ) :
    {s : DigitSeq n | is_good_seq s}.ncard + 8 ^ n + 5 ^ n = 9 ^ n + 4 ^ n := by
  let A : Set (DigitSeq n) := {s | NoFive s}
  let B : Set (DigitSeq n) := {s | NoEven s}
  have hgood : {s : DigitSeq n | is_good_seq s} = (A ∪ B)ᶜ := by
    ext s
    simp [A, B, NoFive, NoEven, HasFive, HasEven, is_good_seq_iff_hasEven_hasFive]
    tauto
  have hAcard : A.ncard = 8 ^ n := by
    rw [← Set.fintypeCard_eq_ncard A]
    exact card_all_noFive n
  have hBcard : B.ncard = 5 ^ n := by
    rw [← Set.fintypeCard_eq_ncard B]
    exact card_all_noEven n
  have hABcard : (A ∩ B).ncard = 4 ^ n := by
    have hAB : A ∩ B = {s : DigitSeq n | NoFive s ∧ NoEven s} := by
      ext s
      simp [A, B]
    rw [hAB, ← Set.fintypeCard_eq_ncard]
    exact card_all_noFive_noEven n
  have hUcard : Nat.card (DigitSeq n) = 9 ^ n := by
    rw [Nat.card_eq_fintype_card]
    simp [DigitSeq, Digit]
  have hcompl := Set.ncard_add_ncard_compl (A ∪ B)
  have hunion := Set.ncard_union_add_ncard_inter A B
  rw [hgood]
  rw [hAcard, hBcard, hABcard] at hunion
  rw [hUcard] at hcompl
  lia

/--
@isnad1 id=eq.3h4v.s5.f454b35bfdf7 from=translated src=- shape=9ff790f3 vocab=d042ff62
-/
lemma ennreal_eq_sub_sub_of_add_add_eq {a b c d : ENNReal}
    (hb : b ≠ ⊤) (hc : c ≠ ⊤) (h : (a + c) + b = d) : a = d - b - c := by
  exact ENNReal.eq_sub_of_add_eq hc (ENNReal.eq_sub_of_add_eq hb h)

noncomputable abbrev solution (n : ℕ) : ENNReal :=
  1 + (4 / 9) ^ n - (8 / 9) ^ n - (5 / 9) ^ n

end Usa1972P3
