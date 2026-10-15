/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/
module

public import Tengoku.LeanPool.LeanPool.FourAP.Basic
public import Tengoku

/-!
# The reverse binary order

This file formalizes the order `◁` introduced before Lemma 1 in the paper
“A 4AP-free permutation of the positive integers”.  The least significant
unequal bit decides the comparison, with `1` preceding `0`.  Dividing by two
removes a common least significant bit.  We use this recursive description
both for a computable comparison and for the elementary proofs in the paper.
-/

@[expose] public section

namespace FourAP

/-- The binary comparison from the paragraph defining `◁` in the paper.
It returns `true` precisely when the first argument precedes the second.
The special case `(0, 0)` ends the recursion after all bits have been removed. -/
def binaryCompare (a b : ℕ) : Bool :=
  if a + b = 0 then false
  else if a % 2 = b % 2 then binaryCompare (a / 2) (b / 2)
  else decide (b % 2 < a % 2)
termination_by a + b
decreasing_by omega

/-- The paper's strict order `◁`, the reverse order on binary strings when
compared at their first unequal bit starting from the least significant end. -/
def bits (a b : ℕ) : Prop := binaryCompare a b = true

/-- Binary comparison is decidable by the recursion defining the paper's order. -/
instance bitsDecidable : DecidableRel bits := fun _ _ => inferInstanceAs (Decidable (_ = true))

/-- At equal zero strings, there is no first unequal bit.
@isnad1 id=not.0h0v.s3.d64db949c0d9 from=translated src=- shape=90d9b386 vocab=b2aa6a65
-/
@[simp] theorem not_bits_zero_zero : ¬ bits 0 0 := by
  simp [bits, binaryCompare]

/-- Recursive form of the paper's definition: compare the low bits first,
then discard them if they agree.
@isnad1 id=iff.0h2v.s6.98ccce7e55a8 from=translated src=- shape=8bce4450 vocab=12671939
-/
theorem bits_iff (a b : ℕ) :
    bits a b ↔ b % 2 < a % 2 ∨ (a % 2 = b % 2 ∧ bits (a / 2) (b / 2)) := by
  by_cases hz : a + b = 0
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst a
    subst b
    simp
  · unfold bits
    rw [binaryCompare]
    simp only [hz, ↓reduceIte]
    by_cases hp : a % 2 = b % 2
    · simp [hp]
    · simp [hp]

/-- Equal parity allows the rescaling described in the self-similarity
paragraph of the paper.
@isnad1 id=iff.1h2v.s6.d1f4029264d8 from=translated src=- shape=90663e00 vocab=f1485363
-/
theorem bits_iff_of_same_parity {a b : ℕ} (hp : a % 2 = b % 2) :
    bits a b ↔ bits (a / 2) (b / 2) := by
  rw [bits_iff]
  simp [hp]

/-- For unequal parity, the least significant bit already decides the order.
@isnad1 id=iff.1h2v.s6.9edf79c0052b from=translated src=- shape=a23f2c17 vocab=fa355243
-/
theorem bits_iff_of_diff_parity {a b : ℕ} (hp : a % 2 ≠ b % 2) :
    bits a b ↔ b % 2 < a % 2 := by
  rw [bits_iff]
  simp [hp]

/-- Self-similarity of `◁` on the even integers (before Lemma 1).
@isnad1 id=iff.0h2v.s5.fcbeb193bc6d from=translated src=- shape=e929eefb vocab=58914110
-/
@[simp] theorem bits_even_even (a b : ℕ) : bits (2 * a) (2 * b) ↔ bits a b := by
  rw [bits_iff]
  simp

/-- Self-similarity of `◁` on the odd integers (before Lemma 1).
@isnad1 id=iff.0h2v.s5.aa1307c6c1da from=translated src=- shape=2fcd7b2c vocab=d8713b91
-/
@[simp] theorem bits_odd_odd (a b : ℕ) :
    bits (2 * a + 1) (2 * b + 1) ↔ bits a b := by
  rw [bits_iff]
  have ha : (2 * a + 1) / 2 = a := by omega
  have hb : (2 * b + 1) / 2 = b := by omega
  simp [ha, hb, Nat.add_mod]

/-- The two parity restrictions have the same rescaled order, as used in
Lemma 2. Here `p = 0` selects the even part and `p = 1` the odd part.
@isnad1 id=iff.1h3v.s5.7f76b34e7936 from=translated src=- shape=bc8a36bc vocab=57665f35
-/
theorem bits_parity (a b p : ℕ) (hp : p < 2) :
    bits (2 * a + p) (2 * b + p) ↔ bits a b := by
  have : p = 0 ∨ p = 1 := by omega
  rcases this with rfl | rfl <;> simp

/-- All odd integers precede all even integers (the self-similarity paragraph).
@isnad1 id=bits.0h2v.s5.f229f8c3d21c from=translated src=- shape=b90a5cf9 vocab=d8713b91
-/
theorem bits_odd_even (a b : ℕ) : bits (2 * a + 1) (2 * b) := by
  rw [bits_iff]
  left
  omega

/-- The converse parity comparison never holds.
@isnad1 id=not.0h2v.s5.bbf8059656c5 from=translated src=- shape=9686e28e vocab=d8713b91
-/
theorem not_bits_even_odd (a b : ℕ) : ¬ bits (2 * a) (2 * b + 1) := by
  rw [bits_iff]
  omega

/-- Irreflexivity verifies that the paper's binary comparison is strict.
@isnad1 id=not.0h1v.s2.de2b91a6c454 from=translated src=- shape=66a6bd96 vocab=b2aa6a65
-/
theorem bits_irrefl (a : ℕ) : ¬ bits a a := by
  by_cases ha : a = 0
  · subst a
    exact not_bits_zero_zero
  · rw [bits_iff_of_same_parity rfl]
    exact bits_irrefl (a / 2)
termination_by a
decreasing_by omega

/-- Two entries compared strictly in `◁` are different.
@isnad1 id=ne.1h2v.s3.f9392fdd8b82 from=translated src=- shape=37236ace vocab=b2aa6a65
-/
theorem bits_ne {a b : ℕ} (h : bits a b) : a ≠ b := by
  rintro rfl
  exact bits_irrefl a h

/-- Asymmetry is part of the verification that `◁` is a strict linear order.
@isnad1 id=not.1h2v.s3.83d36efa8f0f from=translated src=- shape=4115e120 vocab=b2aa6a65
-/
theorem bits_asymm {a b : ℕ} (hab : bits a b) : ¬ bits b a := by
  have hne : a ≠ b := bits_ne hab
  rw [bits_iff] at hab ⊢
  rcases hab with hp | ⟨hp, hab⟩
  · rintro (hq | ⟨hq, _⟩) <;> omega
  · rintro (hq | ⟨_, hba⟩)
    · omega
    · exact bits_asymm hab hba
termination_by a + b
decreasing_by omega

/-- Any distinct binary strings have a first unequal bit: totality of `◁`.
@isnad1 id=or.1h2v.s4.f62d333b3fe9 from=translated src=- shape=1f4f79a3 vocab=b2aa6a65
-/
theorem bits_total {a b : ℕ} (hne : a ≠ b) : bits a b ∨ bits b a := by
  by_cases hp : a % 2 = b % 2
  · have hq : a / 2 ≠ b / 2 := by omega
    rw [bits_iff_of_same_parity hp, bits_iff_of_same_parity hp.symm]
    exact bits_total hq
  · rw [bits_iff_of_diff_parity hp, bits_iff_of_diff_parity (Ne.symm hp)]
    omega
termination_by a + b
decreasing_by omega

/-- Transitivity completes the elementary verification that the binary
comparison in the paper defines a strict linear order.
@isnad1 id=bits.2h3v.s4.9e80ad15a18d from=translated src=- shape=0bc0c4a6 vocab=b2aa6a65
-/
theorem bits_trans {a b c : ℕ} (hab : bits a b) (hbc : bits b c) : bits a c := by
  have hne : a ≠ b := bits_ne hab
  rw [bits_iff] at hab hbc ⊢
  rcases hab with hp | ⟨hp, hab⟩
  · rcases hbc with hq | ⟨hq, _⟩
    · exact Or.inl (lt_trans hq hp)
    · left
      omega
  · rcases hbc with hq | ⟨hq, hbc⟩
    · left
      omega
    · exact Or.inr ⟨hp.trans hq, bits_trans hab hbc⟩
termination_by a + b + c
decreasing_by omega

/-- Zero cannot precede any integer, as asserted just before the discussion
of the literature in the paper.
@isnad1 id=not.0h1v.s3.a87bcd5d8a5f from=translated src=- shape=a237e748 vocab=b2aa6a65
-/
theorem not_bits_zero (a : ℕ) : ¬ bits 0 a := by
  by_cases ha : a = 0
  · subst a
    exact not_bits_zero_zero
  · rw [bits_iff]
    rintro (hp | ⟨_, h⟩)
    · omega
    · exact not_bits_zero (a / 2) h
termination_by a
decreasing_by omega

/-- Zero is the greatest element of `◁` (used in Lemma 2's base case).
@isnad1 id=bits.1h1v.s4.31f8ff194894 from=translated src=- shape=5a715b29 vocab=b2aa6a65
-/
theorem bits_zero {a : ℕ} (ha : a ≠ 0) : bits a 0 := by
  rcases bits_total ha with h | h
  · exact h
  · exact False.elim (not_bits_zero a h)

/-- The elementary 3AP-freeness proof preceding equation (1). If the low bits
agree we divide all entries by two; otherwise the middle low bit differs from
both endpoint low bits, and two consecutive comparisons are impossible.
The equations include increasing and decreasing progressions alike.
@isnad1 id=not.1h3v.s5.babff7db810c from=translated src=- shape=06ebc4fe vocab=d8713b91
-/
theorem bits_no_three_of_eq {a b c : ℕ} (hap : a + c = 2 * b) :
    ¬ (bits a b ∧ bits b c) := by
  rintro ⟨hab, hbc⟩
  have hne : a ≠ b := bits_ne hab
  by_cases hp : a % 2 = b % 2
  · have hq : b % 2 = c % 2 := by omega
    have heq : a / 2 + c / 2 = 2 * (b / 2) := by omega
    exact bits_no_three_of_eq heq
      ⟨(bits_iff_of_same_parity hp).mp hab,
       (bits_iff_of_same_parity hq).mp hbc⟩
  · have hq : b % 2 ≠ c % 2 := by omega
    have h₁ := (bits_iff_of_diff_parity hp).mp hab
    have h₂ := (bits_iff_of_diff_parity hq).mp hbc
    omega
termination_by a + b + c
decreasing_by omega

/-- The dual order also contains no 3AP, as used in Lemma 1.
@isnad1 id=not.1h3v.s5.12efc3304540 from=translated src=- shape=855b8379 vocab=d8713b91
-/
theorem bits_dual_no_three {a b c : ℕ} (hap : a + c = 2 * b) :
    ¬ (bits b a ∧ bits c b) := by
  rintro ⟨hba, hcb⟩
  exact bits_no_three_of_eq (by omega : c + a = 2 * b) ⟨hcb, hba⟩

/-- Equation (1), labelled `eq:pairs` in the paper, in equation form.
For four consecutive AP terms, the first and third adjacent pairs compare
in the same direction. The proof removes common low bits until parity differs.
@isnad1 id=iff.2h4v.s6.8a85f9bd63f1 from=translated src=- shape=ea64e7ac vocab=d8713b91
-/
theorem bits_pairs_of_eq {a b c d : ℕ}
    (h₁ : a + c = 2 * b) (h₂ : b + d = 2 * c) :
    bits a b ↔ bits c d := by
  by_cases hz : a + b + c + d = 0
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    have hc : c = 0 := by omega
    have hd : d = 0 := by omega
    subst a
    subst b
    subst c
    subst d
    rfl
  · by_cases hp : a % 2 = b % 2
    · have hq : c % 2 = d % 2 := by omega
      have heq₁ : a / 2 + c / 2 = 2 * (b / 2) := by omega
      have heq₂ : b / 2 + d / 2 = 2 * (c / 2) := by omega
      rw [bits_iff_of_same_parity hp, bits_iff_of_same_parity hq]
      exact bits_pairs_of_eq heq₁ heq₂
    · have hq : c % 2 ≠ d % 2 := by omega
      rw [bits_iff_of_diff_parity hp, bits_iff_of_diff_parity hq]
      omega
termination_by a + b + c + d
decreasing_by omega

/-- Equation (1) of the paper, packaged for a nonconstant four-term AP.
@isnad1 id=iff.1h4v.s4.b1a361be33bf from=translated src=- shape=0ca165f7 vocab=c03f529d
-/
theorem bits_pairs {a b c d : ℕ} (hap : IsAP4 a b c d) :
    bits a b ↔ bits c d := bits_pairs_of_eq hap.2.1 hap.2.2

/-- In particular the binary order itself is 4AP-free; this starts the
construction with the empty safe prefix.
@isnad1 id=apfree.0h0v.s1.851552ea3354 from=translated src=- shape=49959d42 vocab=f1e6e42a
-/
theorem bits_apFree : APFree bits := by
  intro a b c d hap hab hbc _hcd
  exact bits_no_three_of_eq hap.2.1 ⟨hab, hbc⟩

/-- Equality of the lowest binary digits is equality of parity. This is the
bridge between the recursive definition and the binary-digit description
in the paper.
@isnad1 id=iff.0h2v.s5.9550867e95a3 from=translated src=- shape=67070a50 vocab=97c54398
-/
theorem testBit_zero_eq_iff (a b : ℕ) :
    a.testBit 0 = b.testBit 0 ↔ a % 2 = b % 2 := by
  simp only [Nat.testBit_zero, decide_eq_decide]
  omega

/-- A strict binary comparison exhibits the first unequal bit, with the
first integer's bit equal to one and the second integer's bit equal to zero.
This is the forward direction of the paper's defining description of `◁`.
@isnad1 id=ex.1h2v.s5.18e93ff5884a from=translated src=- shape=27fa2416 vocab=cc0d8339
-/
theorem exists_first_differing_bit {a b : ℕ} (hab : bits a b) :
    ∃ k, (∀ i < k, a.testBit i = b.testBit i) ∧
      a.testBit k = true ∧ b.testBit k = false := by
  have hne : a ≠ b := bits_ne hab
  rw [bits_iff] at hab
  rcases hab with hp | ⟨hp, hab⟩
  · refine ⟨0, ?_, ?_, ?_⟩
    · intro i hi; omega
    · simp only [Nat.testBit_zero, decide_eq_true_eq]
      omega
    · simp only [Nat.testBit_zero, decide_eq_false_iff_not]
      omega
  · obtain ⟨k, hlow, ha, hb⟩ := exists_first_differing_bit hab
    refine ⟨k + 1, ?_, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero => exact (testBit_zero_eq_iff a b).mpr hp
      | succ i =>
        simpa only [Nat.testBit_succ] using hlow i (by omega)
    · simpa only [Nat.testBit_succ] using ha
    · simpa only [Nat.testBit_succ] using hb
termination_by a + b
decreasing_by omega

/-- Conversely, the least significant unequal bit determines the recursive
comparison. This is the backward direction of the paper's definition.
@isnad1 id=bits.3h3v.s5.7b532e6ba65f from=translated src=- shape=4068132f vocab=cc0d8339
-/
theorem bits_of_first_differing_bit {a b k : ℕ}
    (hlow : ∀ i < k, a.testBit i = b.testBit i)
    (ha : a.testBit k = true) (hb : b.testBit k = false) : bits a b := by
  induction k generalizing a b with
  | zero =>
    rw [bits_iff]
    left
    simp only [Nat.testBit_zero, decide_eq_true_eq] at ha
    simp only [Nat.testBit_zero, decide_eq_false_iff_not] at hb
    omega
  | succ k ih =>
    have hp : a % 2 = b % 2 :=
      (testBit_zero_eq_iff a b).mp (hlow 0 (by omega))
    rw [bits_iff_of_same_parity hp]
    apply ih
    · intro i hi
      simpa only [Nat.testBit_succ] using hlow (i + 1) (by omega)
    · simpa only [Nat.testBit_succ] using ha
    · simpa only [Nat.testBit_succ] using hb

/-- The definition of `◁` in the paper, stated literally using binary digits.
There is a first differing digit, and its values are respectively `1` and `0`.
Thus our executable recursion is exactly the order described in the text.
@isnad1 id=iff.0h2v.s5.02f038cdc8e0 from=translated src=- shape=cc4a62eb vocab=cc0d8339
-/
theorem bits_iff_first_differing_bit (a b : ℕ) :
    bits a b ↔ ∃ k, (∀ i < k, a.testBit i = b.testBit i) ∧
      a.testBit k = true ∧ b.testBit k = false := by
  constructor
  · exact exists_first_differing_bit
  · rintro ⟨k, hlow, ha, hb⟩
    exact bits_of_first_differing_bit hlow ha hb

/-- The displayed eight-element example from the paper:
`7 ◁ 3 ◁ 5 ◁ 1 ◁ 6 ◁ 2 ◁ 4 ◁ 0`.
`Pairwise` records every comparison in this finite ordered list.
@isnad1 id=pairwise.0h0v.s5.4e864204f2e6 from=translated src=- shape=230d9d16 vocab=c19ef515
-/
theorem bits_eight_example : List.Pairwise bits [7, 3, 5, 1, 6, 2, 4, 0] := by
  decide +kernel

end FourAP
