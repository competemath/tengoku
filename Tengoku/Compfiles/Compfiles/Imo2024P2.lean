/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 2024, Problem 2

Determine all pairs (a,b) of positive integers for which there exist positive integers
g and N such that

   gcd(aⁿ + b, bⁿ + a),   n = 1, 2, ...

holds for all integers n ≥ N.
-/

namespace Imo2024P2

/-
We consider the sequence modulo `ab+1`; if the exponent is `-1` modulo `φ(ab+1)`, the terms
are zero modulo `ab+1`, so `ab+1` divides `g`, and all sufficiently large terms, so all terms,
from which we conclude that `a=b=1`.
-/

open scoped Nat

/-- The condition of the problem. -/
def Condition (a b : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ ∃ g N : ℕ, 0 < g ∧ 0 < N ∧ ∀ n : ℕ, N ≤ n → Nat.gcd (a ^ n + b) (b ^ n + a) = g

/--
@isnad1 id=iff.2h5v.s7.202d93d93e64 from=translated src=- shape=d4d69777 vocab=9ad44b0e
-/
lemma dvd_pow_iff_of_dvd_sub {a b d n : ℕ} {z : ℤ} (ha : a.Coprime d)
    (hd : (φ d : ℤ) ∣ (n : ℤ) - z) :
    d ∣ a ^ n + b ↔ (((ZMod.unitOfCoprime _ ha) ^ z : (ZMod d)ˣ) : ZMod d) + b = 0 := by
  obtain ⟨k, hk⟩ := hd
  rw [show z = n + (-k) * φ d by lia]
  rw [zpow_add, zpow_mul', ← ZMod.natCast_eq_zero_iff]
  simp

namespace Condition

variable {a b : ℕ} (h : Condition a b)

section
include h

/--
@isnad1 id=lt.1h2v.s4.28fe47b71c8b from=translated src=- shape=949fefb0 vocab=4d1d8202
-/
lemma a_pos : 0 < a := h.1

/--
@isnad1 id=lt.1h2v.s4.ab922ab693a7 from=translated src=- shape=f99f57a5 vocab=4d1d8202
-/
lemma b_pos : 0 < b := h.2.1

/-- The value of `g` in the problem (determined by `a` and `b`). -/
noncomputable def g : ℕ := h.2.2.choose

/--
@isnad1 id=ex.1h2v.s6.6c268cf75d4c from=translated src=- shape=dcfeee60 vocab=a44b623e
-/
lemma g_spec : ∃ N : ℕ, 0 < h.g ∧ 0 < N ∧ ∀ n : ℕ, N ≤ n → Nat.gcd (a ^ n + b) (b ^ n + a) = h.g :=
  h.2.2.choose_spec

/-- The value of `N` in the problem (any sufficiently large value). -/
noncomputable def N : ℕ := h.g_spec.choose

/--
@isnad1 id=and.1h2v.s6.f13ad3cbc30b from=translated src=- shape=55692084 vocab=f6063bda
-/
lemma N_spec : 0 < h.g ∧ 0 < h.N ∧ ∀ n : ℕ, h.N ≤ n → Nat.gcd (a ^ n + b) (b ^ n + a) = h.g :=
  h.g_spec.choose_spec

/--
@isnad1 id=lt.1h2v.s4.78fa8886f98c from=translated src=- shape=c799e463 vocab=9f7ba56b
-/
lemma g_pos : 0 < h.g := h.N_spec.1

/--
@isnad1 id=lt.1h2v.s4.50e253819a25 from=translated src=- shape=c799e463 vocab=0003938f
-/
lemma N_pos : 0 < h.N := h.N_spec.2.1

/--
@isnad1 id=eq.2h3v.s6.374566d29ef2 from=translated src=- shape=3c82a7e5 vocab=bc8df4ba
-/
lemma gcd_eq_g {n : ℕ} (hn : h.N ≤ n) : Nat.gcd (a ^ n + b) (b ^ n + a) = h.g := h.N_spec.2.2 n hn

/--
@isnad1 id=conditio.1h2v.s3.ddba1b8191ee from=translated src=- shape=7e524d71 vocab=49af749a
-/
protected lemma symm : Condition b a := by
  refine ⟨h.b_pos, h.a_pos, h.g, h.N, h.g_pos, h.N_pos, fun n hn ↦ ?_⟩
  rw [Nat.gcd_comm]
  exact h.gcd_eq_g hn

/--
@isnad1 id=dvd.4h4v.s6.c78c898df10c from=translated src=- shape=f47becf3 vocab=c96c6988
-/
lemma dvd_g_of_le_N_of_dvd {n : ℕ} (hn : h.N ≤ n) {d : ℕ} (hab : d ∣ a ^ n + b)
    (hba : d ∣ b ^ n + a) : d ∣ h.g := by
  rw [← h.gcd_eq_g hn, Nat.dvd_gcd_iff]
  exact ⟨hab, hba⟩

end

/--
@isnad1 id=coprime.0h2v.s4.d1ed235bb5b6 from=translated src=- shape=976a6e73 vocab=f7395964
-/
lemma a_coprime_ab_add_one : a.Coprime (a * b + 1) := by
  simp

/-- A sufficiently large value of n, congruent to `-1` mod `φ (a * b + 1)`. -/
noncomputable def large_n : ℕ := (max h.N h.symm.N + 1) * φ (a * b + 1) - 1

/--
@isnad1 id=eq.1h2v.s4.5ca46e35354b from=translated src=- shape=90ed22ad vocab=da8ffbf6
-/
lemma symm_large_n : h.symm.large_n = h.large_n := by
  simp_rw [large_n]
  congr 2
  · rw [max_comm]
  · rw [mul_comm]

/--
@isnad1 id=le.1h2v.s4.7e42433e99f2 from=translated src=- shape=fb0951f5 vocab=5bf68878
-/
lemma N_le_large_n : h.N ≤ h.large_n := by
  have hp : 0 < φ (a * b + 1) := Nat.totient_pos.2 (Nat.add_pos_right _ zero_lt_one)
  rw [large_n, add_mul, one_mul, Nat.add_sub_assoc (Nat.one_le_of_lt hp)]
  suffices h.N ≤ h.N * φ (a * b + 1) + (φ (a * b + 1) - 1) by
    refine this.trans ?_
    gcongr
    simp
  exact Nat.le_add_right_of_le (Nat.le_mul_of_pos_right _ hp)

/--
@isnad1 id=dvd.1h2v.s5.f4b6c8b3369c from=translated src=- shape=65a71532 vocab=28408769
-/
lemma dvd_large_n_sub_neg_one : (φ (a * b + 1) : ℤ) ∣ (h.large_n : ℤ) - (-1 : ℤ) := by
  simp [large_n]

/-- A sufficiently large value of n, congruent to `0` mod `φ (a * b + 1)`. -/
noncomputable def large_n_0 : ℕ := (max h.N h.symm.N) * φ (a * b + 1)

/--
@isnad1 id=eq.1h2v.s4.9113dfd08d48 from=translated src=- shape=90ed22ad vocab=844e0695
-/
lemma symm_large_n_0 : h.symm.large_n_0 = h.large_n_0 := by
  simp_rw [large_n_0]
  congr 1
  · rw [max_comm]
  · rw [mul_comm]

/--
@isnad1 id=le.1h2v.s4.4cc32cf9d252 from=translated src=- shape=fb0951f5 vocab=bed2545b
-/
lemma N_le_large_n_0 : h.N ≤ h.large_n_0 := by
  have hp : 0 < φ (a * b + 1) := Nat.totient_pos.2 (Nat.add_pos_right _ zero_lt_one)
  rw [large_n_0]
  suffices h.N ≤ h.N * φ (a * b + 1) by
    refine this.trans ?_
    gcongr
    simp
  exact Nat.le_mul_of_pos_right _ hp

/--
@isnad1 id=dvd.1h2v.s5.f4328aa15057 from=translated src=- shape=448ace6f vocab=9a4442b0
-/
lemma dvd_large_n_0_sub_zero : (φ (a * b + 1) : ℤ) ∣ (h.large_n_0 : ℤ) - (0 : ℤ) := by
  simp [large_n_0]

/--
@isnad1 id=dvd.1h2v.s5.9ca6311f8fbc from=translated src=- shape=b81082b5 vocab=c955881c
-/
lemma ab_add_one_dvd_a_pow_large_n_add_b : a * b + 1 ∣ a ^ h.large_n + b := by
  rw [dvd_pow_iff_of_dvd_sub a_coprime_ab_add_one h.dvd_large_n_sub_neg_one, zpow_neg, zpow_one]
  suffices ((ZMod.unitOfCoprime _ a_coprime_ab_add_one : (ZMod (a * b + 1))ˣ) : ZMod (a * b + 1)) *
    ((((ZMod.unitOfCoprime _ a_coprime_ab_add_one)⁻¹ : (ZMod (a * b + 1))ˣ) :
      ZMod (a * b + 1)) + (b : ZMod (a * b + 1))) = 0 from
      (IsUnit.mul_right_eq_zero (ZMod.unitOfCoprime _ a_coprime_ab_add_one).isUnit).1 this
  rw [mul_add]
  norm_cast
  simp only [mul_inv_cancel, Units.val_one, ZMod.coe_unitOfCoprime]
  norm_cast
  convert ZMod.natCast_self (a * b + 1) using 2
  exact add_comm _ _

/--
@isnad1 id=dvd.1h2v.s5.02c6cea4a631 from=translated src=- shape=94a0616d vocab=c955881c
-/
lemma ab_add_one_dvd_b_pow_large_n_add_a : a * b + 1 ∣ b ^ h.large_n + a := by
  convert h.symm.ab_add_one_dvd_a_pow_large_n_add_b using 1
  · rw [mul_comm]
  · rw [h.symm_large_n]

/--
@isnad1 id=dvd.1h2v.s5.531388139de6 from=translated src=- shape=427c8996 vocab=88a4f1a5
-/
lemma ab_add_one_dvd_g : a * b + 1 ∣ h.g :=
  h.dvd_g_of_le_N_of_dvd h.N_le_large_n h.ab_add_one_dvd_a_pow_large_n_add_b
    h.ab_add_one_dvd_b_pow_large_n_add_a

/--
@isnad1 id=dvd.1h2v.s5.8f340259919e from=translated src=- shape=b81082b5 vocab=1fd907f0
-/
lemma ab_add_one_dvd_a_pow_large_n_0_add_b : a * b + 1 ∣ a ^ h.large_n_0 + b := by
  refine h.ab_add_one_dvd_g.trans ?_
  rw [← h.gcd_eq_g h.N_le_large_n_0]
  exact Nat.gcd_dvd_left _ _

include h

/--
@isnad1 id=dvd.1h2v.s5.38ae612b920f from=translated src=- shape=e974fa58 vocab=45ddfca8
-/
lemma ab_add_one_dvd_b_add_one : a * b + 1 ∣ b + 1 := by
  rw [add_comm b]
  suffices a * b + 1 ∣ a ^ h.large_n_0 + b by
    rw [dvd_pow_iff_of_dvd_sub a_coprime_ab_add_one h.dvd_large_n_0_sub_zero, zpow_zero] at this
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    norm_cast at this
  exact h.ab_add_one_dvd_a_pow_large_n_0_add_b

/--
@isnad1 id=eq.1h2v.s4.fdec43da0692 from=translated src=- shape=025a27bb vocab=49af749a
-/
lemma a_eq_one : a = 1 := by
  have hle : a * b + 1 ≤ b + 1 := Nat.le_of_dvd (by lia) h.ab_add_one_dvd_b_add_one
  rw [add_le_add_iff_right] at hle
  suffices a ≤ 1 by
    have hp := h.a_pos
    lia
  have hle' : a * b ≤ 1 * b := by
    simpa using hle
  exact Nat.le_of_mul_le_mul_right hle' h.b_pos

/--
@isnad1 id=eq.1h2v.s4.8580159638d4 from=translated src=- shape=ee2c62e5 vocab=49af749a
-/
lemma b_eq_one : b = 1 := h.symm.a_eq_one

end Condition

abbrev solutionSet : Set (ℕ+ × ℕ+) := {(1, 1)}

end Imo2024P2
