/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
module

public import Tengoku
import Std.Tactic.BVDecide.Normalize.Prop

/-!
This file contains a list of theorems required during the implementation of this dsl
and the creation of the proof for the otp example.
Some of them might actually already exists in the mathlib but
i had trouble finding them.
-/

@[expose] public section

/--
@isnad1 id=var.1h4v.s4.9516fc96f71a from=translated src=- shape=f7812673 vocab=e3b0c442
-/
theorem excluded_middle_implication : ∀ (P Q C : Prop),
  (P ∧ Q → C) ∧ (P ∧ ¬Q → C) →
  P →
  C
  := by
  intros P Q C
  tauto

/--
@isnad1 id=iff.0h3v.s6.e696f7cd764f from=translated src=- shape=e9132f3b vocab=8c0d3764
-/
theorem Nat.mod_succ_eq {a b m : ℕ} : a % m = b % m ↔ (a + 1) % m = (b + 1) % m := by
  constructor
  · exact add_mod_eq_add_mod_right 1
  · intro h₁
    rw [← ModEq] at *
    exact ModEq.add_right_cancel' 1 h₁

/--
@isnad1 id=le.1h2v.s4.456ad479d187 from=translated src=- shape=294e6570 vocab=cf369417
-/
theorem Nat.le_sub_one_le : ∀ (n m : Nat), n ≤ m → n - 1 ≤ m := by
  intros n m h
  omega

/--
@isnad1 id=iff.0h1v.s4.dfa9d501acd7 from=translated src=- shape=5954ff65 vocab=6ff3cf84
-/
theorem Nat.gt_zero_le_one : ∀ (n : ℕ),
  (0 < n) ↔ 1 ≤ n := by
  intros n
  omega

/--
@isnad1 id=lt.1h2v.s4.1d1fbedae9ef from=translated src=- shape=911613f2 vocab=13a96747
-/
theorem Nat.add_gt_zero_gt_zero : ∀ (n m: ℕ) ,
  0 < n →
  0 < n + m
  := by
  intros n m h
  omega

/--
@isnad1 id=lt.1h2v.s4.c0b19541e9a0 from=translated src=- shape=e4f3c5c0 vocab=edd5cb09
-/
theorem Nat.add_gt_zero : ∀ (n m : Nat),
  n > 0 →
  n + m > 0 := by
  intros n m h
  omega

/--
@isnad1 id=lt.2h2v.s5.f4dac9005c59 from=translated src=- shape=a37ca708 vocab=13a96747
-/
theorem Nat.gt_and_neq_succ_gt_succ : ∀ (n m : ℕ), n < m → m ≠ n + 1 → n + 1 < m := by
  intros n m h₁ h₂
  grind

/--
@isnad1 id=iff.0h3v.s5.0a4475f31242 from=translated src=- shape=c1705657 vocab=13a96747
-/
theorem Nat.lt_add_cancel_right : ∀ (n m k: ℕ),
  n + k < m + k ↔ n < m
  := by
  simp

/--
@isnad1 id=lt.2h3v.s5.6b619fa79f5b from=translated src=- shape=f5b88549 vocab=2c881234
-/
theorem Nat.lt_sub_left : ∀ (a b c : ℕ),
  b < a →
  a < b + c →
  a - b < c := by
  intros a b c BLtA ALtBC
  omega

/--
@isnad1 id=lt.3h3v.s5.6e61bc59f3f9 from=translated src=- shape=6a812222 vocab=13d82426
-/
theorem Nat.size_sub_lt_size : ∀ (x l s: Nat),
  l < s →
  x ≤ l →
  x ≥ 1 →
  l - x + 1 < s := by
  intros x l s hl hx h1
  omega

/--
@isnad1 id=ne.1h1v.s4.a33b67952417 from=translated src=- shape=23aa8b17 vocab=cd913208
-/
theorem UInt64.gt_zero_neq_zero : ∀ (u:UInt64),
  u > 0 → u ≠ 0 := by
  intro u h neq
  simp_all

/--
@isnad1 id=iff.0h1v.s3.d69bd610a470 from=translated src=- shape=7fb1b6fe vocab=632e87e5
-/
theorem UInt64.lt_zero : ∀ (u:UInt64), u < 0 ↔ False := by
  simp

/--
@isnad1 id=iff.0h2v.s4.d94f74fc1128 from=translated src=- shape=e5555f7a vocab=a730b297
-/
theorem UInt64.lt_toNat_iff : ∀ (u i : UInt64),
  u.toNat < i.toNat ↔ u < i := fun _ _ => Iff.rfl

/--
@isnad1 id=iff.0h2v.s4.4e50a17aad48 from=translated src=- shape=e5555f7a vocab=3c1f7e4d
-/
theorem UInt64.le_toNat_iff : ∀ (u i : UInt64),
  u.toNat ≤ i.toNat ↔ u ≤ i := fun _ _ => Iff.rfl

/--
@isnad1 id=lt.2h4v.s5.848f50c42bb0 from=translated src=- shape=6bee0241 vocab=1f5e933b
-/
theorem UInt64.add_lt_add : ∀ (n m k c : UInt64),
  n < m ∧ k < c →
  m.toNat + c.toNat < UInt64.size →
  n + k < m + c := by
  rintro n m k c ⟨hlt_l, hlt_r⟩ hsum
  have hfin : n.toNat + k.toNat < m.toNat + c.toNat := Nat.add_lt_add hlt_l hlt_r
  have mcNat : (m + c).toNat = m.toNat + c.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hsum]
  have nkNat : (n + k).toNat = n.toNat + k.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (Nat.lt_trans hfin hsum)]
  rw [←UInt64.lt_toNat_iff, mcNat, nkNat]
  exact hfin

/--
@isnad1 id=iff.0h3v.s4.fd1fcee64828 from=translated src=- shape=c1705657 vocab=8c9d1920
-/
theorem UInt64.add_cancel_right_iff : ∀ (u i k : UInt64),
  u + k = i + k ↔ u = i := by
  simp_all

/--
@isnad1 id=iff.0h3v.s4.b27add8ed467 from=translated src=- shape=d590f6f2 vocab=8c9d1920
-/
theorem UInt64.add_cancel_left_iff : ∀ (u i k: UInt64),
  k + u = k + i ↔ u = i := by
  simp_all

/--
@isnad1 id=eq.2h3v.s6.611ca6619920 from=translated src=- shape=803a1325 vocab=41304cc8
-/
theorem UInt64.add_sub_assoc : ∀ (p l x : UInt64),
  x ≤ l →
  x > 0 →
  p + (l - x) + 1 = p + (l - (x - 1)) := by
  intros p l x h_xLeL h_xGtZ
  grind only

/--
@isnad1 id=ne.1h3v.s5.7a41496a9c45 from=translated src=- shape=901c2968 vocab=a303c379
-/
theorem UInt64.add_right_ne_of_lt : ∀ (n i l : UInt64),
  i < l →
  n + l ≠ n + i := by
  intro n i l h_iLtl neq
  simp_all

instance instPreorderUInt64LeanPool : Preorder UInt64 where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := by simp
  le_trans := by apply UInt64.le_trans
  lt_iff_le_not_ge := by
    intros a b
    constructor
    · intro h
      simpa only [UInt64.not_le] using ⟨UInt64.le_of_lt h, h⟩
    · simp
