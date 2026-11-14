/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.NumberTheory.Elementary.Divisibility
import Tengoku.Seed.Data.ZMod.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 同余、剩余环与中国剩余定理

本文件把自然数同余和剩余环中的相等连接起来，集中给出同余对加法、乘法、乘方的相容性，
并以“共同解存在”和“剩余环同构”两种形式陈述互素模数的中国剩余定理。
-/

namespace SandronesLibrary.NumberTheory.Elementary

/-- Natural numbers are congruent modulo `n` when they have the same remainder upon division by
`n`.  This definition also covers modulus zero.

> **Entry**: number-theory.elementary.congruence-/
def Congruent (n a b : ℕ) : Prop :=
  a % n = b % n

/-- The textbook remainder definition agrees with Mathlib's `Nat.ModEq`.-/
theorem congruent_iff_modEq (n a b : ℕ) : Congruent n a b ↔ a ≡ b [MOD n] := by
  rfl

/-- 自然数模 `n` 同余，当且仅当它们在剩余环 `ZMod n` 中表示同一个元素。
> **Entry**: number-theory.elementary.congruence-/
theorem modEq_iff_zmod_eq (n a b : ℕ) :
    a ≡ b [MOD n] ↔ (a : ZMod n) = (b : ZMod n) := by
  exact (ZMod.natCast_eq_natCast_iff a b n).symm

/-- 同余关系同时保持加法、乘法和自然数次幂。
> **Entry**: number-theory.elementary.congruence-/
theorem modEq_add_mul_pow {n a b c d k : ℕ} (hab : a ≡ b [MOD n])
    (hcd : c ≡ d [MOD n]) :
    a + c ≡ b + d [MOD n] ∧ a * c ≡ b * d [MOD n] ∧ a ^ k ≡ b ^ k [MOD n] := by
  exact ⟨hab.add hcd, hab.mul hcd, hab.pow k⟩

/-- The textbook congruence relation is compatible with addition, multiplication, and powers.-/
theorem congruent_add_mul_pow {n a b c d k : ℕ} (hab : Congruent n a b)
    (hcd : Congruent n c d) :
    Congruent n (a + c) (b + d) ∧ Congruent n (a * c) (b * d) ∧
      Congruent n (a ^ k) (b ^ k) := by
  rw [congruent_iff_modEq] at hab hcd
  exact ⟨hab.add hcd, hab.mul hcd, hab.pow k⟩

/-- **中国剩余定理（存在形式）**：互素模数下，任意两个指定余数有共同解。
> **Entry**: number-theory.elementary.chinese-remainder-/
theorem chinese_remainder_exists {m n a b : ℕ} (h : m.Coprime n) :
    ∃ x : ℕ, x ≡ a [MOD m] ∧ x ≡ b [MOD n] := by
  exact ⟨Nat.chineseRemainder h a b, (Nat.chineseRemainder h a b).property⟩

/-- Chinese remainder theorem stated with the textbook congruence relation.-/
theorem chinese_remainder_exists_congruent {m n a b : ℕ} (h : m.Coprime n) :
    ∃ x : ℕ, Congruent m x a ∧ Congruent n x b := by
  obtain ⟨x, hxa, hxb⟩ := chinese_remainder_exists h
  exact ⟨x, (congruent_iff_modEq _ _ _).2 hxa, (congruent_iff_modEq _ _ _).2 hxb⟩

/-- **中国剩余定理（结构形式）**：模 `mn` 的剩余环同构于模 `m`、模 `n` 剩余环的直积。
> **Entry**: number-theory.elementary.chinese-remainder-/
noncomputable def chineseRemainderEquiv {m n : ℕ} (h : m.Coprime n) :
    ZMod (m * n) ≃+* ZMod m × ZMod n :=
  ZMod.chineseRemainder h

end SandronesLibrary.NumberTheory.Elementary
