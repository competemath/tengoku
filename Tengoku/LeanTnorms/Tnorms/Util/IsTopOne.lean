/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Define the `IsTopOneClass` which states that `1` is a top element.  This class is similar to the
  `IsBotZeroClass` in Mathlib and this file is modeled after it.  Unlike `IsBotZeroClass`, the dual
  of `IsTopOneClass` is not mathematically useful, since very few algebraic structures have `0` as
  their largest element. `IsTopOneClass` also implies `IsBotZeroClass` under some mild assumptions.
-/

public section
namespace Tengoku.LeanTnorms end Tengoku.LeanTnorms open Tengoku.LeanTnorms 
/-- A typeclass expressing that the `1` of a type is a top element. In a partial `OrderBot`, this
is equivalent to `⊤ = 1`.-/
class _root_.Tengoku.LeanTnorms.IsTopOneClass (α : Type*) [LE α] [One α] : Prop where
  isTop_one : IsTop (1 : α)

instance _root_.Tengoku.LeanTnorms.instOneTop_unitInterval : IsTopOneClass unitInterval where
  isTop_one p := by
    rw [← Subtype.coe_le_coe]
    exact p.2.2

variable {α : Type*} {a b : α}

section LE
variable [LE α] [One α] [IsTopOneClass α]

theorem _root_.Tengoku.LeanTnorms.isTop_one : IsTop (1 : α) := IsTopOneClass.isTop_one

@[simp]
theorem _root_.Tengoku.LeanTnorms.le_one {a : α} : a ≤ 1 := isTop_one a

variable (α) in
/-- Create an `OrderTop` instance, setting `1` as the bottom element.-/
@[implicit_reducible]
def Tengoku.LeanTnorms.IsTopOneClass.toOrderTop : OrderTop α where
  top := 1
  le_top _ := le_one

end LE

-- See note [lower instance priority]

section Preorder
variable [Preorder α] [One α] [IsTopOneClass α]

@[simp]
theorem _root_.Tengoku.LeanTnorms.not_one_lt : ¬ 1 < a := le_one.not_gt

theorem _root_.Tengoku.LeanTnorms.lt_one_of_gt (h : a < b) : a < 1 := le_one.trans_lt' h

alias LT.lt.lt_one := lt_one_of_gt

theorem _root_.Tengoku.LeanTnorms.ne_one_of_lt' (h : a < b) : a ≠ 1 := h.lt_one.ne

alias LT.lt.ne_one' := ne_one_of_lt'

end Preorder

section PartialOrder
variable [PartialOrder α] [One α] [IsTopOneClass α]

theorem _root_.Tengoku.LeanTnorms.top_eq_one [OrderTop α] : (⊤ : α) = 1 := isTop_one.eq_top.symm

theorem _root_.Tengoku.LeanTnorms.one_eq_top [OrderTop α] : 1 = (⊤ : α) := top_eq_one.symm

@[simp]
theorem _root_.Tengoku.LeanTnorms.one_le_iff_eq_one : 1 ≤ a ↔ a = 1 := le_one.ge_iff_eq

alias ⟨eq_one_of_one_le, _⟩ := le_one_iff_eq_one
alias LE.le.eq_one' := eq_one_of_le_one

theorem _root_.Tengoku.LeanTnorms.lt_one_iff_ne_one : a < 1 ↔ a ≠ 1 := le_one.lt_iff_ne

alias ⟨_, lt_one_of_ne_one⟩ := lt_one_iff_ne_one
alias Ne.lt_one := lt_one_of_ne_one

theorem _root_.Tengoku.LeanTnorms.eq_one_or_lt_one (a : α) : a = 1 ∨ a < 1 := le_one.eq_or_lt

lemma _root_.Tengoku.LeanTnorms.one_notMem_iff' {s : Set α} : 1 ∉ s ↔ ∀ x ∈ s, x < 1 :=
  let := IsTopOneClass.toOrderTop α
  top_notMem_iff

end PartialOrder

section LinearOrder
variable [LinearOrder α] [One α] [IsTopOneClass α]

theorem _root_.Tengoku.LeanTnorms.one_min' (a : α) : min 1 a = a := by simp

theorem _root_.Tengoku.LeanTnorms.min_one' (a : α) : min a 1 = a := by simp

theorem _root_.Tengoku.LeanTnorms.one_max' (a : α) : max 1 a = 1 := by simp

theorem _root_.Tengoku.LeanTnorms.max_one' (a : α) : max a 1 = 1 := by simp

@[simp]
theorem _root_.Tengoku.LeanTnorms.max_eq_one' {a b : α} : max a b = 1 ↔ a = 1 ∨ b = 1 :=
  let := IsTopOneClass.toOrderTop α
  max_eq_top

@[simp]
theorem _root_.Tengoku.LeanTnorms.min_eq_one' {a b : α} : min a b = 1 ↔ a = 1 ∧ b = 1 :=
  let := IsTopOneClass.toOrderTop α
  min_eq_top

end LinearOrder

section SemilatticeInf
variable [SemilatticeInf α] [One α] [IsTopOneClass α]

theorem _root_.Tengoku.LeanTnorms.one_inf' (a : α) : 1 ⊓ a = a := by simp

theorem _root_.Tengoku.LeanTnorms.inf_one' (a : α) : a ⊓ 1 = a := by simp

@[simp]
theorem _root_.Tengoku.LeanTnorms.inf_eq_one {a b : α} : a ⊓ b = 1 ↔ a = 1 ∧ b = 1 :=
  let := IsTopOneClass.toOrderTop α
  inf_eq_top_iff

end SemilatticeInf

section SemilatticeSup
variable [SemilatticeSup α] [One α] [IsTopOneClass α]

theorem _root_.Tengoku.LeanTnorms.one_sup' (a : α) : 1 ⊔ a = 1 := by simp

theorem _root_.Tengoku.LeanTnorms.sup_one' (a : α) : a ⊔ 1 = 1 := by simp

end SemilatticeSup

section OrderedMonoid

variable {M : Type*}

lemma _root_.Tengoku.LeanTnorms.mul_le_left [LE M] [MulOneClass M] [MulLeftMono M] [IsTopOneClass M]
    (p q : M) : p * q ≤ p := by
  nth_rw 2 [← mul_one p]
  exact mul_le_mul_right le_one p

lemma _root_.Tengoku.LeanTnorms.mul_le_right [LE M] [MulOneClass M] [MulRightMono M] [IsTopOneClass M]
    (p q : M) : p * q ≤ q := by
  nth_rw 2 [← one_mul q]
  exact mul_le_mul_left le_one q

instance _root_.Tengoku.LeanTnorms.instIsBotZeroClassOfIsTopOneClassLeft [LE M] [MulZeroOneClass M] [MulLeftMono M]
    [IsTopOneClass M] : IsBotZeroClass M where
  isBot_zero a := mul_zero a ▸ mul_le_left a 0

instance _root_.Tengoku.LeanTnorms.instIsBotZeroClassOfIsTopOneClassRight [LE M] [MulZeroOneClass M] [MulRightMono M]
    [IsTopOneClass M] : IsBotZeroClass M where
  isBot_zero a := zero_mul a ▸ mul_le_right 0 a

end OrderedMonoid
-- Tengoku: root names of this library moved to Tengoku.LeanTnorms so they do not collide with other libraries (generated)
