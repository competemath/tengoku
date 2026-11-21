/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Tengoku

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

/--
@isnad1 id=istopone.0h0v.s4.d3bf956662a2 from=translated src=- shape=049cd614 vocab=6dfd6d5d
-/
instance _root_.Tengoku.LeanTnorms.instOneTop_unitInterval : IsTopOneClass unitInterval where
  isTop_one p := by
    rw [← Subtype.coe_le_coe]
    exact p.2.2

variable {α : Type*} {a b : α}

section LE
variable [LE α] [One α] [IsTopOneClass α]

/--
@isnad1 id=istop.0h1v.s4.a396cb449cb9 from=translated src=- shape=8b3a4111 vocab=4741af3b
-/
theorem _root_.Tengoku.LeanTnorms.isTop_one : IsTop (1 : α) := IsTopOneClass.isTop_one

/--
@isnad1 id=le.0h2v.s4.04f7b39c466d from=translated src=- shape=83c94174 vocab=fdee57a8
-/
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

/--
@isnad1 id=not.0h2v.s4.46f9db1ee082 from=translated src=- shape=3025512c vocab=0b1fdb91
-/
@[simp]
theorem _root_.Tengoku.LeanTnorms.not_one_lt : ¬ 1 < a := le_one.not_gt

/--
@isnad1 id=lt.1h3v.s5.760d77aa7e6d from=translated src=- shape=5968fc32 vocab=0b1fdb91
-/
theorem _root_.Tengoku.LeanTnorms.lt_one_of_gt (h : a < b) : a < 1 := le_one.trans_lt' h

/--
@isnad1 id=lt.1h3v.s5.760d77aa7e6d from=translated src=- shape=5968fc32 vocab=0b1fdb91
-/
alias LT.lt.lt_one := lt_one_of_gt

/--
@isnad1 id=ne.1h3v.s5.00187c8d9782 from=translated src=- shape=50d298d0 vocab=0b1fdb91
-/
theorem _root_.Tengoku.LeanTnorms.ne_one_of_lt' (h : a < b) : a ≠ 1 := h.lt_one.ne

/--
@isnad1 id=ne.1h3v.s5.00187c8d9782 from=translated src=- shape=50d298d0 vocab=0b1fdb91
-/
alias LT.lt.ne_one' := ne_one_of_lt'

end Preorder

section PartialOrder
variable [PartialOrder α] [One α] [IsTopOneClass α]

/--
@isnad1 id=eq.0h1v.s5.bed3db53faad from=translated src=- shape=c36186dc vocab=be42ca77
-/
theorem _root_.Tengoku.LeanTnorms.top_eq_one [OrderTop α] : (⊤ : α) = 1 := isTop_one.eq_top.symm

/--
@isnad1 id=eq.0h1v.s5.7dfa8f099cee from=translated src=- shape=270ba7b6 vocab=be42ca77
-/
theorem _root_.Tengoku.LeanTnorms.one_eq_top [OrderTop α] : 1 = (⊤ : α) := top_eq_one.symm

/--
@isnad1 id=iff.0h2v.s5.6bcfc5f0c9b3 from=translated src=- shape=1ea034a3 vocab=b0171571
-/
@[simp]
theorem _root_.Tengoku.LeanTnorms.one_le_iff_eq_one : 1 ≤ a ↔ a = 1 := le_one.ge_iff_eq

alias ⟨Tengoku.LeanTnorms.eq_one_of_one_le, _⟩ := le_one_iff_eq_one
alias LE.le.eq_one' := eq_one_of_le_one

/--
@isnad1 id=iff.0h2v.s5.a6776bf6f651 from=translated src=- shape=1c4da498 vocab=c229f365
-/
theorem _root_.Tengoku.LeanTnorms.lt_one_iff_ne_one : a < 1 ↔ a ≠ 1 := le_one.lt_iff_ne

/--
@isnad1 id=lt.1h2v.s5.2e65eef5fb6d from=translated src=- shape=e063fc2b vocab=c229f365
-/
alias ⟨_, Tengoku.LeanTnorms.lt_one_of_ne_one⟩ := lt_one_iff_ne_one
/--
@isnad1 id=lt.1h2v.s5.2e65eef5fb6d from=translated src=- shape=e063fc2b vocab=c229f365
-/
alias Ne.lt_one := lt_one_of_ne_one

theorem _root_.Tengoku.LeanTnorms.eq_one_or_lt_one (a : α) : a = 1 ∨ a < 1 := le_one.eq_or_lt

/--
@isnad1 id=iff.0h2v.s5.e74ccc7fae91 from=translated src=- shape=f8f3a2fa vocab=7e57385c
-/
lemma _root_.Tengoku.LeanTnorms.one_notMem_iff' {s : Set α} : 1 ∉ s ↔ ∀ x ∈ s, x < 1 :=
  let := IsTopOneClass.toOrderTop α
  top_notMem_iff

end PartialOrder

section LinearOrder
variable [LinearOrder α] [One α] [IsTopOneClass α]

/--
@isnad1 id=eq.0h2v.s5.614efc4d0f52 from=translated src=- shape=4c2340e7 vocab=5821096a
-/
theorem _root_.Tengoku.LeanTnorms.one_min' (a : α) : min 1 a = a := by simp

/--
@isnad1 id=eq.0h2v.s5.4bdf57224c19 from=translated src=- shape=9add8af8 vocab=5821096a
-/
theorem _root_.Tengoku.LeanTnorms.min_one' (a : α) : min a 1 = a := by simp

/--
@isnad1 id=eq.0h2v.s5.e9cd5fc8af4c from=translated src=- shape=6a5d68bb vocab=829aee18
-/
theorem _root_.Tengoku.LeanTnorms.one_max' (a : α) : max 1 a = 1 := by simp

/--
@isnad1 id=eq.0h2v.s5.f524a93057f1 from=translated src=- shape=9938c0df vocab=829aee18
-/
theorem _root_.Tengoku.LeanTnorms.max_one' (a : α) : max a 1 = 1 := by simp

/--
@isnad1 id=iff.0h3v.s6.61d9630c4b9f from=translated src=- shape=cc849372 vocab=829aee18
-/
@[simp]
theorem _root_.Tengoku.LeanTnorms.max_eq_one' {a b : α} : max a b = 1 ↔ a = 1 ∨ b = 1 :=
  let := IsTopOneClass.toOrderTop α
  max_eq_top

/--
@isnad1 id=iff.0h3v.s6.b3beb88e69af from=translated src=- shape=cc849372 vocab=5821096a
-/
@[simp]
theorem _root_.Tengoku.LeanTnorms.min_eq_one' {a b : α} : min a b = 1 ↔ a = 1 ∧ b = 1 :=
  let := IsTopOneClass.toOrderTop α
  min_eq_top

end LinearOrder

section SemilatticeInf
variable [SemilatticeInf α] [One α] [IsTopOneClass α]

/--
@isnad1 id=eq.0h2v.s5.73c6a6fdec46 from=translated src=- shape=4c2340e7 vocab=c9e45a83
-/
theorem _root_.Tengoku.LeanTnorms.one_inf' (a : α) : 1 ⊓ a = a := by simp

/--
@isnad1 id=eq.0h2v.s5.bae12b206ef2 from=translated src=- shape=9add8af8 vocab=c9e45a83
-/
theorem _root_.Tengoku.LeanTnorms.inf_one' (a : α) : a ⊓ 1 = a := by simp

/--
@isnad1 id=iff.0h3v.s5.c27ceaeb8e54 from=translated src=- shape=cc849372 vocab=c9e45a83
-/
@[simp]
theorem _root_.Tengoku.LeanTnorms.inf_eq_one {a b : α} : a ⊓ b = 1 ↔ a = 1 ∧ b = 1 :=
  let := IsTopOneClass.toOrderTop α
  inf_eq_top_iff

end SemilatticeInf

section SemilatticeSup
variable [SemilatticeSup α] [One α] [IsTopOneClass α]

/--
@isnad1 id=eq.0h2v.s5.c65726acb38f from=translated src=- shape=6a5d68bb vocab=34c4141f
-/
theorem _root_.Tengoku.LeanTnorms.one_sup' (a : α) : 1 ⊔ a = 1 := by simp

/--
@isnad1 id=eq.0h2v.s5.8587416363c5 from=translated src=- shape=9938c0df vocab=34c4141f
-/
theorem _root_.Tengoku.LeanTnorms.sup_one' (a : α) : a ⊔ 1 = 1 := by simp

end SemilatticeSup

section OrderedMonoid

variable {M : Type*}

/--
@isnad1 id=le.0h3v.s5.209e3df86aa1 from=translated src=- shape=db2f7978 vocab=2abf31fd
-/
lemma _root_.Tengoku.LeanTnorms.mul_le_left [LE M] [MulOneClass M] [MulLeftMono M] [IsTopOneClass M]
    (p q : M) : p * q ≤ p := by
  nth_rw 2 [← mul_one p]
  exact mul_le_mul_right le_one p

/--
@isnad1 id=le.0h3v.s5.4926c3f5a90c from=translated src=- shape=06f73a51 vocab=0d3e236c
-/
lemma _root_.Tengoku.LeanTnorms.mul_le_right [LE M] [MulOneClass M] [MulRightMono M] [IsTopOneClass M]
    (p q : M) : p * q ≤ q := by
  nth_rw 2 [← one_mul q]
  exact mul_le_mul_left le_one q

/--
@isnad1 id=isbotzer.0h1v.s5.1bcfda861e3e from=translated src=- shape=7ddc04c7 vocab=b0625cbb
-/
instance _root_.Tengoku.LeanTnorms.instIsBotZeroClassOfIsTopOneClassLeft [LE M] [MulZeroOneClass M] [MulLeftMono M]
    [IsTopOneClass M] : IsBotZeroClass M where
  isBot_zero a := mul_zero a ▸ mul_le_left a 0

/--
@isnad1 id=isbotzer.0h1v.s5.82bd524357a9 from=translated src=- shape=7ddc04c7 vocab=0e8909db
-/
instance _root_.Tengoku.LeanTnorms.instIsBotZeroClassOfIsTopOneClassRight [LE M] [MulZeroOneClass M] [MulRightMono M]
    [IsTopOneClass M] : IsBotZeroClass M where
  isBot_zero a := zero_mul a ▸ mul_le_right 0 a

end OrderedMonoid
-- Tengoku: root names of this library moved to Tengoku.LeanTnorms so they do not collide with other libraries (generated)
