/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.BigOperators.Pi
public import Tengoku.Seed.Algebra.Group.Action.Pointwise.Set.Basic
public import Tengoku.Seed.Algebra.Group.Pi.Basic
public import Tengoku.Seed.GroupTheory.GroupAction.DomAct.Basic

/-!
# Translation operator

This file defines the translation of a function from a group by an element of that group.

## Notation

`τ a f` is notation for `translate a f`.

## See also

Generally, translation is the same as acting on the domain by subtraction. This setting is
abstracted by `DomAddAct` in such a way that `τ a f = DomAddAct.mk (-a) +ᵥ f` (see
`translate_eq_domAddActMk_vadd`). Using `DomAddAct` is irritating in applications because of this
negation appearing inside `DomAddAct.mk`. Although mathematically equivalent, the pen and paper
convention is that translating is an action by subtraction, not by addition.
-/

@[expose] public section

open Function Set
open scoped Pointwise

variable {ι α β M G H : Type*} [AddCommGroup G]

/-- Translation of a function in a group by an element of that group.
`τ a f` is defined as `x ↦ f (x - a)`. -/
def translate (a : G) (f : G → α) : G → α := fun x ↦ f (x - a)

@[inherit_doc] scoped[translate] notation "τ " => translate

open scoped translate

/--
@isnad1 id=eq.0h5v.s5.9610b2f29b9c from=seed src=0 shape=a729c836 vocab=36a37978
-/
@[simp] lemma translate_apply (a : G) (f : G → α) (x : G) : τ a f x = f (x - a) := rfl
/--
@isnad1 id=eq.0h3v.s5.5c47a42c19ae from=seed src=0 shape=2ecb2ae6 vocab=0b76cbeb
-/
@[simp] lemma translate_zero (f : G → α) : τ 0 f = f := by ext; simp

/--
@isnad1 id=eq.0h5v.s5.e94a62d21bdf from=seed src=0 shape=b982e752 vocab=26ce7b9e
-/
lemma translate_translate (a b : G) (f : G → α) : τ a (τ b f) = τ (a + b) f := by
  ext; simp [sub_sub]

/--
@isnad1 id=eq.0h5v.s5.581519b3ac87 from=seed src=0 shape=342b8c2c vocab=26ce7b9e
-/
lemma translate_add (a b : G) (f : G → α) : τ (a + b) f = τ a (τ b f) := by ext; simp [sub_sub]

/-- See `translate_add`
@isnad1 id=eq.0h5v.s5.79eae0262d93 from=seed src=0 shape=597c0987 vocab=26ce7b9e
-/
lemma translate_add' (a b : G) (f : G → α) : τ (a + b) f = τ b (τ a f) := by
  rw [add_comm, translate_add]

/--
@isnad1 id=eq.0h5v.s5.e45c7dcaa78b from=seed src=0 shape=39b2a2e8 vocab=0b76cbeb
-/
lemma translate_comm (a b : G) (f : G → α) : τ a (τ b f) = τ b (τ a f) := by
  rw [← translate_add, translate_add']

-- We make `simp` push the `τ` outside
/--
@isnad1 id=eq.0h6v.s5.86c18f04b5f8 from=seed src=0 shape=7340e3f1 vocab=6293d2cf
-/
@[simp] lemma comp_translate (a : G) (f : G → α) (g : α → β) : g ∘ τ a f = τ a (g ∘ f) := rfl

/--
@isnad1 id=eq.0h4v.s6.93ce57ad9705 from=seed src=0 shape=04cccba1 vocab=9f59685f
-/
lemma translate_eq_domAddActMk_vadd (a : G) (f : G → α) : τ a f = DomAddAct.mk (-a) +ᵥ f := by
  ext; simp [DomAddAct.vadd_apply, sub_eq_neg_add]

/--
@isnad1 id=eq.0h6v.s6.d42b2c41aa49 from=seed src=0 shape=beb67e81 vocab=ebc4dda2
-/
@[simp]
lemma translate_smul_right [SMul H α] (a : G) (f : G → α) (c : H) : τ a (c • f) = c • τ a f := rfl

/--
@isnad1 id=eq.0h3v.s5.1af659661aa3 from=seed src=0 shape=ca50c53e vocab=520832cd
-/
@[simp] lemma translate_zero_right [Zero α] (a : G) : τ a (0 : G → α) = 0 := rfl
/--
@isnad1 id=eq.0h5v.s6.eab3686bd9e6 from=seed src=0 shape=44a7b71a vocab=2ac49cbf
-/
lemma translate_add_right [Add α] (a : G) (f g : G → α) : τ a (f + g) = τ a f + τ a g := rfl
/--
@isnad1 id=eq.0h5v.s6.e3223fc997d3 from=seed src=0 shape=44a7b71a vocab=56da529f
-/
lemma translate_sub_right [Sub α] (a : G) (f g : G → α) : τ a (f - g) = τ a f - τ a g := rfl
/--
@isnad1 id=eq.0h4v.s5.dec7255f542f from=seed src=0 shape=48df5137 vocab=c0f3a0df
-/
lemma translate_neg_right [Neg α] (a : G) (f : G → α) : τ a (-f) = -τ a f := rfl

section AddCommMonoid
variable [AddCommMonoid M]

/--
@isnad1 id=eq.0h6v.s6.0e7a392e2048 from=seed src=0 shape=29c73d0f vocab=69124c17
-/
lemma translate_sum_right (a : G) (f : ι → G → M) (s : Finset ι) :
    τ a (∑ i ∈ s, f i) = ∑ i ∈ s, τ a (f i) := by ext; simp

/--
@isnad1 id=eq.0h4v.s5.ba96c91d30a7 from=seed src=0 shape=ff3d03a4 vocab=3c9eb4c3
-/
lemma sum_translate [Fintype G] (a : G) (f : G → M) : ∑ b, τ a f b = ∑ b, f b :=
  Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ ↦ rfl

end AddCommMonoid

section AddCommGroup
variable [AddCommGroup H]

/--
@isnad1 id=eq.0h4v.s6.c4fcf478ea6a from=seed src=0 shape=fdff0299 vocab=33708254
-/
@[simp] lemma support_translate (a : G) (f : G → H) : support (τ a f) = a +ᵥ support f := by
  ext; simp [mem_vadd_set_iff_neg_vadd_mem, sub_eq_neg_add]

end AddCommGroup

variable [CommMonoid M]

/--
@isnad1 id=eq.0h6v.s6.3e007db8b744 from=seed src=0 shape=29c73d0f vocab=6af45523
-/
lemma translate_prod_right (a : G) (f : ι → G → M) (s : Finset ι) :
    τ a (∏ i ∈ s, f i) = ∏ i ∈ s, τ a (f i) := by ext; simp
