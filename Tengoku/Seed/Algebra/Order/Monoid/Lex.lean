/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Prod
public import Tengoku.Seed.Algebra.Order.Hom.Monoid
public import Tengoku.Seed.Data.Prod.Lex
public import Tengoku.Seed.Order.Prod.Lex.Hom

/-!
# Order homomorphisms for products of ordered monoids

This file defines order homomorphisms for products of ordered monoids, for both the plain product
and the lexicographic product.

The product of ordered monoids `α × β` is an ordered monoid itself with both natural inclusions
and projections, making it the coproduct as well.

## TODO

Create the "OrdCommMon" category.

-/

@[expose] public section

namespace MonoidHom

variable {α β : Type*} [Monoid α] [Preorder α] [Monoid β] [Preorder β]

/--
@isnad1 id=monotone.0h2v.s6.917a5056b62b from=seed src=0 shape=dfe08969 vocab=05898373
-/
@[to_additive]
lemma inl_mono : Monotone (MonoidHom.inl α β) :=
  fun _ _ ↦ by simp

/--
@isnad1 id=strictmo.0h2v.s6.b0fc25df9389 from=seed src=0 shape=dfe08969 vocab=5451d437
-/
@[to_additive]
lemma inl_strictMono : StrictMono (MonoidHom.inl α β) :=
  fun _ _ ↦ by simp

/--
@isnad1 id=monotone.0h2v.s6.3aa5aec095b2 from=seed src=0 shape=00a24539 vocab=e061348d
-/
@[to_additive]
lemma inr_mono : Monotone (MonoidHom.inr α β) :=
  fun _ _ ↦ by simp

/--
@isnad1 id=strictmo.0h2v.s6.8990a5b5df5c from=seed src=0 shape=00a24539 vocab=e60bccbb
-/
@[to_additive]
lemma inr_strictMono : StrictMono (MonoidHom.inr α β) :=
  fun _ _ ↦ by simp

/--
@isnad1 id=monotone.0h2v.s6.aacaa45f257e from=seed src=0 shape=230ae6a8 vocab=3dd921c1
-/
@[to_additive]
lemma fst_mono : Monotone (MonoidHom.fst α β) :=
  fun _ _ ↦ by simp +contextual [Prod.le_def]

/--
@isnad1 id=monotone.0h2v.s6.7b7b7a040c77 from=seed src=0 shape=8d1c3549 vocab=a38f9f67
-/
@[to_additive]
lemma snd_mono : Monotone (MonoidHom.snd α β) :=
  fun _ _ ↦ by simp +contextual [Prod.le_def]

end MonoidHom

namespace OrderMonoidHom

variable (α β : Type*) [Monoid α] [PartialOrder α] [Monoid β] [Preorder β]

/-- Given ordered monoids M, N, the natural inclusion ordered homomorphism from M to M × N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural inclusion
ordered homomorphism from M to M × N. -/]
def inl : α →*o α × β where
  __ := MonoidHom.inl _ _
  monotone' := MonoidHom.inl_mono

/-- Given ordered monoids M, N, the natural inclusion ordered homomorphism from N to M × N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural inclusion
ordered homomorphism from N to M × N. -/]
def inr : β →*o α × β where
  __ := MonoidHom.inr _ _
  monotone' := MonoidHom.inr_mono

/-- Given ordered monoids M, N, the natural projection ordered homomorphism from M × N to M. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural projection
ordered homomorphism from M × N to M. -/]
def fst : α × β →*o α where
  __ := MonoidHom.fst _ _
  monotone' := MonoidHom.fst_mono

/-- Given ordered monoids M, N, the natural projection ordered homomorphism from M × N to N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural projection
ordered homomorphism from M × N to N. -/]
def snd : α × β →*o β where
  __ := MonoidHom.snd _ _
  monotone' := MonoidHom.snd_mono

/-- Given ordered monoids M, N, the natural inclusion ordered homomorphism from M to the
lexicographic M ×ₗ N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural inclusion
ordered homomorphism from M to the lexicographic M ×ₗ N. -/]
def inlₗ : α →*o α ×ₗ β where
  __ := (Prod.Lex.toLexOrderHom).comp (inl α β)
  map_one' := rfl
  map_mul' := by simp [← toLex_mul]

/-- Given ordered monoids M, N, the natural inclusion ordered homomorphism from N to the
lexicographic M ×ₗ N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural inclusion
ordered homomorphism from N to the lexicographic M ×ₗ N. -/]
def inrₗ : β →*o (α ×ₗ β) where
  __ := Prod.Lex.toLexOrderHom.comp (inr α β)
  map_one' := rfl
  map_mul' := by simp [← toLex_mul]

/-- Given ordered monoids M, N, the natural projection ordered homomorphism from the
lexicographic M ×ₗ N to M. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural projection
ordered homomorphism from the lexicographic M ×ₗ N to M. -/]
def fstₗ : (α ×ₗ β) →*o α where
  toFun p := (ofLex p).fst
  map_one' := rfl
  map_mul' := by simp
  monotone' := Prod.Lex.monotone_fst_ofLex

/--
@isnad1 id=eq.0h2v.s6.7845cca3f969 from=seed src=0 shape=1f3ec40a vocab=92cd3b45
-/
@[to_additive (attr := simp)]
theorem fst_comp_inl : (fst α β).comp (inl α β) = .id α :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.5ccff455868a from=seed src=0 shape=2c9707dc vocab=b0904605
-/
@[to_additive (attr := simp)]
theorem fstₗ_comp_inlₗ : (fstₗ α β).comp (inlₗ α β) = .id α :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.4b11b175d9c3 from=seed src=0 shape=512caa4d vocab=d35b3eca
-/
@[to_additive (attr := simp)]
theorem snd_comp_inl : (snd α β).comp (inl α β) = 1 :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.2117be0c6d12 from=seed src=0 shape=12298dfb vocab=302fcfca
-/
@[to_additive (attr := simp)]
theorem fst_comp_inr : (fst α β).comp (inr α β) = 1 :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.11e837db21de from=seed src=0 shape=3b9a6148 vocab=ad1bbdb5
-/
@[to_additive (attr := simp)]
theorem snd_comp_inr : (snd α β).comp (inr α β) = .id β :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.14c77bbea254 from=seed src=0 shape=9bde83dc vocab=0542f94a
-/
@[to_additive]
theorem inl_mul_inr_eq_mk (m : α) (n : β) : inl α β m * inr α β n = (m, n) := by
  simp

/--
@isnad1 id=eq.0h4v.s8.d00c8053e9ab from=seed src=0 shape=d871adb5 vocab=d3cd571e
-/
@[to_additive]
theorem inlₗ_mul_inrₗ_eq_toLex (m : α) (n : β) : inlₗ α β m * inrₗ α β n = toLex (m, n) := by
  simp [← toLex_mul]

variable {α β}

/--
@isnad1 id=commute.0h4v.s7.b2de8f02f771 from=seed src=0 shape=e48b5e75 vocab=1015aaf4
-/
@[to_additive]
theorem commute_inl_inr (m : α) (n : β) : Commute (inl α β m) (inr α β n) :=
  Commute.prod (.one_right m) (.one_left n)

/--
@isnad1 id=commute.0h4v.s7.05e5f0542286 from=seed src=0 shape=afd29cd5 vocab=78c38ebd
-/
@[to_additive]
theorem commute_inlₗ_inrₗ (m : α) (n : β) : Commute (inlₗ α β m) (inrₗ α β n) :=
  Commute.prod (.one_right m) (.one_left n)

end OrderMonoidHom
