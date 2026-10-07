/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.FreeMonoid.Basic
public import Tengoku.Seed.Algebra.Free
public import Tengoku.Seed.Algebra.Group.WithOne.Basic
public import Tengoku.Seed.Algebra.Group.Units.Basic
public import Tengoku.Seed.Data.Set.Operations

import Tengoku.Seed.Data.Set.Insert

/-!
# Relation between the free semigroup and the free monoid

We provide some constructions relating the free semigroup and the free monoid on the same type.

## Main definitions
* `FreeSemigroup.toFreeMonoid`: the natural embedding of the free semigroup into the free monoid.
* `FreeMonoid.equivWithOneFreeSemigroup`: the free monoid is isomorphic to the free semigroup
  with a `1` added.
-/

public section

variable {α : Type*}

namespace FreeSemigroup

open FreeMonoid

/--
The natural embedding of the free semigroup into the free monoid.
This is injective (`FreeSemigroup.toFreeMonoid_injective`), and its image
consists of all non-`1` elements of the free monoid (`FreeSemigroup.eq_one_or_toFreeMonoid`).
-/
@[expose, to_additive /-- The natural embedding of the free additive semigroup into the
free additive monoid. This is injective (`FreeAddSemigroup.toFreeAddMonoid_injective`), and its
image consists of all non-`0` elements of the free additive monoid
(`FreeAddSemigroup.eq_zero_or_toFreeAddMonoid`). -/]
def toFreeMonoid : FreeSemigroup α →ₙ* FreeMonoid α :=
  lift FreeMonoid.of

/--
@isnad1 id=eq.0h2v.s6.2dfcf47cfbed from=seed src=0 shape=0ddbd884 vocab=c28bf843
-/
@[to_additive (attr := simp, grind =)]
lemma toFreeMonoid_of (x : α) : toFreeMonoid (.of x) = .of x := rfl

/--
@isnad1 id=eq.0h3v.s6.3129c7269ce9 from=seed src=0 shape=6f5e8b9c vocab=84c7c4ee
-/
@[to_additive]
lemma toFreeMonoid_mk_eq_cons (x : α) (xs : List α) :
    toFreeMonoid ⟨x, xs⟩ = FreeMonoid.ofList (x :: xs) := by
  suffices ∀ x : FreeMonoid α, (xs.map FreeMonoid.of).foldl (· * ·) x = x * ofList xs by
    simpa [← List.foldl_map, lift_mk_eq_foldl, toFreeMonoid, lift] using this (FreeMonoid.of x)
  induction xs with grind [ofList_nil, ofList_cons]

/--
@isnad1 id=injectiv.0h1v.s6.621bfe765fb7 from=seed src=0 shape=bfe13a5f vocab=7ee0b631
-/
@[to_additive (attr := grind .)]
lemma toFreeMonoid_injective : Function.Injective (@toFreeMonoid α) := by
  rintro ⟨x, xs⟩ ⟨y, ys⟩ h
  simp only [toFreeMonoid_mk_eq_cons, Equiv.apply_eq_iff_eq] at h
  simpa using h

/--
@isnad1 id=ne.0h2v.s6.60fb790c4fad from=seed src=0 shape=a74634b0 vocab=a6077981
-/
@[to_additive (attr := simp, grind .)]
lemma toFreeMonoid_ne_one (x : FreeSemigroup α) : toFreeMonoid x ≠ 1 := by
  induction x with simp

@[to_additive]
lemma eq_one_or_toFreeMonoid (x : FreeMonoid α) : x = 1 ∨ ∃ y, toFreeMonoid y = x :=
  x.inductionOn' (by simp) <| by
    rintro b _ (rfl | ⟨y, rfl⟩)
    · exact Or.inr ⟨of b, by simp⟩
    · exact Or.inr ⟨of b * y, by simp⟩

/--
@isnad1 id=eq.0h1v.s6.fd210da4a9c0 from=seed src=0 shape=88e2048e vocab=f67cd9bf
-/
@[to_additive (attr := simp)]
lemma range_toFreeMonoid : Set.range (@toFreeMonoid α) = {1}ᶜ := by
  ext x; grind [eq_one_or_toFreeMonoid x]

end FreeSemigroup

open FreeSemigroup FreeMonoid WithOne

/--
The free monoid on `α` is isomorphic to the free semigroup on `α` with a `1` added.
-/
@[expose, to_additive (attr := simps) /-- The free additive monoid on `α` is isomorphic to
the free additive semigroup on `α` with a `0` added. -/]
def FreeMonoid.equivWithOneFreeSemigroup : FreeMonoid α ≃* WithOne (FreeSemigroup α) where
  toFun := lift fun x ↦ ↑(FreeSemigroup.of x)
  invFun := WithOne.lift toFreeMonoid
  left_inv x := by induction x with simp [*]
  right_inv x := by
    induction x with
    | one => simp
    | coe a => induction a with simp_all
  map_mul' := by simp
