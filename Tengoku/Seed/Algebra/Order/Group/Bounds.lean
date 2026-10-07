/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Order.Bounds.Basic
public import Tengoku.Seed.Algebra.Order.Monoid.Defs
public import Tengoku.Seed.Algebra.Order.Group.Unbundled.Basic

/-!
# Least upper bound and the greatest lower bound in linear ordered additive commutative groups
-/

public section

section LinearOrderedAddCommGroup

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {s : Set α} {a ε : α}

/--
@isnad1 id=ex.2h4v.s7.d0d203cca561 from=seed src=0 shape=f41d0f09 vocab=86dc438a
-/
theorem IsGLB.exists_between_self_add (h : IsGLB s a) (hε : 0 < ε) : ∃ b ∈ s, a ≤ b ∧ b < a + ε :=
  h.exists_between <| lt_add_of_pos_right _ hε

/--
@isnad1 id=ex.3h4v.s7.3012acf45f98 from=seed src=0 shape=fca70bef vocab=46427cd2
-/
theorem IsGLB.exists_between_self_add' (h : IsGLB s a) (h₂ : a ∉ s) (hε : 0 < ε) :
    ∃ b ∈ s, a < b ∧ b < a + ε :=
  h.exists_between' h₂ <| lt_add_of_pos_right _ hε

/--
@isnad1 id=ex.2h4v.s7.8ed360d5b4ac from=seed src=0 shape=73f441a9 vocab=c1e6cc6c
-/
theorem IsLUB.exists_between_sub_self (h : IsLUB s a) (hε : 0 < ε) : ∃ b ∈ s, a - ε < b ∧ b ≤ a :=
  h.exists_between <| sub_lt_self _ hε

/--
@isnad1 id=ex.3h4v.s7.b32c31c694c5 from=seed src=0 shape=f8dce132 vocab=740ca77a
-/
theorem IsLUB.exists_between_sub_self' (h : IsLUB s a) (h₂ : a ∉ s) (hε : 0 < ε) :
    ∃ b ∈ s, a - ε < b ∧ b < a :=
  h.exists_between' h₂ <| sub_lt_self _ hε

end LinearOrderedAddCommGroup
