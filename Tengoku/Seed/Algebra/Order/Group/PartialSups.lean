/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.Group.OrderIso
public import Tengoku.Seed.Order.PartialSups

/-!
# Results about `partialSups` of functions taking values in a `Group`
-/

public section

variable {α ι : Type*}

variable [SemilatticeSup α] [Group α] [Preorder ι] [LocallyFiniteOrderBot ι]

/--
@isnad1 id=eq.0h5v.s7.ef8f7bb7b782 from=seed src=0 shape=d3f62f0c vocab=4d5b7f7f
-/
@[to_additive]
lemma partialSups_const_mul [MulLeftMono α] (f : ι → α) (c : α) (i : ι) :
    partialSups (c * f ·) i = c * partialSups f i := map_partialSups (OrderIso.mulLeft _) ..

/--
@isnad1 id=eq.0h5v.s7.72d2cd822cc4 from=seed src=0 shape=56f0072d vocab=4f40a94e
-/
@[to_additive]
lemma partialSups_mul_const [MulRightMono α] (f : ι → α) (c : α) (i : ι) :
    partialSups (f · * c) i = partialSups f i * c := map_partialSups (OrderIso.mulRight _) ..
