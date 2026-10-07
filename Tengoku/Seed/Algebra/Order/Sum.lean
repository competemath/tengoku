/-
Copyright (c) 2024 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Notation.Pi.Defs
public import Tengoku.Seed.Order.Basic

/-!
# Interaction between `Sum.elim`, `≤`, and `0` or `1`

This file provides basic API for part-wise comparison of `Sum.elim` vectors against `0` or `1`.
-/

public section

namespace Sum

variable {α₁ α₂ β : Type*} [LE β] [One β] {v₁ : α₁ → β} {v₂ : α₂ → β}

/--
@isnad1 id=iff.0h5v.s7.eae35fff3dd8 from=seed src=0 shape=7fe77a99 vocab=28a701a1
-/
@[to_additive]
lemma one_le_elim_iff : 1 ≤ Sum.elim v₁ v₂ ↔ 1 ≤ v₁ ∧ 1 ≤ v₂ :=
  const_le_elim_iff

/--
@isnad1 id=iff.0h5v.s7.b3bce13cc677 from=seed src=0 shape=f9c85aba vocab=28a701a1
-/
@[to_additive]
lemma elim_le_one_iff : Sum.elim v₁ v₂ ≤ 1 ↔ v₁ ≤ 1 ∧ v₂ ≤ 1 :=
  elim_le_const_iff

end Sum
