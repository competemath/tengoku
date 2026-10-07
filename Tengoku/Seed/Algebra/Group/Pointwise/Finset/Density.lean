/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Pointwise.Finset.Scalar
public import Tengoku.Seed.Algebra.Group.Action.Pointwise.Finset
public import Tengoku.Seed.Algebra.Group.Action.Defs
public import Tengoku.Seed.Data.Finset.Density

/-!
# Theorems about the density of pointwise operations on finsets.
-/

public section

open scoped Pointwise

variable {α β : Type*}

namespace Finset

variable [DecidableEq α] [InvolutiveInv α] {s : Finset α} {a : α} in
/--
@isnad1 id=eq.0h2v.s5.e258954878e4 from=seed src=0 shape=109e8c87 vocab=b25429eb
-/
@[to_additive (attr := simp)]
lemma dens_inv [Fintype α] (s : Finset α) : s⁻¹.dens = s.dens := by simp [dens]

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β} in
/--
@isnad1 id=eq.0h4v.s6.eb160341c913 from=seed src=0 shape=217d41b4 vocab=f9fd4694
-/
@[to_additive (attr := simp)]
lemma dens_smul_finset [Fintype β] (a : α) (s : Finset β) : (a • s).dens = s.dens := by simp [dens]

end Finset
