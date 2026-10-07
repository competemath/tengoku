/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Pointwise.Finset.Basic
public import Tengoku.Seed.Algebra.Group.Pointwise.Finset.Scalar
public import Tengoku.Seed.Algebra.Module.Torsion.Free
public import Tengoku.Seed.Algebra.Ring.Action.Pointwise.Set

/-!
# Pointwise actions on sets in a ring

This file proves properties of pointwise actions on sets in a ring.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

public section

open Module
open scoped Pointwise

variable {R G M : Type*}

namespace Finset
section Semiring
variable [Semiring R] [IsDomain R] [AddCommMonoid M] [DecidableEq M] [Module R M]
  [IsTorsionFree R M] {s : Finset R} {t : Finset M} {r : R}

/--
@isnad1 id=iff.1h4v.s7.b6a11bedc395 from=seed src=0 shape=f4ef0ab8 vocab=ecf2ccc3
-/
lemma zero_mem_smul_finset_iff (hr : r ≠ 0) : 0 ∈ r • t ↔ 0 ∈ t := by
  rw [← mem_coe, coe_smul_finset, Set.zero_mem_smul_set_iff hr, mem_coe]

/--
@isnad1 id=iff.0h4v.s7.90fb1338072c from=seed src=0 shape=af041dc7 vocab=85b733e7
-/
lemma zero_mem_smul_iff : (0 : M) ∈ s • t ↔ 0 ∈ s ∧ t.Nonempty ∨ 0 ∈ t ∧ s.Nonempty := by
  rw [← mem_coe, coe_smul, Set.zero_mem_smul_iff]; rfl

end Semiring

variable [Ring R] [AddCommGroup G] [Module R G] [DecidableEq G] {s : Finset R} {t : Finset G}
  {a : R}

/--
@isnad1 id=eq.0h4v.s7.5ad5fef32b24 from=seed src=0 shape=2bc4a2bb vocab=81c4c0c2
-/
@[simp] lemma neg_smul_finset : -a • t = -(a • t) := by
  simp only [← image_smul, ← image_neg_eq_neg, image_image, neg_smul, Function.comp_def]

/--
@isnad1 id=eq.0h4v.s7.47ad945a3441 from=seed src=0 shape=5a63f91b vocab=43ef425b
-/
@[simp] protected lemma neg_smul [DecidableEq R] : -s • t = -(s • t) := by
  simp_rw [← image_neg_eq_neg]
  exact image₂_image_left_comm neg_smul

end Finset
