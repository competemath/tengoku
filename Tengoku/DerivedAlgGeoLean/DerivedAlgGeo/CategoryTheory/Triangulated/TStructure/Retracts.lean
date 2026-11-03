/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Retracts and canonical boundedness in triangulated categories

This file contains t-structure facts that require no geometric input.  In
particular, the aisle, coaisle, and bounded object properties of an arbitrary
t-structure are stable under retracts.
-/

namespace CategoryTheory

open Limits Pretriangulated Triangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The `≤ n` part of a t-structure is stable under retracts.
@isnad1 id=isle.1h6v.s6.805e5129eee3 from=translated src=- shape=74624c54 vocab=8f5d966a
-/
lemma tStructureIsLE_of_retract (t : TStructure C) {X Y : C} (r : Retract X Y) (n : ℤ)
    (hY : t.IsLE Y n) : t.IsLE X n := by
  rw [t.isLE_iff_orthogonal n (n + 1) rfl]
  intro Z f hZ
  have hzero : r.r ≫ f = 0 := t.zero_of_isLE_of_isGE (r.r ≫ f) n (n + 1)
    (by omega) hY hZ
  rw [← Category.id_comp f, ← r.retract, Category.assoc, hzero, comp_zero]

/-- The `≥ n` part of a t-structure is stable under retracts.
@isnad1 id=isge.1h6v.s6.a8fa19f4d037 from=translated src=- shape=74624c54 vocab=225454e0
-/
lemma tStructureIsGE_of_retract (t : TStructure C) {X Y : C} (r : Retract X Y) (n : ℤ)
    (hY : t.IsGE Y n) : t.IsGE X n := by
  rw [t.isGE_iff_orthogonal (n - 1) n (by omega)]
  intro Z f hZ
  have hzero : f ≫ r.i = 0 := t.zero_of_isLE_of_isGE (f ≫ r.i) (n - 1) n
    (by omega) hZ hY
  rw [← Category.comp_id f, ← r.retract, ← Category.assoc, hzero, zero_comp]

end CategoryTheory
