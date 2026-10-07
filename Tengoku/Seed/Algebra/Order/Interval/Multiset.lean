/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.Interval.Finset.Basic
public import Tengoku.Seed.Order.Interval.Multiset

/-!
# Algebraic properties of multiset intervals

This file provides results about the interaction of algebra with `Multiset.Ixx`.
-/

public section

variable {α : Type*}

namespace Multiset
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  [ExistsAddOfLE α] [LocallyFiniteOrder α]

/--
@isnad1 id=eq.0h4v.s6.574109ac60e4 from=seed src=0 shape=ce10642a vocab=4b4460b2
-/
lemma map_add_left_Icc (a b c : α) : (Icc a b).map (c + ·) = Icc (c + a) (c + b) := by
  classical rw [Icc, Icc, ← Finset.image_add_left_Icc, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

/--
@isnad1 id=eq.0h4v.s6.a1886b11a807 from=seed src=0 shape=ce10642a vocab=fa57ac80
-/
lemma map_add_left_Ico (a b c : α) : (Ico a b).map (c + ·) = Ico (c + a) (c + b) := by
  classical rw [Ico, Ico, ← Finset.image_add_left_Ico, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

/--
@isnad1 id=eq.0h4v.s6.662f8eafc9a9 from=seed src=0 shape=ce10642a vocab=a997fe4a
-/
lemma map_add_left_Ioc (a b c : α) : (Ioc a b).map (c + ·) = Ioc (c + a) (c + b) := by
  classical rw [Ioc, Ioc, ← Finset.image_add_left_Ioc, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

/--
@isnad1 id=eq.0h4v.s6.7d6b1fb22137 from=seed src=0 shape=ce10642a vocab=31dabc47
-/
lemma map_add_left_Ioo (a b c : α) : (Ioo a b).map (c + ·) = Ioo (c + a) (c + b) := by
  classical rw [Ioo, Ioo, ← Finset.image_add_left_Ioo, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

/--
@isnad1 id=eq.0h4v.s6.9d8f4ab23c15 from=seed src=0 shape=617c7480 vocab=4b4460b2
-/
lemma map_add_right_Icc (a b c : α) : ((Icc a b).map fun x => x + c) = Icc (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact map_add_left_Icc _ _ _

/--
@isnad1 id=eq.0h4v.s6.8d38c79f8c1a from=seed src=0 shape=617c7480 vocab=fa57ac80
-/
lemma map_add_right_Ico (a b c : α) : ((Ico a b).map fun x => x + c) = Ico (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact map_add_left_Ico _ _ _

/--
@isnad1 id=eq.0h4v.s6.941b2209ccf7 from=seed src=0 shape=617c7480 vocab=a997fe4a
-/
lemma map_add_right_Ioc (a b c : α) : ((Ioc a b).map fun x => x + c) = Ioc (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact map_add_left_Ioc _ _ _

/--
@isnad1 id=eq.0h4v.s6.43c17f945df6 from=seed src=0 shape=617c7480 vocab=31dabc47
-/
lemma map_add_right_Ioo (a b c : α) : ((Ioo a b).map fun x => x + c) = Ioo (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact map_add_left_Ioo _ _ _

end Multiset
