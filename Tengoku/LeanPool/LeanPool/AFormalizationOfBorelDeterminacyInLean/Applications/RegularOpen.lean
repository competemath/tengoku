/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module

public import Tengoku

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Applications.RegularOpen

Auxiliary declarations for the Borel determinacy formalization.
-/

@[expose] public section

variable {X : Type*} [tX : TopologicalSpace X] {A B : Set X} {U V : tX.Opens}

namespace TopologicalSpace.Opens
/--
@isnad1 id=iff.0h3v.s5.ac22aed4a5c1 from=translated src=- shape=657e6ab8 vocab=a5421abf
-/
lemma le_def : U ≤ V ↔ (U : Set X) ⊆ V := by simp only [SetLike.coe_subset_coe]
/--
@isnad1 id=eq.0h3v.s6.d9cfa34cbd1e from=translated src=- shape=1740e35a vocab=91c3fecb
-/
@[simp] lemma coe_himp' : U ⇨ V = interior (V ∪ (U : Set X)ᶜ) := by
  suffices U ⇨ V = Opens.interior (V ∪ (U : Set X)ᶜ) by
    simp_all
  apply eq_of_forall_le_iff; intro W
  simp_rw [le_himp_iff, ← SetLike.coe_subset_coe, coe_inf, coe_interior,
    W.isOpen.subset_interior_iff]
  constructor <;> (intro h; tauto_set)
/--
@isnad1 id=eq.0h2v.s5.3d527b81edf4 from=translated src=- shape=6fe93734 vocab=5781a65f
-/
@[simp] lemma coe_compl' : Uᶜ = interior (U : Set X)ᶜ := by rw [← himp_bot, coe_himp']; simp
/--
@isnad1 id=eq.0h2v.s6.10a26232ae08 from=translated src=- shape=711766e9 vocab=fb6b1a4a
-/
lemma coe_compl_compl : ((Uᶜᶜ : tX.Opens) : Set X) = interior (closure U) := by simp
/--
@isnad1 id=iff.0h2v.s5.dc5bbf830e96 from=translated src=- shape=aa8ea6fa vocab=516a073a
-/
lemma isRegular_iff : Heyting.IsRegular U ↔ interior (closure U) = (U : Set X) := by
  simp [Heyting.IsRegular, Opens.ext_iff]
end TopologicalSpace.Opens
open TopologicalSpace

/--
@isnad1 id=eq.0h2v.s4.68dde5a0d220 from=translated src=- shape=d1e99066 vocab=24bb4ed5
-/
lemma interior_closure_interior_closure_eq_interior_closure :
  interior (closure (interior (closure A))) = interior (closure A) :=
  subset_antisymm (interior_mono (isClosed_closure.closure_interior_subset))
    isOpen_interior.subset_interior_closure
/--
@isnad1 id=isregula.1h2v.s5.827ee1e59360 from=translated src=- shape=0e55d25a vocab=b786b955
-/
lemma IsClosed.interior_isRegular (hA : IsClosed A) : Heyting.IsRegular (Opens.interior A) := by
  rw [Opens.isRegular_iff, ← hA.closure_eq, Opens.coe_interior,
    interior_closure_interior_closure_eq_interior_closure]
