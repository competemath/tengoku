/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module

public import Tengoku

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Applications.General

Auxiliary declarations for the Borel determinacy formalization.
-/

@[expose] public section

/--
@isnad1 id=le.0h4v.s5.a525c3cbb28d from=translated src=- shape=a6308c42 vocab=ec2b17ec
-/
lemma diff_subset_union {I} {A B C : Set I} : A \ C ⊆ (A \ B) ∪ (B \ C) := by tauto_set
/--
@isnad1 id=iff.0h5v.s6.e58e65163f63 from=translated src=- shape=8e6d72ed vocab=611f1d95
-/
lemma projection_formula {α β} (f : α → β) (X : Set α) (Y : Set β) :
  Disjoint X (f⁻¹' Y) ↔ Disjoint (f '' X) Y := by --exists?
  constructor <;> intro h
  · rw [Set.disjoint_iff] at *; rintro _ ⟨⟨x, hx, rfl⟩, hy⟩; exact h ⟨hx, hy⟩
  · exact Set.disjoint_of_subset_left (Set.subset_preimage_image f X) (h.preimage f)

namespace Filter
variable {α β γ : Type*} {s t : Set α} {l : Filter α}
end Filter
