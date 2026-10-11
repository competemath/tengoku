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

lemma diff_subset_union {I} {A B C : Set I} : A \ C ⊆ (A \ B) ∪ (B \ C) := by tauto_set
lemma projection_formula {α β} (f : α → β) (X : Set α) (Y : Set β) :
  Disjoint X (f⁻¹' Y) ↔ Disjoint (f '' X) Y := by --exists?
  constructor <;> intro h
  · rw [Set.disjoint_iff] at *; rintro _ ⟨⟨x, hx, rfl⟩, hy⟩; exact h ⟨hx, hy⟩
  · exact Set.disjoint_of_subset_left (Set.subset_preimage_image f X) (h.preimage f)

namespace Filter
variable {α β γ : Type*} {s t : Set α} {l : Filter α}
end Filter
