/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.GroupConfig.Rank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Automorphisms and the rank calculus

Blueprint `sources/group_configuration/01-universal-domain.tex`, `lem:equiv`:
every `k`-automorphism of `K` preserves relative algebraic closures, ranks and
independence. (`lem:conj` is `AclGeom.exists_ambientAutomorphism_of_idealOf_eq`.)
The algebraic-to-finite direction of `lem:orbit` is `GroupConfig.finite_conjugates`
in `GroupConfig.ConjugateSet`. Its converse and the transcendental orbit
characterization are proved in `GroupConfig.OrbitFiniteness`.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** matroids, ranks and independence are invariant under base-field
automorphisms (`lem:equiv`). The full orbit characterization is in
`GroupConfig.OrbitFiniteness`; group-of-germs extraction is in `GroupConfig.Main`.
-/

namespace GroupConfig

open AclGeom IntermediateField Matroid Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The image of the matroid over `C` under a `k`-automorphism is the matroid over the
image of `C`.-/
theorem rkMatroid_image (σ : K ≃ₐ[k] K) (C : Set K) :
    rkMatroid k (σ '' C) = (rkMatroid k C).map σ σ.injective.injOn := by
  refine Matroid.ext_closure fun X ↦ ?_
  rw [map_closure_eq, rkMatroid_closure_eq, rkMatroid_closure_eq]
  calc (racl k (σ '' C ∪ X) : Set K) = racl k (σ '' (C ∪ σ ⁻¹' X)) := by
        rw [image_union, image_preimage_eq X σ.surjective]
    _ = ((racl k (C ∪ σ ⁻¹' X)).map σ.toAlgHom : Set K) := by rw [racl_map]
    _ = σ '' (racl k (C ∪ σ ⁻¹' X) : Set K) := by
        rw [IntermediateField.coe_map]
        rfl

/-- `lem:equiv`: automorphisms preserve ranks.-/
theorem erk_image (σ : K ≃ₐ[k] K) (C X : Set K) :
    erk k (σ '' C) (σ '' X) = erk k C X := by
  unfold erk
  rw [rkMatroid_image]
  exact eRk_map _ _ (subset_univ X)

/-- `lem:equiv`: automorphisms preserve independence.-/
theorem IndepOver.image (σ : K ≃ₐ[k] K) {C A B : Set K} (h : IndepOver k C A B) :
    IndepOver k (σ '' C) (σ '' A) (σ '' B) := by
  intro a' ha' hfin'
  have ha : σ ⁻¹' a' ⊆ A := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := ha' hy
    rwa [← σ.injective hzy]
  have hfin : (σ ⁻¹' a').Finite := hfin'.preimage σ.injective.injOn
  have hrepr : a' = σ '' (σ ⁻¹' a') := (image_preimage_eq a' σ.surjective).symm
  rw [hrepr, ← image_union, erk_image, erk_image]
  exact h ha hfin

theorem indepOver_image_iff (σ : K ≃ₐ[k] K) {C A B : Set K} :
    IndepOver k (σ '' C) (σ '' A) (σ '' B) ↔ IndepOver k C A B := by
  refine ⟨fun h ↦ ?_, IndepOver.image σ⟩
  have h' := h.image σ.symm
  simpa [image_image] using h'

end

end GroupConfig
