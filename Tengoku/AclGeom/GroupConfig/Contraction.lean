/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.GroupConfig.FieldOfDefinition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extension and contraction of ideals: dropping variables

Blueprint `sources/group_configuration/01-universal-domain.tex`, `lem:extcontr`(2).

For a field extension `M ⊆ K`, the polynomial ring `K[Y]` sits inside `K[Y, Z]` via
`MvPolynomial.rename Sum.inl`.  Contracting an ideal of `K[Y, Z]` extended from `M[Y, Z]`
to `K[Y]` gives the extension of the contraction (`comap_rename_map_eq`): an ideal of
`K[Y, Z]` defined over `M` contracts to an ideal of `K[Y]` defined over `M`.  The proof
decomposes a polynomial of `K[Y]` along an `M`-basis of `K` (`sum_smul_map_coordPoly`)
and uses that the coefficient projections commute with renaming (`coordPoly_rename`).
(`lem:extcontr`(1) is `AclGeom.comap_map_mvPolynomial_eq_self`.)

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** coefficient projections commute with injective variable renaming,
and extension/contraction commute along any injective renaming. These results
hold for arbitrary field extensions and coordinate types. Named consumer:
projection of locus ideals in `GroupConfig.Germ.Graph`.
-/

namespace GroupConfig

open Module MvPolynomial Set

noncomputable section

variable {K : Type*} [Field K] {R : Type*} [CommRing R] [Algebra R K] {ι κ : Type*}

/-- Coefficient projections commute with renaming variables along an injection.-/
theorem coordPoly_rename (l : K →ₗ[R] R) {f : ι → κ} (hf : Function.Injective f)
    (p : MvPolynomial ι K) : coordPoly l (rename f p) = rename f (coordPoly l p) := by
  refine MvPolynomial.ext _ _ fun d ↦ ?_
  rw [coeff_coordPoly]
  by_cases hd : ∃ u : ι →₀ ℕ, u.mapDomain f = d
  · obtain ⟨u, rfl⟩ := hd
    rw [coeff_rename_mapDomain _ hf, coeff_rename_mapDomain _ hf, coeff_coordPoly]
  · push Not at hd
    have h1 : (rename f p).coeff d = 0 := by
      by_contra h
      obtain ⟨u, hu, -⟩ := coeff_rename_ne_zero _ _ _ h
      exact hd u hu
    have h2 : (rename f (coordPoly l p)).coeff d = 0 := by
      by_contra h
      obtain ⟨u, hu, -⟩ := coeff_rename_ne_zero _ _ _ h
      exact hd u hu
    rw [h1, h2, map_zero]

variable (M : Type*) [Field M] [Algebra M K]

/-- `lem:extcontr`(2): contracting along an injective renaming of variables an ideal extended
from `M` gives the extension of the contraction (for `Sum.inl : ι → ι ⊕ κ`: an ideal of
`K[Y, Z]` defined over `M` contracts to an ideal of `K[Y]` defined over `M`).-/
theorem comap_rename_map_eq {ι₁ ι₂ : Type*} {f : ι₁ → ι₂} (hf : Function.Injective f)
    (J : Ideal (MvPolynomial ι₂ M)) :
    (J.map (MvPolynomial.map (algebraMap M K))).comap
        (rename f : MvPolynomial ι₁ K →ₐ[K] MvPolynomial ι₂ K) =
      (J.comap (rename f : MvPolynomial ι₁ M →ₐ[M] MvPolynomial ι₂ M)).map
        (MvPolynomial.map (algebraMap M K)) := by
  classical
  refine le_antisymm ?_ ?_
  · intro g hg
    rw [Ideal.mem_comap] at hg
    -- Decompose `g` along an `M`-basis of `K`; each component contracts into `J`.
    let b := Basis.ofVectorSpace M K
    rw [← sum_smul_map_coordPoly b g]
    refine Submodule.sum_mem _ fun j _ ↦ Submodule.smul_of_tower_mem _ (b j) ?_
    refine Ideal.mem_map_of_mem _ ?_
    rw [Ideal.mem_comap, ← coordPoly_rename _ hf]
    exact coordPoly_mem_of_mem_map _ hg
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap] at hg
    rw [Ideal.mem_comap, Ideal.mem_comap, ← map_rename]
    exact Ideal.mem_map_of_mem _ hg

end

end GroupConfig
