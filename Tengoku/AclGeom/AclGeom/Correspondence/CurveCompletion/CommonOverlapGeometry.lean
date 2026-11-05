/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.AclGeom.Correspondence.WeilGluing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Common Overlap Geometry

**Status:** proved, with a named consumer in the actual curve-completion construction.
These lemmas reach CurveCompletion.connectedGroup_completion_and_extensions: an actual
one-dimensional connected algebraic group over an ACF base embeds openly in a constructed
proper normal integral dimension-one curve, and its individual automorphisms extend uniquely.
The original smooth separated curve is retained. Projectivity, jointly regular extended
families and the full rational/non-affine classifier remain separate source obligations.
The source of truth is `sources/blueprint.tex`, Lemma `affine-action` (#21).
-/

namespace AclGeom.WeilGluing
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {J : Type u} (U : J → Scheme.{u}) (W : Scheme.{u})
  (f : ∀ i, W ⟶ U i) [∀ i, IsOpenImmersion (f i)]

/-- The literal common-overlap maps have equal composites into the actual gluing. Named consumer:
overlap_glue_condition.-/
theorem commonOverlap_glue_condition (i j : J) (hij : i ≠ j) :
    f i ≫ (commonOverlapGlueData U W f).ι i =
      f j ≫ (commonOverlapGlueData U W f).ι j := by
  let D := commonOverlapGlueData U W f
  have hv : D.V (i, j) = W := by
    simp only [D, commonOverlapGlueData, CategoryTheory.GlueData.ofGlueData',
      commonOverlapGlueData', hij, ↓reduceDIte]
  let q := eqToHom hv.symm
  have h := congrArg (fun p ↦ q ≫ p) (D.glue_condition i j)
  dsimp only [q] at h
  simp only [D, commonOverlapGlueData, CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f', commonOverlapGlueData', hij, hij.symm,
    ↓reduceDIte, ← Category.assoc, Category.id_comp] at h
  erw [eqToHom_trans (C := Scheme.{u})] at h
  simpa only [commonOverlapGlueData, CategoryTheory.GlueData.ofGlueData',
    commonOverlapGlueData', eqToHom_trans (C := Scheme.{u}),
    eqToHom_refl, Category.id_comp] using h.symm

set_option backward.isDefEq.respectTransparency false in
-- Match the strict atlas endpoints while transporting its actual pullback cone.
/-- The literal common overlap is the actual pullback of two distinct chart inclusions into the
gluing. Named consumer: overlap_isPullback.-/
theorem commonOverlap_isPullback (i j : J) (hij : i ≠ j) :
    IsPullback (f i) (f j) ((commonOverlapGlueData U W f).ι i)
      ((commonOverlapGlueData U W f).ι j) := by
  let D := commonOverlapGlueData U W f
  have hv : D.V (i, j) = W := by
    simp only [D, commonOverlapGlueData, CategoryTheory.GlueData.ofGlueData',
      commonOverlapGlueData', hij, ↓reduceDIte]
  have H : IsPullback (D.f i j) (D.t i j ≫ D.f j i) (D.ι i) (D.ι j) :=
    { w := (D.glue_condition i j).symm
      isLimit' := ⟨D.vPullbackConeIsLimit i j⟩ }
  refine H.of_iso (eqToIso hv) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    (by simp [D]) (by simp [D])
  · simp only [Iso.refl_hom, Category.comp_id, eqToIso.hom,
      D, commonOverlapGlueData, CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f', commonOverlapGlueData', hij, ↓reduceDIte]
  · simp only [Iso.refl_hom, Category.comp_id, eqToIso.hom,
      D, commonOverlapGlueData, CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f', commonOverlapGlueData', hij, hij.symm,
      ↓reduceDIte, ← Category.assoc, Category.comp_id, Category.id_comp]
    erw [eqToHom_trans (C := Scheme.{u}), eqToHom_trans (C := Scheme.{u})]

end
end AclGeom.WeilGluing
