/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.AclGeom.Correspondence.ProperCurveExtension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Automorphisms extend from an open to a proper normal curve

**Status:** proved over every field. An actual morphism from a nonempty open of a normal
integral locally Noetherian curve to a proper target extends uniquely. Every automorphism of
that open extends uniquely to an automorphism of the entire proper normal curve, with the
literal commuting square; both inverse identities are internal. In the proper-over-field
consumer, Noetherianity is derived. This proves individual translation/automorphism extension
in source Lemma 8.4.

For a given actual proper normal integral dimension-one curve, the closed-point/place
identification is now proved by CurvePointsPlaces.exists_point_place_model, including actual
stalk ring equivalences and automorphism compatibility. The given proper normal curve is an
actual input. Projective presentation, joint regularity of extended families, rational-action
regularization and the full original classifier remain owed, alongside group/chunk/six-point
statements, algebraization/descent and every true bypassed auxiliary. All eight original #21
work items and the full durable goal remain active and incomplete.

For actual smooth integral dimension-one curves over an ACF base, SmoothCurveStalks now
derives integral closedness of every actual stalk and DVRs at closed points internally; its
actual connected-group and individual proper-smooth extension consumers have no normality
premise.

CurveCompletion now constructs the actual proper-normal dimension-one model and the ORIGINAL
smooth separated ACF curve's open embedding internally. Its actual connected-group consumer
derives smoothness and extends every original-group scheme automorphism uniquely. Projective
presentation and jointly regular extended families remain separate obligations (#21).
-/

namespace AclGeom.ProperCurve
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {k : Type u} [Field k]

/-- A map from a nonempty open of a normal curve to a proper target extends uniquely.
The open comparison is an actual open immersion, not a supplied extension certificate.
Named consumer: extending the automorphisms of the original group curve to its completion.-/
theorem existsUnique_morphism_extension_from_open
    (X Y U : Over (Spec (.of k))) [IsIntegral X.left] [IsLocallyNoetherian X.left]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (hnormal : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    [IsProper Y.hom] [Nonempty U.left]
    (j : U ⟶ X) [IsOpenImmersion j.left] (a : U ⟶ Y) :
    ∃! F : X ⟶ Y, j ≫ F = a := by
  have : Y.left.IsSeparated := by
    constructor
    rw [← Limits.terminal.comp_from Y.hom]
    infer_instance
  have hdense : Dense (j.left.opensRange : Set X.left) :=
    j.left.opensRange.2.dense (Set.range_nonempty j.left)
  have : IsDominant j.left := ⟨hdense⟩
  let p : X.left.PartialMap Y.left :=
    { domain := j.left.opensRange
      dense_domain := hdense
      hom := j.left.isoOpensRange.inv ≫ a.left }
  have hpbase : p.hom ≫ Y.hom = p.domain.ι ≫ X.hom := by
    dsimp only [p]
    rw [Category.assoc, Over.w a, ← Over.w j, ← Category.assoc,
      Scheme.Hom.isoOpensRange_inv_comp]
  have hpfield : p.fromFunctionField ≫ Y.hom =
      X.left.fromSpecStalk (genericPoint X.left) ≫ X.hom := by
    dsimp only [Scheme.PartialMap.fromFunctionField,
      Scheme.PartialMap.fromSpecStalkOfMem]
    rw [Category.assoc, hpbase, ← Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι]
  let r := Scheme.RationalMap.ofFunctionField X.hom Y.hom p.fromFunctionField hpfield
  have hr : r = p.toRationalMap := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    exact Scheme.RationalMap.fromFunctionField_ofFunctionField _ _ _ _
  have hrbase : r.compHom Y.hom = X.hom.toRationalMap :=
    ((Scheme.RationalMap.equivFunctionField X.hom Y.hom)
      ⟨p.fromFunctionField, hpfield⟩).property
  obtain ⟨F, ⟨hFr, hFbase⟩, _⟩ :=
    existsUnique_extension hdim hnormal X.hom Y.hom r hrbase
  have hF : F.toRationalMap = p.toRationalMap := hFr.trans hr
  have hpF : p.hom = p.domain.ι ≫ F :=
    (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp hF.symm)
  let F' : X ⟶ Y := Over.homMk F hFbase
  have hjF : j ≫ F' = a := by
    apply Over.OverMorphism.ext
    change j.left ≫ F = a.left
    rw [← j.left.isoOpensRange_hom_ι, Category.assoc, ← hpF]
    dsimp only [p]
    rw [Iso.hom_inv_id_assoc]
  refine ⟨F', hjF, ?_⟩
  intro q hq
  apply Over.OverMorphism.ext
  apply ext_of_isDominant j.left
  exact congrArg Over.Hom.left (hq.trans hjF.symm)

/-- Every automorphism of a nonempty open in a proper normal integral curve extends
uniquely to an automorphism of the whole curve. This is the individual extension assertion
in the source proof of `lem:affine-action`; neither a completion nor joint regularity of a
family is asserted. All global maps and inverse identities are constructed internally.-/
theorem existsUnique_iso_extension
    (X U : Over (Spec (.of k))) [IsIntegral X.left]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (hnormal : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    [IsProper X.hom] [Nonempty U.left]
    (j : U ⟶ X) [IsOpenImmersion j.left] (a : U ≅ U) :
    ∃! F : X ≅ X, j ≫ F.hom = a.hom ≫ j := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : X.left.IsSeparated := by
    constructor
    rw [← Limits.terminal.comp_from X.hom]
    infer_instance
  have hdense : Dense (j.left.opensRange : Set X.left) :=
    j.left.opensRange.2.dense (Set.range_nonempty j.left)
  have : IsDominant j.left := ⟨hdense⟩
  obtain ⟨F, hF, _⟩ :=
    existsUnique_morphism_extension_from_open X X U hdim hnormal j (a.hom ≫ j)
  obtain ⟨H, hH, _⟩ :=
    existsUnique_morphism_extension_from_open X X U hdim hnormal j (a.inv ≫ j)
  have hFH : F ≫ H = 𝟙 X := by
    apply Over.OverMorphism.ext
    apply ext_of_isDominant j.left
    have h : j ≫ F ≫ H = j := by
      rw [← Category.assoc, hF, Category.assoc, hH, Iso.hom_inv_id_assoc]
    simpa only [Over.comp_left, Over.id_left, Category.comp_id] using
      congrArg Over.Hom.left h
  have hHF : H ≫ F = 𝟙 X := by
    apply Over.OverMorphism.ext
    apply ext_of_isDominant j.left
    have h : j ≫ H ≫ F = j := by
      rw [← Category.assoc, hH, Category.assoc, hF, Iso.inv_hom_id_assoc]
    simpa only [Over.comp_left, Over.id_left, Category.comp_id] using
      congrArg Over.Hom.left h
  let e : X ≅ X := { hom := F, inv := H, hom_inv_id := hFH, inv_hom_id := hHF }
  refine ⟨e, hF, ?_⟩
  intro d hd
  apply Iso.ext
  apply Over.OverMorphism.ext
  apply ext_of_isDominant j.left
  exact congrArg Over.Hom.left (hd.trans hF.symm)

end
end AclGeom.ProperCurve
