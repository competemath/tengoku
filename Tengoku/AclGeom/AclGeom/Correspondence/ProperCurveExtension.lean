/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.AclGeom.Correspondence.NormalCurveStalks
import Tengoku.Seed.AlgebraicGeometry.ValuativeCriterion
import Tengoku.Seed.AlgebraicGeometry.Birational.RationalMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unique extension of rational maps from normal curves

**Status:** proved from actual local normality, local Noetherianity, dimension at most one and
properness of the target over a separated base. Properness extends the generic map over every
stalk via the valuative criterion. Stalk spreading-out fills every point of the rational-map
domain; separatedness gives uniqueness. No valuation-ring or extension certificate is a caller
premise. Named consumers: actual open-automorphism extension and birational isomorphisms of
proper normal curves in source Lemma 8.4.

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

/-- Equality of rational maps reflects equality of morphisms into separated schemes.
Named consumer: uniqueness of the extension to a proper curve.
@isnad1 id=eq.1h4v.s5.e2f6b1ecd1ee from=translated src=- shape=893813e3 vocab=f42c13dd
-/
theorem hom_eq_of_toRationalMap_eq
    {X Y : Scheme.{u}} [IsReduced X] [Y.IsSeparated]
    (f g : X ⟶ Y) (h : f.toRationalMap = g.toRationalMap) : f = g := by
  apply (cancel_epi X.topIso.hom).mp
  exact (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated
    (S := ⊤_ Scheme)).mp (Scheme.PartialMap.toRationalMap_eq_iff.mp h)

/-- A rational map from a normal integral locally Noetherian curve to a proper target
has no missing point in its domain. Normality is the actual integral closedness of stalks.
Named consumer: the unique global extension and the proper-curve function-field theorem.
@isnad1 id=eq.3h6v.s7.4e29af9ce6e2 from=translated src=- shape=edb6448a vocab=244b7918
-/
theorem domain_eq_top
    {X Y S : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (f : X.RationalMap Y) (hf : f.compHom sY = sX.toRationalMap) :
    f.domain = ⊤ := by
  apply top_unique
  intro x _
  have := hnormal x
  have hD : IsDomain (X.presheaf.stalk x) := inferInstance
  have hV : ValuationRing (X.presheaf.stalk x) := stalk_valuationRing X hdim x
  have hstalk : Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ X.fromSpecStalk x =
      X.fromSpecStalk (genericPoint X) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)
  have hgeneric : f.fromFunctionField ≫ sY =
      X.fromSpecStalk (genericPoint X) ≫ sX :=
    ((Scheme.RationalMap.equivFunctionField sX sY).symm ⟨f, hf⟩).property
  let sq : ValuativeCommSq sY :=
    { R := X.presheaf.stalk x
      domain := hD
      valuationRing := hV
      K := X.functionField
      i₁ := f.fromFunctionField
      i₂ := X.fromSpecStalk x ≫ sX
      commSq := ⟨hgeneric.trans ((congrArg (fun q ↦ q ≫ sX) hstalk).symm.trans
        (Category.assoc _ _ _))⟩ }
  have hproper : IsProper sY := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hproper
  obtain ⟨l, hl₁, hl₂⟩ := (hproper.1.1.1.existence sq).exists_lift
  dsimp only [sq] at hl₁ hl₂
  let g := Scheme.PartialMap.ofFromSpecStalk sX sY l hl₂
  have hx : x ∈ g.domain :=
    Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY l hl₂
  have hgx : g.fromSpecStalkOfMem hx = l :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY l hl₂
  have hη : genericPoint X ∈ g.domain :=
    (genericPoint_specializes x).mem_open g.domain.2 hx
  have hfac : Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
      g.domain.fromSpecStalkOfMem x hx =
      g.domain.fromSpecStalkOfMem (genericPoint X) hη := by
    apply (cancel_mono g.domain.ι).mp
    rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι]
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)
  have hg : g.toRationalMap = f := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [Scheme.RationalMap.fromFunctionField_toRationalMap]
    change g.domain.fromSpecStalkOfMem (genericPoint X) hη ≫ g.hom = _
    rw [← hfac, Category.assoc]
    change _ ≫ g.fromSpecStalkOfMem hx = _
    rw [hgx]
    exact hl₁
  exact Scheme.RationalMap.mem_domain.mpr ⟨g, hx, hg⟩

/-- Every rational map from a normal integral locally Noetherian curve to a proper target
extends uniquely over the whole source. All extension data are constructed internally.
Named consumer: the proper-normal-curve function-field isomorphism theorem.
@isnad1 id=existsun.3h6v.s7.d25d70ed93d8 from=translated src=- shape=e8dcf54d vocab=f33bda30
-/
theorem existsUnique_extension
    {X Y S : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [S.IsSeparated]
    (hdim : topologicalKrullDim X ≤ 1)
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (f : X.RationalMap Y) (hf : f.compHom sY = sX.toRationalMap) :
    ∃! g : X ⟶ Y, g.toRationalMap = f ∧ g ≫ sY = sX := by
  have : Y.IsSeparated := by
    constructor
    rw [← Limits.terminal.comp_from sY]
    infer_instance
  let p := f.toPartialMap
  have hp : p.domain = ⊤ := domain_eq_top hdim hnormal sX sY f hf
  let j : X ⟶ p.domain.toScheme := X.topIso.inv ≫ (X.isoOfEq hp).inv
  have hj : j ≫ p.domain.ι = 𝟙 X := by
    dsimp only [j]
    rw [Category.assoc, Scheme.isoOfEq_inv_ι, Scheme.toIso_inv_ι]
  have hij : p.domain.ι ≫ j = 𝟙 _ := by
    apply (cancel_mono p.domain.ι).mp
    rw [Category.assoc, hj, Category.comp_id, Category.id_comp]
  let g := j ≫ p.hom
  have hpg : p.hom = p.domain.ι ≫ g := by
    dsimp only [g]
    rw [← Category.assoc, hij, Category.id_comp]
  have hg : g.toRationalMap = f := by
    rw [← f.toRationalMap_toPartialMap]
    exact (Scheme.PartialMap.toRationalMap_eq_iff.mpr
      ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated
        (S := ⊤_ Scheme)).mpr hpg)).symm
  refine ⟨g, ⟨hg, ?_⟩, fun q hq ↦ hom_eq_of_toRationalMap_eq q g (hq.1.trans hg.symm)⟩
  apply hom_eq_of_toRationalMap_eq
  change (g ≫ sY).toPartialMap.toRationalMap = _
  rw [← Scheme.Hom.toPartialMap_compHom,
    Scheme.RationalMap.compHom_toRationalMap]
  change g.toRationalMap.compHom sY = sX.toRationalMap
  rw [hg]
  exact hf

end
end AclGeom.ProperCurve
