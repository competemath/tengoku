/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.Seed.AlgebraicGeometry.Birational.Composition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Function-field equivalences and inverse rational maps

This module develops the generic-point calculus needed to turn an equivalence
of function fields into mutually inverse dominant rational maps.  It records
the field homomorphism induced by a dominant partial map, proves its behavior
under composition, and shows that a function-field equivalence and its inverse
cancel at the level of rational maps.

This module is part of the formalization of the
Evans--Hrushovski--Gismatullin reconstruction theorem; the source of truth
is `sources/blueprint.tex`.
-/

open CategoryTheory
open AlgebraicGeometry
open IsLocalRing
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

noncomputable section

variable {X Y Z : Scheme.{u}}

/--
@isnad1 id=eq.0h3v.s8.c02a171862e9 from=translated src=- shape=173f149c vocab=823c3fe1
-/
lemma map_genericPoint_of_isDominant (f : X ⟶ Y)
    [IrreducibleSpace X] [IrreducibleSpace Y] [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  symm
  apply (genericPoint_spec Y).eq
  rw [← f.denseRange.closure_range]
  simpa only [Set.image_univ] using (genericPoint_spec X).image f.continuous

-- Unfold scheme carriers and generic-stalk aliases while elaborating this proof.
set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h3v.s8.c29ad718547c from=translated src=- shape=f9cf6aa5 vocab=ce964b65
-/
lemma PartialMap.fromFunctionField_closedPoint (f : X.PartialMap Y)
    [IrreducibleSpace X] [IrreducibleSpace Y] [IsDominant f.hom] :
    f.fromFunctionField (closedPoint X.functionField) = genericPoint Y := by
  letI : Nonempty f.domain := f.dense_domain.nonempty.to_subtype
  letI : IrreducibleSpace f.domain :=
    f.domain.ι.isOpenEmbedding.irreducibleSpace
  rw [PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem,
    Scheme.Hom.comp_apply]
  rw [← map_genericPoint_of_isDominant f.hom]
  congr 1
  apply f.domain.ι.isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, Scheme.Opens.fromSpecStalkOfMem_ι,
    Scheme.fromSpecStalk_closedPoint,
    genericPoint_eq_of_isOpenImmersion f.domain.ι]

/-- The map on function fields contravariantly induced by a dominant partial map.-/
noncomputable def PartialMap.functionFieldMap (f : X.PartialMap Y)
    [IrreducibleSpace X] [IrreducibleSpace Y] [IsDominant f.hom] :
    Y.functionField ⟶ X.functionField :=
  (Y.presheaf.stalkCongr (.of_eq f.fromFunctionField_closedPoint.symm)).hom ≫
    Scheme.stalkClosedPointTo f.fromFunctionField

/-- The canonical lift of the source generic point to a partial map's domain.-/
noncomputable def PartialMap.genericLift (f : X.PartialMap Y)
    [IrreducibleSpace X] : Spec X.functionField ⟶ f.domain.toScheme :=
  f.domain.fromSpecStalkOfMem (genericPoint X)
    ((genericPoint_specializes _).mem_open f.domain.2
      f.dense_domain.nonempty.choose_spec)

/--
@isnad1 id=eq.0h3v.s6.51944cb156b4 from=translated src=- shape=0b14ece0 vocab=f0592ddd
-/
@[reassoc]
lemma PartialMap.genericLift_hom (f : X.PartialMap Y)
    [IrreducibleSpace X] : f.genericLift ≫ f.hom = f.fromFunctionField := by
  rfl

/--
@isnad1 id=eq.0h3v.s6.1b1798ca3c47 from=translated src=- shape=58f31c03 vocab=e66a0adf
-/
@[reassoc]
lemma PartialMap.genericLift_ι (f : X.PartialMap Y)
    [IrreducibleSpace X] :
    f.genericLift ≫ f.domain.ι = X.fromSpecStalk (genericPoint X) := by
  exact Scheme.Opens.fromSpecStalkOfMem_ι _ _ _

/-- The lift of a composite partial map to the domain of its second factor.-/
noncomputable def PartialMap.compLift (f : X.PartialMap Y)
    [PreirreducibleSpace X] [Nonempty Y] [IsDominant f.hom]
    (g : Y.PartialMap Z) :
    (f.comp g).domain.toScheme ⟶ g.domain.toScheme := by
  change (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain).toScheme ⟶
    g.domain.toScheme
  exact (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫
    f.hom ∣_ g.domain

/-- The canonical map from a composite domain to the first partial map's domain.-/
noncomputable def PartialMap.compToDomain (f : X.PartialMap Y)
    [PreirreducibleSpace X] [Nonempty Y] [IsDominant f.hom]
    (g : Y.PartialMap Z) :
    (f.comp g).domain.toScheme ⟶ f.domain.toScheme := by
  change (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain).toScheme ⟶
    f.domain.toScheme
  exact (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫
    (f.hom ⁻¹ᵁ g.domain).ι

/--
@isnad1 id=eq.0h5v.s7.7648e9671b16 from=translated src=- shape=989ecb04 vocab=d49333e3
-/
@[reassoc]
lemma PartialMap.compLift_hom (f : X.PartialMap Y)
    [PreirreducibleSpace X] [Nonempty Y] [IsDominant f.hom]
    (g : Y.PartialMap Z) :
    f.compLift g ≫ g.hom = (f.comp g).hom := by
  rfl

/--
@isnad1 id=le.0h5v.s6.d0bd88777c28 from=translated src=- shape=9ec53fcb vocab=3ed65ef2
-/
lemma PartialMap.comp_domain_le (f : X.PartialMap Y)
    [PreirreducibleSpace X] [Nonempty Y] [IsDominant f.hom]
    (g : Y.PartialMap Z) : (f.comp g).domain ≤ f.domain := by
  change f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ g.domain) ≤ f.domain
  exact (Set.image_subset_range _ _).trans_eq Subtype.range_val

/--
@isnad1 id=eq.0h5v.s6.b53afd447010 from=translated src=- shape=5541f56d vocab=49b4c8f6
-/
lemma PartialMap.compToDomain_eq_homOfLE (f : X.PartialMap Y)
    [PreirreducibleSpace X] [Nonempty Y] [IsDominant f.hom]
    (g : Y.PartialMap Z) :
    f.compToDomain g = X.homOfLE (f.comp_domain_le g) := by
  rw [← cancel_mono f.domain.ι]
  change
    (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫
        (f.hom ⁻¹ᵁ g.domain).ι ≫ f.domain.ι =
      X.homOfLE (f.comp_domain_le g) ≫ f.domain.ι
  simp only [Hom.isoImage_inv_ι, homOfLE_ι]
  change (f.comp g).domain.ι = (f.comp g).domain.ι
  rfl

/--
@isnad1 id=eq.0h5v.s7.59c6825e7d66 from=translated src=- shape=1ba3d479 vocab=8a8ff6b5
-/
@[reassoc]
lemma PartialMap.compLift_ι (f : X.PartialMap Y)
    [PreirreducibleSpace X] [Nonempty Y] [IsDominant f.hom]
    (g : Y.PartialMap Z) :
    f.compLift g ≫ g.domain.ι =
      f.compToDomain g ≫ f.hom := by
  change
    (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫
        f.hom ∣_ g.domain ≫ g.domain.ι =
      (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫
        (f.hom ⁻¹ᵁ g.domain).ι ≫ f.hom
  let a := (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv
  exact congrArg (fun q ↦ a ≫ q) (morphismRestrict_ι f.hom g.domain)

/--
@isnad1 id=eq.0h5v.s7.221f29e299fa from=translated src=- shape=27b7594a vocab=baaf7f4f
-/
lemma PartialMap.genericLift_compToDomain_hom (f : X.PartialMap Y)
    [IrreducibleSpace X] [Nonempty Y] [IsDominant f.hom]
    (g : Y.PartialMap Z) :
    (f.comp g).genericLift ≫ f.compToDomain g ≫ f.hom =
      f.fromFunctionField := by
  rw [f.compToDomain_eq_homOfLE g]
  exact f.fromFunctionField_restrict (f.comp g).dense_domain
    (f.comp_domain_le g)

-- Unfold scheme carriers and generic-stalk aliases while elaborating this proof.
set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h5v.s6.e4fc8fc20410 from=translated src=- shape=10c845fb vocab=fb3fcc2c
-/
lemma PartialMap.fromFunctionField_comp (f : X.PartialMap Y)
    [IrreducibleSpace X] [IrreducibleSpace Y] [IsDominant f.hom]
    (g : Y.PartialMap Z) :
    (f.comp g).fromFunctionField =
      Spec.map f.functionFieldMap ≫
        g.fromFunctionField := by
  have hfgeneric :
      f.fromFunctionField (closedPoint X.functionField) = genericPoint Y :=
    f.fromFunctionField_closedPoint
  rw [← (f.comp g).genericLift_hom]
  rw [← f.compLift_hom g]
  rw [← g.genericLift_hom]
  suffices h : (f.comp g).genericLift ≫ f.compLift g =
      Spec.map f.functionFieldMap ≫ g.genericLift by
    simpa only [Category.assoc] using
      congrArg (fun q ↦ q ≫ g.hom) h
  apply (cancel_mono g.domain.ι).mp
  rw [Category.assoc, f.compLift_ι g]
  rw [f.genericLift_compToDomain_hom g]
  dsimp only [PartialMap.functionFieldMap]
  rw [Category.assoc, g.genericLift_ι]
  rw [Spec.map_comp_assoc]
  have ht :
      Spec.map
          (Y.presheaf.stalkCongr (.of_eq hfgeneric.symm)).hom ≫
          Y.fromSpecStalk (genericPoint Y) =
        Y.fromSpecStalk
          (f.fromFunctionField (closedPoint X.functionField)) := by
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk
      (Inseparable.of_eq hfgeneric).specializes
  rw [ht]
  rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

/-- The generic-point morphism contravariantly attached to a function-field equivalence.-/
noncomputable def functionFieldMorphism
    [IrreducibleSpace X] [IrreducibleSpace Y]
    (E : X.functionField ≃+* Y.functionField) :
    Spec X.functionField ⟶ Y :=
  Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫
    Y.fromSpecStalk (genericPoint Y)

-- Unfold scheme carriers and generic-stalk aliases while elaborating this proof.
set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h3v.s8.6f6421b50a22 from=translated src=- shape=0709a563 vocab=aa03b67e
-/
lemma functionFieldMorphism_closedPoint
    [IrreducibleSpace X] [IrreducibleSpace Y]
    (E : X.functionField ≃+* Y.functionField) :
    functionFieldMorphism E (closedPoint X.functionField) = genericPoint Y := by
  letI : IsLocalHom E.symm.toRingHom :=
    .of_surjective _ E.symm.surjective
  rw [functionFieldMorphism, Scheme.Hom.comp_apply, Spec_closedPoint]
  exact Scheme.fromSpecStalk_closedPoint

/-- The field homomorphism contravariantly recovered from a morphism at the generic point.-/
noncomputable def functionFieldMapOfMorphism
    [IrreducibleSpace X] [IrreducibleSpace Y]
    (F : Spec X.functionField ⟶ Y)
    (hF : F (closedPoint X.functionField) = genericPoint Y) :
    Y.functionField ⟶ X.functionField :=
  (Y.presheaf.stalkCongr (.of_eq hF.symm)).hom ≫
    Scheme.stalkClosedPointTo F

/--
@isnad1 id=eq.3h4v.s9.2966a5188d67 from=translated src=- shape=0bc7db3b vocab=eb0ee530
-/
lemma functionFieldMapOfMorphism_congr
    [IrreducibleSpace X] [IrreducibleSpace Y]
    {F G : Spec X.functionField ⟶ Y}
    (hFG : F = G)
    (hF : F (closedPoint X.functionField) = genericPoint Y)
    (hG : G (closedPoint X.functionField) = genericPoint Y) :
    functionFieldMapOfMorphism F hF = functionFieldMapOfMorphism G hG := by
  subst G
  rfl

-- Unfold scheme carriers and generic-stalk aliases while elaborating this proof.
set_option backward.isDefEq.respectTransparency false in
/-- Recovering the field map from its generic-point morphism returns the original map.
@isnad1 id=eq.0h3v.s8.1b6f6f915299 from=translated src=- shape=0a49cf4c vocab=f1809a42
-/
lemma functionFieldMap_functionFieldMorphism
    [IsIntegral X] [IsIntegral Y]
    (E : X.functionField ≃+* Y.functionField) :
    functionFieldMapOfMorphism (functionFieldMorphism E)
      (functionFieldMorphism_closedPoint E) =
        CommRingCat.ofHom E.symm.toRingHom := by
  let q : Y.functionField ⟶ X.functionField :=
    CommRingCat.ofHom E.symm.toRingHom
  let xq : Σ y, { q : Y.presheaf.stalk y ⟶ X.functionField //
      IsLocalHom q.hom } := ⟨genericPoint Y, q, inferInstance⟩
  have hr := (SpecToEquivOfLocalRing Y X.functionField).apply_symm_apply xq
  obtain ⟨hpoint, hmap⟩ := SpecToEquivOfLocalRing_eq_iff.mp hr
  dsimp [SpecToEquivOfLocalRing, xq, q] at hpoint hmap
  change Scheme.stalkClosedPointTo
      (Spec.map q ≫ Y.fromSpecStalk (genericPoint Y)) = _ ≫ q at hmap
  change _ ≫ Scheme.stalkClosedPointTo
      (Spec.map q ≫ Y.fromSpecStalk (genericPoint Y)) = q
  let hF := functionFieldMorphism_closedPoint E
  have hmap' : Scheme.stalkClosedPointTo
      (Spec.map q ≫ Y.fromSpecStalk (genericPoint Y)) =
        (Y.presheaf.stalkCongr (.of_eq hF)).hom ≫ q := by
    exact hmap
  rw [hmap']
  change (Y.presheaf.stalkCongr (.of_eq hF)).inv ≫
    (Y.presheaf.stalkCongr (.of_eq hF)).hom ≫ q = q
  exact Iso.inv_hom_id_assoc _ q

/-- The generic-point morphism contravariantly attached to an arbitrary
embedding of integral-scheme function fields.-/
noncomputable def functionFieldMorphismOfHom
    [IrreducibleSpace X] [IrreducibleSpace Y]
    (q : Y.functionField ⟶ X.functionField) :
    Spec X.functionField ⟶ Y :=
  Spec.map q ≫ Y.fromSpecStalk (genericPoint Y)

-- Unfold scheme carriers and generic-stalk aliases while elaborating this proof.
set_option backward.isDefEq.respectTransparency false in
/-- A function-field embedding sends the closed point of the source field
spectrum to the generic point of the target scheme.
@isnad1 id=eq.0h3v.s8.cef0e0e22364 from=translated src=- shape=3e9080e1 vocab=0deadeb5
-/
lemma functionFieldMorphismOfHom_closedPoint
    [IsIntegral X] [IsIntegral Y]
    (q : Y.functionField ⟶ X.functionField) :
    functionFieldMorphismOfHom q (closedPoint X.functionField) =
      genericPoint Y := by
  letI : IsLocalHom q.hom := by
    refine ⟨fun a ha ↦ ?_⟩
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact (isUnit_iff_ne_zero.mp ha) (by rw [hz, map_zero])
  rw [functionFieldMorphismOfHom, Scheme.Hom.comp_apply, Spec_closedPoint,
    Scheme.fromSpecStalk_closedPoint]

-- Unfold scheme carriers and generic-stalk aliases while elaborating this proof.
set_option backward.isDefEq.respectTransparency false in
/-- Recovering the contravariant function-field map from the generic-point
morphism attached to an embedding returns that embedding.
@isnad1 id=eq.0h3v.s5.11d93bafba9f from=translated src=- shape=6f603ec9 vocab=eda4a094
-/
lemma functionFieldMap_functionFieldMorphismOfHom
    [IsIntegral X] [IsIntegral Y]
    (q : Y.functionField ⟶ X.functionField) :
    functionFieldMapOfMorphism (functionFieldMorphismOfHom q)
      (functionFieldMorphismOfHom_closedPoint q) = q := by
  letI : IsLocalHom q.hom := by
    refine ⟨fun a ha ↦ ?_⟩
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact (isUnit_iff_ne_zero.mp ha) (by rw [hz, map_zero])
  let xq : Σ y, { q : Y.presheaf.stalk y ⟶ X.functionField //
      IsLocalHom q.hom } := ⟨genericPoint Y, q, inferInstance⟩
  have hr := (SpecToEquivOfLocalRing Y X.functionField).apply_symm_apply xq
  obtain ⟨hpoint, hmap⟩ := SpecToEquivOfLocalRing_eq_iff.mp hr
  dsimp [SpecToEquivOfLocalRing, xq] at hpoint hmap
  change Scheme.stalkClosedPointTo
      (Spec.map q ≫ Y.fromSpecStalk (genericPoint Y)) = _ ≫ q at hmap
  change _ ≫ Scheme.stalkClosedPointTo
      (Spec.map q ≫ Y.fromSpecStalk (genericPoint Y)) = q
  let hF := functionFieldMorphismOfHom_closedPoint q
  have hmap' : Scheme.stalkClosedPointTo
      (Spec.map q ≫ Y.fromSpecStalk (genericPoint Y)) =
        (Y.presheaf.stalkCongr (.of_eq hF)).hom ≫ q := by
    exact hmap
  rw [hmap']
  change (Y.presheaf.stalkCongr (.of_eq hF)).inv ≫
    (Y.presheaf.stalkCongr (.of_eq hF)).hom ≫ q = q
  exact Iso.inv_hom_id_assoc _ q

/-- A dominant partial map induces a prescribed function-field embedding as
soon as its generic-point morphism is the one attached to that embedding.
@isnad1 id=eq.1h4v.s6.d552bd2ec505 from=translated src=- shape=78b2d7f4 vocab=0c599180
-/
lemma PartialMap.functionFieldMap_eq_of_fromFunctionField_eq_hom
    [IsIntegral X] [IsIntegral Y]
    (f : X.PartialMap Y) [IsDominant f.hom]
    (q : Y.functionField ⟶ X.functionField)
    (h : f.fromFunctionField = functionFieldMorphismOfHom q) :
    f.functionFieldMap = q := by
  change functionFieldMapOfMorphism f.fromFunctionField
      f.fromFunctionField_closedPoint = q
  exact (functionFieldMapOfMorphism_congr h
    f.fromFunctionField_closedPoint
    (functionFieldMorphismOfHom_closedPoint q)).trans
      (functionFieldMap_functionFieldMorphismOfHom q)

-- Unfold scheme carriers and generic-stalk aliases while elaborating this proof.
set_option backward.isDefEq.respectTransparency false in
/-- Two morphisms from the spectrum of an integral scheme's function field
which carry the closed point to the target generic point are equal as soon as
they induce the same map on function fields.
@isnad1 id=eq.3h4v.s9.3a886ae7be66 from=translated src=- shape=fa1adbaf vocab=5ac8131b
-/
lemma functionFieldMorphism_eq_of_functionFieldMapOfMorphism_eq
    [IsIntegral X] [IsIntegral Y]
    {F G : Spec X.functionField ⟶ Y}
    (hF : F (closedPoint X.functionField) = genericPoint Y)
    (hG : G (closedPoint X.functionField) = genericPoint Y)
    (hmap : functionFieldMapOfMorphism F hF =
      functionFieldMapOfMorphism G hG) : F = G := by
  apply (SpecToEquivOfLocalRing Y X.functionField).injective
  apply SpecToEquivOfLocalRing_eq_iff.mpr
  refine ⟨hF.trans hG.symm, ?_⟩
  unfold functionFieldMapOfMorphism at hmap
  let eF := Y.presheaf.stalkCongr (.of_eq hF.symm)
  let eG := Y.presheaf.stalkCongr (.of_eq hG.symm)
  have hm := congrArg (fun q ↦ eF.inv ≫ q) hmap
  change stalkClosedPointTo F =
    (Y.presheaf.stalkCongr (.of_eq (hF.trans hG.symm))).hom ≫
      stalkClosedPointTo G
  simpa [Category.assoc, Iso.inv_hom_id_assoc, eF, eG,
    TopCat.Presheaf.stalkCongr, TopCat.Presheaf.stalkSpecializes_comp,
    TopCat.Presheaf.stalkSpecializes_comp_assoc] using hm

/-- A dominant partial map has the generic-point morphism prescribed by a
function-field equivalence as soon as the induced field map is its inverse.
@isnad1 id=eq.1h4v.s8.9cae11bdc5d1 from=translated src=- shape=eb1fb710 vocab=d748b1e1
-/
lemma PartialMap.fromFunctionField_eq_of_functionFieldMap_eq
    [IsIntegral X] [IsIntegral Y]
    (f : X.PartialMap Y) [IsDominant f.hom]
    (E : X.functionField ≃+* Y.functionField)
    (h : f.functionFieldMap = CommRingCat.ofHom E.symm.toRingHom) :
    f.fromFunctionField = functionFieldMorphism E := by
  apply functionFieldMorphism_eq_of_functionFieldMapOfMorphism_eq
    f.fromFunctionField_closedPoint (functionFieldMorphism_closedPoint E)
  change f.functionFieldMap = _
  rw [h]
  exact (functionFieldMap_functionFieldMorphism E).symm

/-- A partial map is dominant when its generic-point morphism hits the target generic point.
@isnad1 id=isdomina.1h3v.s8.05ce29c86d6a from=translated src=- shape=b3ae00dd vocab=ce964b65
-/
lemma PartialMap.isDominant_of_fromFunctionField_closedPoint
    [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X.PartialMap Y)
    (h : f.fromFunctionField (closedPoint X.functionField) = genericPoint Y) :
    IsDominant f.hom := by
  rw [isDominant_iff]
  apply DenseRange.of_comp (g := f.genericLift)
  have hdense : DenseRange f.fromFunctionField := by
    apply (dense_iff_closure_eq.mpr (genericPoint_spec Y)).mono
    rintro y (rfl : y = genericPoint Y)
    exact ⟨closedPoint X.functionField, h⟩
  simpa only [← f.genericLift_hom, Scheme.Hom.comp_base,
    TopCat.coe_comp, Function.comp_apply] using hdense

/-- A rational map is dominant when its function-field morphism hits the target generic point.
@isnad1 id=isdomina.1h3v.s8.d3c65458918a from=translated src=- shape=e949d4fe vocab=98c306d9
-/
lemma RationalMap.isDominant_of_fromFunctionField_closedPoint
    [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : Scheme.RationalMap X Y)
    (h : f.fromFunctionField (closedPoint X.functionField) = genericPoint Y) :
    f.IsDominant := by
  let F := f.representative
  have hF : F.fromFunctionField (closedPoint X.functionField) = genericPoint Y := by
    have hrep : F.fromFunctionField = f.fromFunctionField := by
      change f.representative.fromFunctionField = f.fromFunctionField
      rw [← RationalMap.fromFunctionField_toRationalMap]
      rw [f.toRationalMap_representative]
    rw [hrep]
    exact h
  haveI : IsDominant F.hom := F.isDominant_of_fromFunctionField_closedPoint hF
  rw [← f.toRationalMap_representative]
  infer_instance

/--
@isnad1 id=eq.0h3v.s5.548c5cf7a712 from=translated src=- shape=d59f3166 vocab=051d0f23
-/
lemma RationalMap.fromFunctionField_representative
    [IrreducibleSpace X]
    (f : Scheme.RationalMap X Y) :
    f.representative.fromFunctionField = f.fromFunctionField := by
  rw [← RationalMap.fromFunctionField_toRationalMap]
  rw [f.toRationalMap_representative]

/--
@isnad1 id=eq.0h5v.s6.bb76afa36c46 from=translated src=- shape=bb0511b9 vocab=a275fb6c
-/
lemma RationalMap.fromFunctionField_comp
    [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : Scheme.RationalMap X Y) [f.IsDominant]
    (g : Scheme.RationalMap Y Z) :
    (f.comp g).fromFunctionField =
      Spec.map f.representative.functionFieldMap ≫ g.fromFunctionField := by
  rw [← g.toRationalMap_representative]
  rw [RationalMap.comp_def]
  rw [RationalMap.fromFunctionField_toRationalMap]
  rw [PartialMap.fromFunctionField_comp]
  rw [RationalMap.fromFunctionField_representative]
  rw [g.toRationalMap_representative]

/-- The representative of a dominant rational map recovers a prescribed
function-field embedding from its generic-point description.
@isnad1 id=eq.1h4v.s6.4dd7133eb65a from=translated src=- shape=2741c1bd vocab=8c72a688
-/
lemma RationalMap.functionFieldMap_representative_eq_of_fromFunctionField_eq_hom
    [IsIntegral X] [IsIntegral Y]
    (f : Scheme.RationalMap X Y) [f.IsDominant]
    (q : Y.functionField ⟶ X.functionField)
    (h : f.fromFunctionField = functionFieldMorphismOfHom q) :
    f.representative.functionFieldMap = q := by
  apply PartialMap.functionFieldMap_eq_of_fromFunctionField_eq_hom
  rw [RationalMap.fromFunctionField_representative]
  exact h

/-- Generic-point morphisms prescribed by two successive function-field
embeddings compose contravariantly by composition of those embeddings.
@isnad1 id=eq.2h7v.s7.5df3fb8240c5 from=translated src=- shape=e43cceb9 vocab=4f61a04d
-/
theorem RationalMap.comp_fromFunctionField_eq_hom
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : Scheme.RationalMap X Y) [f.IsDominant]
    (g : Scheme.RationalMap Y Z)
    (qf : Y.functionField ⟶ X.functionField)
    (qg : Z.functionField ⟶ Y.functionField)
    (hf : f.fromFunctionField = functionFieldMorphismOfHom qf)
    (hg : g.fromFunctionField = functionFieldMorphismOfHom qg) :
    (f.comp g).fromFunctionField =
      functionFieldMorphismOfHom (qg ≫ qf) := by
  rw [RationalMap.fromFunctionField_comp]
  rw [f.functionFieldMap_representative_eq_of_fromFunctionField_eq_hom qf hf]
  rw [hg]
  unfold functionFieldMorphismOfHom
  rw [← Category.assoc]
  exact congrArg (fun t ↦ t ≫ Z.fromSpecStalk (genericPoint Z))
    (Spec.map_comp qg qf).symm

/--
@isnad1 id=eq.0h1v.s5.2be17932a19a from=translated src=- shape=79837114 vocab=65f3d114
-/
lemma RationalMap.fromFunctionField_id [IrreducibleSpace X] :
    (RationalMap.id X).fromFunctionField =
      X.fromSpecStalk (genericPoint X) := by
  rw [RationalMap.fromFunctionField_toRationalMap]
  change (𝟙 X : X ⟶ X).toPartialMap.fromSpecStalkOfMem _ = _
  simpa only [Category.comp_id] using PartialMap.fromSpecStalkOfMem_toPartialMap
    (𝟙 X) (genericPoint X)

/--
@isnad1 id=eq.1h4v.s8.8ca37d41be37 from=translated src=- shape=3946beaa vocab=d748b1e1
-/
lemma PartialMap.functionFieldMap_eq_of_fromFunctionField_eq
    [IsIntegral X] [IsIntegral Y]
    (f : X.PartialMap Y) [IsDominant f.hom]
    (E : X.functionField ≃+* Y.functionField)
    (h : f.fromFunctionField = functionFieldMorphism E) :
    f.functionFieldMap = CommRingCat.ofHom E.symm.toRingHom := by
  change functionFieldMapOfMorphism f.fromFunctionField
      f.fromFunctionField_closedPoint = _
  rw [functionFieldMapOfMorphism_congr h]
  exact functionFieldMap_functionFieldMorphism E

/--
@isnad1 id=eq.1h4v.s8.c0953045d930 from=translated src=- shape=ef17d0c2 vocab=1bc99b99
-/
lemma RationalMap.functionFieldMap_representative_eq
    [IsIntegral X] [IsIntegral Y]
    (f : Scheme.RationalMap X Y) [f.IsDominant]
    (E : X.functionField ≃+* Y.functionField)
    (h : f.fromFunctionField = functionFieldMorphism E) :
    f.representative.functionFieldMap =
      CommRingCat.ofHom E.symm.toRingHom := by
  apply PartialMap.functionFieldMap_eq_of_fromFunctionField_eq _ E
  rw [RationalMap.fromFunctionField_representative]
  exact h

/--
@isnad1 id=eq.2h5v.s8.5abece5c302f from=translated src=- shape=d54ff5b0 vocab=3be565e7
-/
theorem RationalMap.comp_eq_id_of_fromFunctionField_eq
    [IsIntegral X] [IsIntegral Y]
    (f : Scheme.RationalMap X Y) [f.IsDominant]
    (g : Scheme.RationalMap Y X) [g.IsDominant]
    (E : X.functionField ≃+* Y.functionField)
    (hf : f.fromFunctionField = functionFieldMorphism E)
    (hg : g.fromFunctionField = functionFieldMorphism E.symm) :
    f.comp g = RationalMap.id X := by
  apply RationalMap.eq_of_fromFunctionField_eq
  rw [RationalMap.fromFunctionField_comp]
  rw [f.functionFieldMap_representative_eq E hf]
  rw [hg]
  unfold functionFieldMorphism
  rw [RationalMap.fromFunctionField_id]
  simp only [RingEquiv.symm_symm]
  rw [← Category.assoc]
  let p : X.functionField ⟶ Y.functionField :=
    CommRingCat.ofHom E.toRingHom
  let q : Y.functionField ⟶ X.functionField :=
    CommRingCat.ofHom E.symm.toRingHom
  have hpq : p ≫ q = 𝟙 _ := by
    ext z
    exact E.symm_apply_apply z
  have hspec : Spec.map q ≫ Spec.map p = 𝟙 _ := by
    calc
      Spec.map q ≫ Spec.map p = Spec.map (p ≫ q) :=
        (Spec.map_comp p q).symm
      _ = Spec.map (𝟙 _) := congrArg Spec.map hpq
      _ = 𝟙 _ := Spec.map_id _
  change (Spec.map q ≫ Spec.map p) ≫
    X.fromSpecStalk (genericPoint X) = _
  rw [hspec, Category.id_comp]

-- Unfold scheme carriers and generic-stalk aliases while elaborating this proof.
set_option backward.isDefEq.respectTransparency false in
/-- Rational maps whose generic-point morphisms are prescribed by two
successive function-field equivalences compose according to the transitive
equivalence.
@isnad1 id=eq.2h7v.s9.5e1cb2b0650b from=translated src=- shape=a006cd3f vocab=e4cce889
-/
theorem RationalMap.comp_fromFunctionField_eq_trans
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : Scheme.RationalMap X Y) [f.IsDominant]
    (g : Scheme.RationalMap Y Z) [g.IsDominant]
    (E : X.functionField ≃+* Y.functionField)
    (F : Y.functionField ≃+* Z.functionField)
    (hf : f.fromFunctionField = functionFieldMorphism E)
    (hg : g.fromFunctionField = functionFieldMorphism F) :
    (f.comp g).fromFunctionField = functionFieldMorphism (E.trans F) := by
  rw [RationalMap.fromFunctionField_comp]
  rw [f.functionFieldMap_representative_eq E hf]
  rw [hg]
  unfold functionFieldMorphism
  rw [← Category.assoc]
  rw [← Spec.map_comp]
  rfl

end

end AlgebraicGeometry.Scheme
