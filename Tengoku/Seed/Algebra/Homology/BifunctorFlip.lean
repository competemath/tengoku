/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Homology.Bifunctor
public import Tengoku.Seed.Algebra.Homology.TotalComplexSymmetry

/-!
# Action of the flip of a bifunctor on homological complexes

Given `K₁ : HomologicalComplex C₁ c₁`, `K₂ : HomologicalComplex C₂ c₂`,
a bifunctor `F : C₁ ⥤ C₂ ⥤ D`, and a complex shape `c` with
`[TotalComplexShape c₁ c₂ c]` and `[TotalComplexShape c₂ c₁ c]`, we define
an isomorphism `mapBifunctor K₂ K₁ F.flip c ≅ mapBifunctor K₁ K₂ F c`
under the additional assumption `[TotalComplexShapeSymmetry c₁ c₂ c]`.

-/

@[expose] public section

open CategoryTheory Limits

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

namespace HomologicalComplex

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (φ₁ : K₁ ⟶ L₁)
  (K₂ L₂ : HomologicalComplex C₂ c₂) (φ₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [TotalComplexShape c₂ c₁ c]
  [TotalComplexShapeSymmetry c₁ c₂ c]

/--
@isnad1 id=iff.0h12v.s7.5ce4c32d2f6d from=seed src=0 shape=00f41cae vocab=4c9b4919
-/
lemma hasMapBifunctor_flip_iff :
    HasMapBifunctor K₂ K₁ F.flip c ↔ HasMapBifunctor K₁ K₂ F c :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).flip_hasTotal_iff c

variable [DecidableEq J] [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c]

instance : HasMapBifunctor K₂ K₁ F.flip c := by
  rw [hasMapBifunctor_flip_iff]
  infer_instance

/-- The canonical isomorphism `mapBifunctor K₂ K₁ F.flip c ≅ mapBifunctor K₁ K₂ F c`. -/
noncomputable def mapBifunctorFlipIso :
    mapBifunctor K₂ K₁ F.flip c ≅ mapBifunctor K₁ K₂ F c :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).totalFlipIso c

/--
@isnad1 id=eq.1h15v.s10.871f8a2cbb9f from=seed src=0 shape=5c348fa8 vocab=bd4d1f59
-/
@[reassoc (attr := simp)]
lemma ι_mapBifunctorFlipIso_hom (i₁ : I₁) (i₂ : I₂) (j : J) (hj : c₂.π c₁ c (i₂, i₁) = j) :
    ιMapBifunctor K₂ K₁ F.flip c i₂ i₁ j hj ≫ (mapBifunctorFlipIso K₁ K₂ F c).hom.f j =
      c₁.σ c₂ c i₁ i₂ • ιMapBifunctor K₁ K₂ F c i₁ i₂ j
        (by rw [← ComplexShape.π_symm c₁ c₂ c i₁ i₂, hj]) :=
  HomologicalComplex₂.ιTotal_totalFlipIso_f_hom
    (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂) c i₁ i₂ j hj

/--
@isnad1 id=eq.1h15v.s10.f2cc5fbbf00f from=seed src=0 shape=911f89f9 vocab=9bc2340e
-/
@[reassoc (attr := simp)]
lemma ι_mapBifunctorFlipIso_inv (i₁ : I₁) (i₂ : I₂) (j : J) (hj : c₁.π c₂ c (i₁, i₂) = j) :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j hj ≫ (mapBifunctorFlipIso K₁ K₂ F c).inv.f j =
      c₁.σ c₂ c i₁ i₂ • ιMapBifunctor K₂ K₁ F.flip c i₂ i₁ j
        (by rw [ComplexShape.π_symm c₁ c₂ c i₁ i₂, hj]) :=
  HomologicalComplex₂.ιTotal_totalFlipIso_f_inv
    (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂) c i₁ i₂ j hj

/--
@isnad1 id=eq.0h12v.s8.1d75c639d0c4 from=seed src=0 shape=63281ce8 vocab=8b932f63
-/
lemma mapBifunctorFlipIso_flip
    [TotalComplexShapeSymmetry c₂ c₁ c] [TotalComplexShapeSymmetrySymmetry c₁ c₂ c] :
    mapBifunctorFlipIso K₂ K₁ F.flip c = (mapBifunctorFlipIso K₁ K₂ F c).symm :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).flip_totalFlipIso c

variable {K₁ K₂ L₁ L₂} in
/--
@isnad1 id=eq.0h16v.s9.894eee8eaeff from=seed src=0 shape=d36b1193 vocab=43d52627
-/
@[reassoc (attr := simp)]
lemma mapBifunctorFlipIso_hom_naturality :
      mapBifunctorMap φ₂ φ₁ F.flip c ≫ (mapBifunctorFlipIso L₁ L₂ F c).hom =
    (mapBifunctorFlipIso K₁ K₂ F c).hom ≫ mapBifunctorMap φ₁ φ₂ F c := by
  cat_disch

end HomologicalComplex
