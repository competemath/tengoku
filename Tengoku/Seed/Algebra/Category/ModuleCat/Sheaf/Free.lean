/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Tengoku.Seed.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Tengoku.Seed.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# Free sheaves of modules

In this file, we construct the functor
`SheafOfModules.freeFunctor : Type u ⥤ SheafOfModules.{u} R` which sends
a type `I` to the coproduct of copies indexed by `I` of `unit R`.

## TODO

* In case the category `C` has a terminal object `X`, promote `freeHomEquiv`
  into an adjunction between `freeFunctor` and the evaluation functor at `X`.
  (Alternatively, assuming specific universe parameters, we could show that
  `freeFunctor` is a left adjoint to `SheafOfModules.sectionsFunctor`.)

-/

@[expose] public section

universe u v₁ v₂ u₁ u₂
open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

/-- The free sheaf of modules on a certain type `I`. -/
noncomputable def free (I : Type u) : SheafOfModules.{u} R := ∐ (fun (_ : I) ↦ unit R)

/-- The inclusions `unit R ⟶ free I`. -/
noncomputable def ιFree {I : Type u} (i : I) : unit R ⟶ free I :=
  Sigma.ι (fun (_ : I) ↦ unit R) i

/-- The tautological cofan with point `free I : SheafOfModules R`. -/
noncomputable def freeCofan (I : Type u) : Cofan (fun (_ : I) ↦ unit R) :=
  Cofan.mk (P := free I) ιFree

/--
@isnad1 id=eq.0h5v.s7.1186ffa68219 from=seed src=0 shape=50d7d438 vocab=ba2e537b
-/
@[simp]
lemma freeCofan_inj {I : Type u} (i : I) :
    (freeCofan (R := R) I).inj i = ιFree i := rfl

/-- `free I` is the colimit of copies of `unit R` indexed by `I`. -/
noncomputable def isColimitFreeCofan (I : Type u) :
    IsColimit (freeCofan (R := R) I) :=
  coproductIsCoproduct _

set_option backward.isDefEq.respectTransparency false in
/-- The data of a morphism `free I ⟶ M` from a free sheaf of modules is
equivalent to the data of a family `I → M.sections` of sections of `M`. -/
noncomputable def freeHomEquiv (M : SheafOfModules.{u} R) {I : Type u} :
    (free I ⟶ M) ≃ (I → M.sections) where
  toFun f i := M.unitHomEquiv (ιFree i ≫ f)
  invFun s := Cofan.IsColimit.desc (isColimitFreeCofan I) (fun i ↦ M.unitHomEquiv.symm (s i))
  left_inv s := Cofan.IsColimit.hom_ext (isColimitFreeCofan I) _ _
    (fun i ↦ by simp [← freeCofan_inj])
  right_inv f := by ext1 i; simp [← freeCofan_inj]

/--
@isnad1 id=eq.0h9v.s9.bbad71eac859 from=seed src=0 shape=bba8510f vocab=ff35e4f7
-/
lemma freeHomEquiv_comp_apply {M N : SheafOfModules.{u} R} {I : Type u}
    (f : free I ⟶ M) (p : M ⟶ N) (i : I) :
    N.freeHomEquiv (f ≫ p) i = sectionsMap p (M.freeHomEquiv f i) := rfl

/--
@isnad1 id=eq.0h8v.s9.ac8cfa8e47c1 from=seed src=0 shape=6f4e1146 vocab=1b28bf36
-/
lemma freeHomEquiv_symm_comp {M N : SheafOfModules.{u} R} {I : Type u} (s : I → M.sections)
    (p : M ⟶ N) :
    M.freeHomEquiv.symm s ≫ p = N.freeHomEquiv.symm (fun i ↦ sectionsMap p (s i)) :=
  N.freeHomEquiv.injective (by ext; simp [freeHomEquiv_comp_apply])

/-- The tautological section of `free I : SheafOfModules R` corresponding to `i : I`. -/
noncomputable abbrev freeSection {I : Type u} (i : I) : (free (R := R) I).sections :=
  (free (R := R) I).freeHomEquiv (𝟙 (free I)) i

/--
@isnad1 id=eq.0h7v.s8.128db7f89ab8 from=seed src=0 shape=5b1ec5f7 vocab=64e53771
-/
lemma freeHomEquiv_apply {M : SheafOfModules.{u} R} {I : Type u}
    (f : free I ⟶ M) (i : I) :
    freeHomEquiv M f i = sectionsMap f (freeSection i) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h7v.s9.b314ceda8a35 from=seed src=0 shape=f3ff04d5 vocab=6d55059f
-/
lemma unitHomEquiv_symm_freeHomEquiv_apply
    {I : Type u} {M : SheafOfModules.{u} R} (f : free I ⟶ M) (i : I) :
    M.unitHomEquiv.symm (M.freeHomEquiv f i) = ιFree i ≫ f := by
  simp [freeHomEquiv]

section

variable {I J : Type u} (f : I → J)

/-- The morphism of presheaves of `R`-modules `free I ⟶ free J` induced by
a map `f : I → J`. -/
noncomputable def freeMap : free (R := R) I ⟶ free J :=
  (freeHomEquiv _).symm (fun i ↦ freeSection (f i))

/--
@isnad1 id=eq.0h6v.s9.52ab4f73097c from=seed src=0 shape=70a39361 vocab=accc223e
-/
@[simp]
lemma freeHomEquiv_freeMap :
    (freeHomEquiv _ (freeMap (R := R) f)) = freeSection.comp f :=
  (freeHomEquiv _).symm.injective (by simp; rfl)

/--
@isnad1 id=eq.0h7v.s7.b3115eef4da1 from=seed src=0 shape=c836027a vocab=c92581a7
-/
@[simp]
lemma sectionMap_freeMap_freeSection (i : I) :
    sectionsMap (freeMap (R := R) f) (freeSection i) = freeSection (f i) := by
  simp [← freeHomEquiv_comp_apply]

/--
@isnad1 id=eq.0h7v.s8.dcdc3c9e3f75 from=seed src=0 shape=bbcc623c vocab=646cb035
-/
lemma sectionsMap_freeHomEquiv_symm_freeSection
    {M : SheafOfModules.{u} R} (f : I → M.sections) (i : I) :
    sectionsMap ((freeHomEquiv M).symm f) (freeSection i) = f i := by
  obtain ⟨f, rfl⟩ := (freeHomEquiv M).surjective f
  cat_disch

/--
@isnad1 id=eq.0h7v.s7.f1572515966c from=seed src=0 shape=56097645 vocab=de89f468
-/
@[reassoc (attr := simp)]
lemma ιFree_freeMap (i : I) :
    ιFree (R := R) i ≫ freeMap f = ιFree (f i) := by
  rw [← unitHomEquiv_symm_freeHomEquiv_apply, freeHomEquiv_freeMap]
  dsimp [freeSection]
  rw [unitHomEquiv_symm_freeHomEquiv_apply, Category.comp_id]

end

/-- The functor `Type u ⥤ SheafOfModules.{u} R` which sends a type `I` to
`free I` which is a coproduct indexed by `I` of copies of `R` (thought of as a
presheaf of modules over itself). -/
noncomputable def freeFunctor : Type u ⥤ SheafOfModules.{u} R :=
  sigmaConst.obj (unit R)

/--
@isnad1 id=eq.0h4v.s7.20658c3c86a4 from=seed src=0 shape=13dc2748 vocab=60c742bd
-/
@[simp]
lemma freeFunctor_obj (X : Type u) :
    (freeFunctor (R := R)).obj X = free X := rfl

/--
@isnad1 id=eq.0h6v.s7.299ed03b5010 from=seed src=0 shape=0c931fb9 vocab=4a38cef7
-/
@[simp]
lemma freeFunctor_map {X Y : Type u} (f : X ⟶ Y) :
    dsimp% (freeFunctor (R := R)).map f = freeMap f :=
  Cofan.IsColimit.hom_ext (isColimitFreeCofan _) _ _
    (fun i ↦ (Sigma.ι_desc _ _).trans (ιFree_freeMap f i).symm)

instance : PreservesColimitsOfSize.{v₂, u₂} (freeFunctor (R := R)) :=
  inferInstanceAs (PreservesColimitsOfSize.{v₂, u₂} (sigmaConst.obj _))

section

variable (I J : Type u)

/-- A binary coproduct of free sheaves of modules is the free sheaf
of modules on the sum type. -/
noncomputable def freeSumIso : free I ⨿ free J ≅ free (R := R) (I ⊕ J) :=
  IsColimit.coconePointUniqueUpToIso
    (coprodIsCoprod (free (R := R) I) (free J))
    (mapIsColimitOfPreservesOfIsColimit (freeFunctor (R := R)) _ _
      (Types.binaryCoproductColimit I J))

/--
@isnad1 id=eq.0h5v.s8.a4125a566730 from=seed src=0 shape=d94abd6b vocab=da4fd6cf
-/
@[reassoc (attr := simp)]
lemma inl_freeSumIso_hom :
    coprod.inl ≫ (freeSumIso (R := R) I J).hom = freeMap Sum.inl := by
  rw [← dsimp% freeFunctor_map (↾(Sum.inl : I → I ⊕ J))]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (free (R := R) I) (free J)) _ (.mk .left)

/--
@isnad1 id=eq.0h5v.s8.1ec1c62ccc82 from=seed src=0 shape=a15b36f2 vocab=a8b381e4
-/
@[reassoc (attr := simp)]
lemma inr_freeSumIso_hom :
    coprod.inr ≫ (freeSumIso (R := R) I J).hom = freeMap Sum.inr := by
  rw [← dsimp% freeFunctor_map (↾(Sum.inr : J → I ⊕ J))]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (free (R := R) I) (free J)) _ (.mk .right)

end

section

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'} {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) (I : Type u)

/-- Let `F` be a functor from the category of sheaves of `R`-modules to sheaves of `S`-modules.
Then a morphism `η : unit S ⟶ F.obj (unit R)` induces a morphism from `free (R := S) I` to
`F.obj (free I)`. See also `mapFreeIso` for the iso version. -/
noncomputable def mapFree (η : unit S ⟶ F.obj (unit R)) : free (R := S) I ⟶ F.obj (free I) :=
  (isColimitFreeCofan I).map (F.mapCocone (freeCofan I)) (Discrete.natTrans fun _ ↦ η)

/--
@isnad1 id=eq.0h10v.s9.e800a537fe03 from=seed src=0 shape=648a27a7 vocab=eee326af
-/
@[reassoc (attr := simp)]
lemma ιFree_mapFree (η : unit S ⟶ F.obj (unit R)) (i : I) :
    ιFree i ≫ mapFree F I η = η ≫ F.map (ιFree i) :=
  IsColimit.ι_map (isColimitFreeCofan I) (F.mapCocone (freeCofan I))
    (Discrete.natTrans fun _ ↦ η) (Discrete.mk i)

variable [PreservesColimitsOfShape (Discrete I) F]

/-- Let `F` be a functor from the category of sheaves of `R`-modules to sheaves of `S`-modules.
If `F` preserves coproducts and `unit S ≅ F.obj (unit R)`, then `F` preserves free sheaves of
modules. -/
noncomputable def mapFreeIso (η : unit S ≅ F.obj (unit R)) : free (R := S) I ≅ F.obj (free I) :=
  (isColimitFreeCofan I).coconePointsIsoOfNatIso (isColimitOfPreserves F (isColimitFreeCofan I))
    (Discrete.natIso fun _ ↦ η)

/--
@isnad1 id=eq.0h9v.s9.cb7f46acbf8f from=seed src=0 shape=e0dd2795 vocab=677564e8
-/
lemma mapFreeIso_hom (η : unit S ≅ F.obj (unit R)) :
    (mapFreeIso F I η).hom = mapFree F I η.hom := rfl

/--
@isnad1 id=eq.0h10v.s9.ec9096e6279c from=seed src=0 shape=5c9ebb05 vocab=ffa88a53
-/
@[reassoc (attr := simp)]
lemma ιFree_mapFreeIso_hom (η : unit S ≅ F.obj (unit R)) (i : I) :
    ιFree i ≫ (mapFreeIso F I η).hom = η.hom ≫ F.map (ιFree i) :=
  ιFree_mapFree _ _ _ _

/--
@isnad1 id=eq.0h10v.s9.ec9096e6279c from=seed src=0 shape=5c9ebb05 vocab=ffa88a53
-/
@[deprecated (since := "2026-04-21")] alias ιFree_mapFree_inv := ιFree_mapFreeIso_hom

/--
@isnad1 id=eq.0h10v.s9.3603417ce752 from=seed src=0 shape=5f1f1df1 vocab=4ca3b367
-/
@[reassoc (attr := simp)]
lemma map_ιFree_mapFreeIso_inv (η : unit S ≅ F.obj (unit R)) (i : I) :
    F.map (ιFree i) ≫ (mapFreeIso F I η).inv = η.inv ≫ ιFree i :=
  IsColimit.ι_map (isColimitOfPreserves F (isColimitFreeCofan I)) (freeCofan I)
    (Discrete.natTrans fun _ ↦ η.inv) (Discrete.mk i)

/--
@isnad1 id=eq.0h10v.s9.3603417ce752 from=seed src=0 shape=5f1f1df1 vocab=4ca3b367
-/
@[deprecated (since := "2026-04-21")] alias map_ιFree_mapFree_hom := map_ιFree_mapFreeIso_inv

end

end SheafOfModules
