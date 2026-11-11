/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Seed.Algebra.Category.ModuleCat.Limits
import Tengoku.Seed.AlgebraicGeometry.Modules.Sheaf
import Tengoku.Seed.CategoryTheory.Sites.SheafCohomology.Cech
import Tengoku.Aintlib.ModularCurves.ForMathlib.FormalCoproductAdditive

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Base-linear Cech complexes of scheme modules

This file retains the module structure over the global functions on the base
in the native Cech complex of a scheme module.
-/

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Opposite
  TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Inverse image commutes with the finite product open indexing a Cech cochain factor.
@isnad1 id=eq.0h7v.s8.8cf39a8aed1c from=translated src=- shape=5f1c7208 vocab=f84110d9
-/
theorem Scheme.Hom.preimage_cechIntersection
    {X Y : Scheme.{u}} (g : Y ⟶ X) {ι : Type u}
    (U : ι → X.Opens) (n : ℕ) (i : Fin (n + 1) → ι) :
    g ⁻¹ᵁ (∏ᶜ fun k : Fin (n + 1) => U (i k)) =
      ∏ᶜ fun k : Fin (n + 1) => g ⁻¹ᵁ U (i k) := by
  rw [show (∏ᶜ fun k : Fin (n + 1) => U (i k)) =
      ⨅ k, U (i k) from
    (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
      (Preorder.isLimitIInf _)).to_eq]
  rw [show (∏ᶜ fun k : Fin (n + 1) => g ⁻¹ᵁ U (i k)) =
      ⨅ k, g ⁻¹ᵁ U (i k) from
    (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
      (Preorder.isLimitIInf _)).to_eq]
  ext y
  rw [TopologicalSpace.Opens.coe_iInf]
  change g y ∈ (((⨅ k, U (i k)) : X.Opens) : Set X) ↔ _
  rw [TopologicalSpace.Opens.coe_iInf]
  simp

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Sections of a scheme module, regarded functorially as modules over the
global functions on the base.-/
noncomputable def baseModulePresheaf {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) :
    X.Opensᵒᵖ ⥤ ModuleCat.{u} Γ(S, (⊤ : S.Opens)) :=
  (PresheafOfModules.forgetToPresheafModuleCat
      (op (⊤ : X.Opens)) (initialOpOfTerminal isTerminalTop)).obj M.1 ⋙
    ModuleCat.restrictScalars π.appTop.hom

/--
@isnad1 id=eq.0h5v.s11.375acfbf852d from=translated src=- shape=cc4bd687 vocab=33270f46
-/
@[simp]
theorem baseModulePresheaf_obj_coe {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) (V : X.Opensᵒᵖ) :
    ((baseModulePresheaf π M).obj V : Type u) = M.presheaf.obj V :=
  rfl

/--
@isnad1 id=eq.0h8v.s15.34dd64364885 from=translated src=- shape=e4057c6e vocab=1ced047c
-/
@[simp]
theorem baseModulePresheaf_map_apply {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {V W : X.Opensᵒᵖ} (f : V ⟶ W)
    (x : M.presheaf.obj V) :
    ((baseModulePresheaf π M).map f).hom x = M.presheaf.map f x :=
  rfl

/-- The base-linear presheaf underlying a scheme module is a sheaf.
@isnad1 id=issheaf.0h4v.s10.7d2bbfcad312 from=translated src=- shape=2fbba852 vocab=b9fcdee3
-/
theorem baseModulePresheaf_isSheaf {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (baseModulePresheaf π M) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _
    (CategoryTheory.forget (ModuleCat.{u} Γ(S, (⊤ : S.Opens))))]
  convert
    (Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget AddCommGrpCat.{u})).mp
      (Scheme.Modules.isSheaf M) using 1
  all_goals rfl

/-- A scheme module, regarded as a sheaf of modules over the global
functions on the base.-/
noncomputable def baseModuleSheaf {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) :
    Sheaf (Opens.grothendieckTopology X)
      (ModuleCat.{u} Γ(S, (⊤ : S.Opens))) :=
  ⟨baseModulePresheaf π M, baseModulePresheaf_isSheaf π M⟩

/--
@isnad1 id=eq.0h5v.s12.01d19dbc77c3 from=translated src=- shape=bc3e8e3b vocab=20270444
-/
@[simp]
theorem baseModuleSheaf_obj_coe {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) (V : X.Opensᵒᵖ) :
    ((baseModuleSheaf π M).obj.obj V : Type u) = M.presheaf.obj V :=
  rfl

/--
@isnad1 id=eq.0h8v.s17.e2e29f9df397 from=translated src=- shape=759fdbe9 vocab=2ecd5eb3
-/
@[simp]
theorem baseModuleSheaf_map_apply {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {V W : X.Opensᵒᵖ} (f : V ⟶ W)
    (x : M.presheaf.obj V) :
    ((baseModuleSheaf π M).obj.map f).hom x = M.presheaf.map f x :=
  rfl

/-- Sections over source opens, functorially regarded as modules over the base ring.-/
noncomputable def baseModulePresheafFunctor {X S : Scheme.{u}} (π : X ⟶ S) :
    X.Modules ⥤ X.Opensᵒᵖ ⥤ ModuleCat.{u} Γ(S, (⊤ : S.Opens)) :=
  toPresheafOfModules X ⋙
    PresheafOfModules.forgetToPresheafModuleCat
      (op (⊤ : X.Opens)) (initialOpOfTerminal isTerminalTop) ⋙
    (Functor.whiskeringRight X.Opensᵒᵖ _ _).obj
      (ModuleCat.restrictScalars π.appTop.hom)

/--
@isnad1 id=eq.0h4v.s11.bb76654cbb7f from=translated src=- shape=69aa2fdb vocab=9e6843ae
-/
@[simp]
theorem baseModulePresheafFunctor_obj {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) :
    (baseModulePresheafFunctor π).obj M = baseModulePresheaf π M :=
  rfl

/--
@isnad1 id=preserve.0h3v.s12.9e190b85a3a3 from=translated src=- shape=3979a91d vocab=cebe3b01
-/
instance baseModulePresheafFunctor_preservesZeroMorphisms
    {X S : Scheme.{u}} (π : X ⟶ S) :
    (baseModulePresheafFunctor π).PreservesZeroMorphisms where
  map_zero M N := by
    ext U x
    rfl

/-- Base-linear sections of a restricted module agree with the corresponding sections on the
image open.-/
noncomputable def baseModulePresheafRestrictAppIso
    {Y S Z : Scheme.{u}} (π : Y ⟶ S) (f : Z ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (U : Z.Opens) :
    (baseModulePresheaf (f ≫ π) (M.restrict f)).obj (op U) ≅
      (baseModulePresheaf π M).obj (op (f ''ᵁ U)) := by
  refine ModuleCat.isoMk (M.restrictAppIso f U) ?_
  intro r
  ext (x : Γ(M.restrict f, U))
  change
    (Y.presheaf.map
        ((initialOpOfTerminal isTerminalTop).to (op (f ''ᵁ U))))
          (π.appTop r) • (M.restrictAppIso f U).hom x =
      (M.restrictAppIso f U).hom
        (Z.presheaf.map ((initialOpOfTerminal isTerminalTop).to (op U))
          ((f ≫ π).appTop r) • x)
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
  congr 1
  have hrestrict (s : Γ(Y, (⊤ : Y.Opens))) :
      (f.appIso U).inv
          (Z.presheaf.map
            ((initialOpOfTerminal isTerminalTop).to (op U))
              (f.appTop s)) =
        Y.presheaf.map
          ((initialOpOfTerminal isTerminalTop).to (op (f ''ᵁ U))) s := by
    have hmap :
        f.appTop ≫ Z.presheaf.map
            ((initialOpOfTerminal isTerminalTop).to (op U)) ≫
              (f.appIso U).inv =
          Y.presheaf.map
            ((initialOpOfTerminal isTerminalTop).to (op (f ''ᵁ U))) := by
      rw [f.appIso_inv_naturality]
      rw [← Category.assoc]
      have htop :
          f.appTop ≫ (f.appIso (⊤ : Z.Opens)).inv =
            Y.presheaf.map
              (homOfLE (show f ''ᵁ (⊤ : Z.Opens) ≤
                (⊤ : Y.Opens) from le_top)).op := by
        have happLE :
            f.appLE (⊤ : Y.Opens) (⊤ : Z.Opens) le_rfl =
              f.appTop := by
          change f.appTop ≫ Z.presheaf.map (homOfLE le_rfl).op = f.appTop
          rw [Subsingleton.elim (homOfLE le_rfl).op (𝟙 _)]
          simp
        have h := f.appLE_appIso_inv (U := (⊤ : Y.Opens))
          (V := (⊤ : Z.Opens)) le_rfl
        rw [happLE] at h
        exact h
      rw [htop]
      rw [← Functor.map_comp]
      rfl
    exact ConcreteCategory.congr_hom hmap s
  rw [Scheme.Hom.comp_appTop]
  exact (hrestrict (π.appTop r)).symm

/-- Naturality of the base-linear section isomorphism for restriction along an open immersion.
@isnad1 id=eq.0h9v.s14.ea80752a5c3b from=translated src=- shape=3446500c vocab=de50ebec
-/
theorem baseModulePresheafRestrictAppIso_hom_naturality
    {Y S Z : Scheme.{u}} (π : Y ⟶ S) (f : Z ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) {U V : Z.Opens} (i : op V ⟶ op U) :
    (baseModulePresheaf (f ≫ π) (M.restrict f)).map i ≫
        (baseModulePresheafRestrictAppIso π f M U).hom =
      (baseModulePresheafRestrictAppIso π f M V).hom ≫
        (baseModulePresheaf π M).map
          (homOfLE (f.image_mono (leOfHom i.unop))).op := by
  ext x
  exact congr($((M.map_restrictAppIso_hom f i)) x)

/-- Base-linear sections on an ambient open are naturally identified with
top sections of the module restricted to that open.-/
noncomputable def baseModulePresheafRestrictIso
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) (U : X.Opens) :
    (baseModulePresheaf f M).obj (op U) ≅
      (ModuleCat.restrictScalars (U.ι ≫ f).appTop.hom).obj
        (ModuleCat.of Γ(U.toScheme, (⊤ : U.toScheme.Opens))
          Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens))) := by
  let eAdd := M.presheaf.mapIso (eqToIso U.ι_image_top).op ≪≫
    (M.restrictAppIso U.ι (⊤ : U.toScheme.Opens)).symm
  refine ModuleCat.isoMk eAdd ?_
  intro r
  ext (x : Γ(M, U))
  change
    (U.ι ≫ f).appTop.hom r •
        (M.restrictAppIso U.ι (⊤ : U.toScheme.Opens)).inv
          (M.presheaf.map (eqToHom U.ι_image_top).op x) =
      (M.restrictAppIso U.ι (⊤ : U.toScheme.Opens)).inv
        (M.presheaf.map (eqToHom U.ι_image_top).op
          (((X.presheaf.map
            ((initialOpOfTerminal isTerminalTop).to (op U))).hom
              (f.appTop.hom r)) • x))
  rw [M.map_smul]
  rw [smul_restrictAppIso_inv_apply]
  congr 1
  rw [Scheme.Hom.comp_appTop]
  have hr : (U.ι.appIso (⊤ : U.toScheme.Opens)).hom
      (X.presheaf.map (eqToHom U.ι_image_top).op
        ((X.presheaf.map
          ((initialOpOfTerminal isTerminalTop).to (op U))).hom
            (f.appTop.hom r))) =
      U.topIso.inv
        ((X.presheaf.map
          ((initialOpOfTerminal isTerminalTop).to (op U))).hom
            (f.appTop.hom r)) := by
    rw [Scheme.Opens.topIso_inv]
    rw [Scheme.Opens.ι_appIso]
    rfl
  rw [hr]
  rw [Scheme.Opens.topIso_inv]
  rw [Scheme.Opens.ι_appTop]
  have hmap :
      X.presheaf.map
          (homOfLE (x := U.ι ''ᵁ (⊤ : U.toScheme.Opens)) le_top).op =
        X.presheaf.map
            ((initialOpOfTerminal isTerminalTop).to (op U)) ≫
          X.presheaf.map (eqToHom U.ι_image_top).op := by
    rw [← Functor.map_comp]
    congr
  rw [hmap]
  rfl

/-- The Cech complex of a scheme module, retaining its module structure over
the global functions on the base.-/
noncomputable def baseCechComplex {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    CochainComplex (ModuleCat.{u} Γ(S, (⊤ : S.Opens))) ℕ :=
  (cechComplexFunctor U).obj (baseModulePresheaf π M)

/-- The base-linear Cech complex, functorially in the scheme module.-/
noncomputable def baseCechComplexFunctor {X S : Scheme.{u}} (π : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens) :
    X.Modules ⥤ CochainComplex (ModuleCat.{u} Γ(S, (⊤ : S.Opens))) ℕ :=
  baseModulePresheafFunctor π ⋙ cechComplexFunctor U

/--
@isnad1 id=eq.0h6v.s13.a8004cb373d1 from=translated src=- shape=326d4083 vocab=4f06cd2f
-/
@[simp]
theorem baseCechComplexFunctor_obj {X S : Scheme.{u}} (π : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens) (M : X.Modules) :
    (baseCechComplexFunctor π U).obj M = baseCechComplex π M U :=
  rfl

end

end AlgebraicGeometry.Scheme.Modules
