import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory Functor

namespace PresheafOfModules

section NatTrans

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F G H : C ⥤ D} {T : Cᵒᵖ ⥤ RingCat.{u}} {S : Dᵒᵖ ⥤ RingCat.{u}}
  (φ : T ⟶ G.op ⋙ S)

set_option backward.isDefEq.respectTransparency false in

noncomputable def pushforwardNatTrans (α : F ⟶ G) :
    pushforward.{v} φ ⟶ pushforward.{v} (F := F) (φ ≫ whiskerRight (NatTrans.op α) S) where
  app M :=
  { app U := (ModuleCat.restrictScalars (φ.app U).hom).map (M.map (α.app U.unop).op)
    naturality {U V} i := by
      ext x
      dsimp
      change (M.presheaf.map (G.map i.unop).op ≫ M.presheaf.map (α.app V.unop).op) _ =
        (M.presheaf.map (α.app U.unop).op ≫ M.presheaf.map (F.map i.unop).op) _
      simp only [← CategoryTheory.Functor.map_comp, ← op_comp, α.naturality] }
  naturality {M N} f := by
    ext U x
    exact congr($(f.naturality (α.app U.unop).op) x).symm

/--
@isnad1 id=eq.0h11v.s12.7221954cf708 from=translated src=- shape=d745a229 vocab=cdfa71ee
-/
@[simp] lemma pushforwardNatTrans_app_app_apply (α : F ⟶ G) (M : PresheafOfModules.{v} S) (U x) :
    ((pushforwardNatTrans φ α).app M).app U x = M.map (α.app U.unop).op x := rfl

noncomputable def pushforwardCongr {φ ψ : T ⟶ G.op ⋙ S} (e : φ = ψ) :
    pushforward.{v} φ ≅ pushforward.{v} ψ :=
  NatIso.ofComponents (fun M ↦ isoMk (fun U ↦ (ModuleCat.restrictScalarsCongr (by subst e; rfl)).app _)
      fun _ _ _ ↦ by subst e; rfl) fun _ ↦ by subst e; rfl

/--
@isnad1 id=eq.1h10v.s11.a5d40fb6f43e from=translated src=- shape=658b6b38 vocab=84f43e37
-/
@[simp] lemma pushforwardCongr_hom_app_app_apply {φ ψ : T ⟶ G.op ⋙ S} (e : φ = ψ)
    (M : PresheafOfModules.{v} S) (U x) :
    ((pushforwardCongr e).hom.app M).app U x = x := by subst e; rfl

/--
@isnad1 id=eq.1h10v.s11.2a1190c280e7 from=translated src=- shape=be3160f9 vocab=daf77f88
-/
@[simp] lemma pushforwardCongr_inv_app_app_apply {φ ψ : T ⟶ G.op ⋙ S} (e : φ = ψ)
    (M : PresheafOfModules.{v} S) (U x) :
    ((pushforwardCongr e).inv.app M).app U x = x := by subst e; rfl

end NatTrans

section Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C} {S : Cᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}}
  (adj : F ⊣ G) (φ : S ⟶ F.op ⋙ R) (ψ : R ⟶ G.op ⋙ S)
  (H₁ : whiskerRight (NatTrans.op adj.counit) R = ψ ≫ G.op.whiskerLeft φ)
  (H₂ : φ ≫ F.op.whiskerLeft ψ ≫ whiskerRight (NatTrans.op adj.unit) S = 𝟙 S)

set_option backward.isDefEq.respectTransparency false in

noncomputable def pushforwardPushforwardAdj : pushforward.{v} φ ⊣ pushforward.{v} ψ where
  unit :=
    (pushforwardId _).inv ≫ pushforwardNatTrans (𝟙 _) adj.counit ≫
      (pushforwardCongr (by simpa using H₁)).hom ≫ (pushforwardComp _ _).inv
  counit :=
    (pushforwardComp _ _).hom ≫ pushforwardNatTrans _ adj.unit ≫
      (pushforwardCongr (by simpa using H₂)).hom ≫ (pushforwardId _).hom
  left_triangle_components X := by
    ext U x
    change (X.presheaf.map (adj.counit.app (F.obj U.unop)).op ≫
      X.presheaf.map (F.map (adj.unit.app U.unop)).op) _ = _
    dsimp only [id_obj]
    rw [← Functor.map_comp, ← op_comp, adj.left_triangle_components]
    simp
  right_triangle_components X := by
    ext U x
    change (X.presheaf.map (G.map (adj.counit.app U.unop)).op ≫
      X.presheaf.map (adj.unit.app (G.obj U.unop)).op) _ = _
    rw [← Functor.map_comp, ← op_comp, adj.right_triangle_components]
    simp

/--
@isnad1 id=eq.2h12v.s13.8af4e703ae91 from=translated src=- shape=1f84fe12 vocab=7da68a78
-/
lemma pushforwardPushforwardAdj_unit_app_app_apply (M U x) :
    ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app M).app U x =
      M.map (adj.counit.app U.unop).op x := rfl

/--
@isnad1 id=eq.2h12v.s13.5b5be9b334eb from=translated src=- shape=fdefaefd vocab=7da68a78
-/
lemma pushforwardPushforwardAdj_counit_app_app_apply (M U x) :
    ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app M).app U x =
      M.map (adj.unit.app U.unop).op x := rfl

end Adjunction

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open TopologicalSpace

variable {X : Scheme.{u}} (U : X.Opens)

noncomputable def restrictPresheafRingHom :
    (U : Scheme.{u}).ringCatSheaf.obj ⟶ U.ι.opensFunctor.op ⋙ X.ringCatSheaf.obj := 𝟙 _

noncomputable def restrictPresheaf : X.PresheafOfModules ⥤ (U : Scheme.{u}).PresheafOfModules :=
  PresheafOfModules.pushforward.{u} (restrictPresheafRingHom U)

noncomputable def restrictPresheaf₀ : X.PresheafOfModules ⥤ (U : Scheme.{u}).PresheafOfModules :=
  PresheafOfModules.pushforward₀.{u} U.ι.opensFunctor X.ringCatSheaf.obj

noncomputable def restrictPresheafIsoRestrictPresheaf₀ : restrictPresheaf U ≅ restrictPresheaf₀ U := Iso.refl _

/--
@isnad1 id=eq.0h4v.s12.03d746b107e9 from=translated src=- shape=a0ecd63c vocab=2a241a51
-/
lemma restrictPresheaf_obj_obj (P : X.PresheafOfModules) (V : (U : Scheme.{u}).Opensᵒᵖ) :
    (((restrictPresheaf U).obj P).obj V : Type u) = P.obj (Opposite.op (U.ι ''ᵁ V.unop)) := rfl

noncomputable def restrictOpen : X.Modules ⥤ (U : Scheme.{u}).Modules :=
  SheafOfModules.pushforward.{u} (F := U.ι.opensFunctor) ⟨restrictPresheafRingHom U⟩

/--
@isnad1 id=eq.0h3v.s10.2914d701a020 from=translated src=- shape=1bf72ddb vocab=7c18624c
-/
lemma restrictOpen_obj_val (M : X.Modules) :
    ((restrictOpen U).obj M).val = (restrictPresheaf U).obj M.val := rfl

noncomputable def restrictOpenIsoRestrictFunctor : restrictOpen U ≅ Modules.restrictFunctor U.ι :=
  SheafOfModules.pushforwardCongr (by
    ext V x
    change x = (U.ι.appIso V.unop).inv x
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    rfl)

noncomputable def restrictOpenIsoPullback : restrictOpen U ≅ Modules.pullback U.ι :=
  restrictOpenIsoRestrictFunctor U ≪≫ Modules.restrictFunctorIsoPullback U.ι

end AlgebraicGeometry.Scheme.Modules
