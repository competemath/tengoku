import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe w v u

open CategoryTheory Category Limits Opposite

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)

abbrev presheafULift : MorphismProperty (Cᵒᵖ ⥤ Type (max w v)) := P.relative uliftYoneda.{w}

variable {P}

/--
@isnad1 id=le.0h1v.s7.1c108e93e173 from=translated src=- shape=1b869b44 vocab=a679dbe6
-/
lemma presheafULift_monomorphisms_le_monomorphisms :
    presheafULift.{w} (monomorphisms C) ≤ monomorphisms _ := fun F G f hf ↦ by
  suffices ∀ {X : C} {a b : uliftYoneda.{w}.obj X ⟶ F}, a ≫ f = b ≫ f → a = b from
    ⟨fun _ _ h ↦ hom_ext_uliftYoneda (fun _ _ ↦ this (by simp only [assoc, h]))⟩
  intro X a b h
  suffices hf.rep.lift (g := a ≫ f) a (𝟙 X) (by simp) =
      hf.rep.lift b (𝟙 X) (by simp [← h]) by
    simpa using uliftYoneda.{w}.congr_map this =≫ (hf.rep.fst (a ≫ f))
  have : Mono (hf.rep.snd (a ≫ f)) := hf.property_snd (a ≫ f)
  simp only [← cancel_mono (hf.rep.snd (a ≫ f)), Functor.relativelyRepresentable.lift_snd]

variable {G : Cᵒᵖ ⥤ Type (max w v)}

/--
@isnad1 id=mono.1h6v.s7.d37d04a3bff6 from=translated src=- shape=411c5b00 vocab=2b567fd2
-/
lemma presheafULift_mono_of_le (hP : P ≤ MorphismProperty.monomorphisms C)
    {X : C} {f : uliftYoneda.{w}.obj X ⟶ G} (hf : P.presheafULift f) : Mono f :=
  MorphismProperty.presheafULift_monomorphisms_le_monomorphisms _
    (MorphismProperty.relative_monotone hP _ hf)

/--
@isnad1 id=eq.1h6v.s8.a34b72b5f5b5 from=translated src=- shape=be3f4fcd vocab=c240a323
-/
lemma fst'_self_eq_snd_ULift (hP : P ≤ MorphismProperty.monomorphisms C)
    {X : C} {f : uliftYoneda.{w}.obj X ⟶ G} (hf : P.presheafULift f) : hf.rep.fst' f = hf.rep.snd f := by
  have := presheafULift_mono_of_le hP hf
  apply uliftYoneda.{w}.map_injective
  rw [← cancel_mono f, (hf.rep.isPullback' f).w]

/--
@isnad1 id=isiso.1h6v.s7.d53033907d22 from=translated src=- shape=dd67afea vocab=d7ab5845
-/
lemma isIso_fst'_self_ULift (hP : P ≤ MorphismProperty.monomorphisms C)
    {X : C} {f : uliftYoneda.{w}.obj X ⟶ G} (hf : P.presheafULift f) : IsIso (hf.rep.fst' f) :=
  have := presheafULift_mono_of_le hP hf
  have := (hf.rep.isPullback' f).isIso_fst_of_mono
  (ULiftYoneda.fullyFaithful C).isIso_of_isIso_map _

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

namespace Scheme

variable (F : Sheaf Scheme.zariskiTopology.{u} (Type (max w u)))
  {ι : Type u} {X : ι → Scheme.{u}}
  (f : (i : ι) → uliftYoneda.{w}.obj (X i) ⟶ F.obj) (hf : ∀ i, MorphismProperty.presheafULift.{w} @IsOpenImmersion (f i))

namespace LocalRepresentabilityULift

variable {F f} (i j k : ι)

set_option backward.isDefEq.respectTransparency false in
open Functor.relativelyRepresentable in

@[simps]
noncomputable def glueData : GlueData where
  J := ι
  U := X
  V := fun (i, j) ↦ (hf i).rep.pullback (f j)
  f i j := (hf i).rep.fst' (f j)
  f_mono i j :=
    have := (hf j).property _ _ _ ((hf i).1.isPullback' (f j)).flip
    IsOpenImmersion.mono _
  f_id i := MorphismProperty.isIso_fst'_self_ULift IsOpenImmersion.le_monomorphisms (hf i)
  t i j := (hf i).rep.symmetry (hf j).rep
  t_id i := by apply (hf i).rep.hom_ext' <;>
    simp [MorphismProperty.fst'_self_eq_snd_ULift IsOpenImmersion.le_monomorphisms (hf i)]
  t' i j k := lift₃ _ _ _ (pullback₃.p₂ _ _ _) (pullback₃.p₃ _ _ _) (pullback₃.p₁ _ _ _)
    (by simp) (by simp)
  t_fac i j k := (hf j).rep.hom_ext' (by simp) (by simp)
  cocycle i j k := pullback₃.hom_ext (by simp) (by simp) (by simp)
  f_open i j := (hf j).property _ _ _ ((hf i).1.isPullback' (f j)).flip

noncomputable def toGlued (i : ι) : X i ⟶ (glueData hf).glued :=
  (glueData hf).ι i

set_option backward.isDefEq.respectTransparency false in

noncomputable def uliftYonedaGluedToSheaf :
    (GrothendieckTopology.uliftYoneda.{w} zariskiTopology).obj (glueData hf).glued ⟶ F where
  hom := uliftYonedaEquiv.symm
    ((glueData hf).sheafValGluedMk (fun i ↦ uliftYonedaEquiv (f i)) (by
      intro (i : ι) (j : ι)
      dsimp only [glueData_V, glueData_J, glueData_U, glueData_f, glueData_t]
      rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_naturality]
      congr 1
      rw [← op_comp, Quiver.Hom.unop_op, Quiver.Hom.unop_op]
      erw [Functor.relativelyRepresentable.symmetry_fst, ((hf i).rep.isPullback' (f j)).w]))

/--
@isnad1 id=eq.0h6v.s8.1125c85ab927 from=translated src=- shape=fde27331 vocab=9009a7da
-/
@[reassoc (attr := simp)]
lemma uliftYoneda_toGlued_uliftYonedaGluedToSheaf (i : ι) :
    uliftYoneda.{w}.map (toGlued hf i) ≫ (uliftYonedaGluedToSheaf hf).hom = f i := by
  apply uliftYonedaEquiv.injective
  have h := uliftYonedaEquiv_naturality (uliftYonedaGluedToSheaf hf).hom (toGlued hf i).op
  rw [Quiver.Hom.unop_op] at h
  rw [← h]
  simp only [uliftYonedaGluedToSheaf, toGlued, Equiv.apply_symm_apply]
  exact GlueData.sheafValGluedMk_val _ _ _ _

/--
@isnad1 id=eq.0h9v.s11.1025e61bc0b6 from=translated src=- shape=21ade4e2 vocab=49cbc7f1
-/
@[simp]
lemma uliftYonedaGluedToSheaf_app_comp {V U : Scheme.{u}} (γ : V ⟶ U) (α : U ⟶ (glueData hf).glued) :
    dsimp% (uliftYonedaGluedToSheaf hf).hom.app (op V) ⟨γ ≫ α⟩ =
      F.obj.map γ.op ((uliftYonedaGluedToSheaf hf).hom.app (op U) ⟨α⟩) :=
  ConcreteCategory.congr_hom ((uliftYonedaGluedToSheaf hf).hom.naturality γ.op) ⟨α⟩

/--
@isnad1 id=eq.1h10v.s9.f4e8e1c34cd2 from=translated src=- shape=74504e23 vocab=b2834e63
-/
lemma comp_toGlued_eq {U : Scheme.{u}} {i j : ι} (a : U ⟶ X i) (b : U ⟶ X j)
    (h : uliftYoneda.{w}.map a ≫ f i = uliftYoneda.{w}.map b ≫ f j) :
    a ≫ toGlued hf i = b ≫ toGlued hf j := by
  rw [← (hf i).rep.lift'_fst a b h, assoc]
  conv_rhs => rw [← (hf i).rep.lift'_snd a b h, assoc]
  congr 1
  exact ((glueData hf).glue_condition i j).symm.trans
    (by simp [toGlued]; erw [Functor.relativelyRepresentable.symmetry_fst_assoc])

/--
@isnad1 id=eq.0h6v.s7.c468b51a70f9 from=translated src=- shape=af277ed8 vocab=19e4ff31
-/
@[simp]
lemma glueData_openCover_map : (glueData hf).openCover.f j = toGlued hf j := rfl

variable [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)]

end LocalRepresentabilityULift

end Scheme

end AlgebraicGeometry
