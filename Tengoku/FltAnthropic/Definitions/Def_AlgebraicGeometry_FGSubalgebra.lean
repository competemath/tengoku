import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

abbrev FGSubalgebra : Type u := {A₀ : Subalgebra R A // A₀.FG}

namespace FGSubalgebra

instance : Nonempty (FGSubalgebra R A) := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

instance : IsDirected (FGSubalgebra R A) (· ≤ ·) :=
  ⟨fun A₀ A₁ ↦ ⟨⟨A₀.1 ⊔ A₁.1, A₀.2.sup A₁.2⟩,
    (le_sup_left : A₀.1 ≤ A₀.1 ⊔ A₁.1), (le_sup_right : A₁.1 ≤ A₀.1 ⊔ A₁.1)⟩⟩

instance : IsFiltered (FGSubalgebra R A) := inferInstance

instance (A₀ : Subalgebra R A) : IsDirected {A₁ : FGSubalgebra R A // A₀ ≤ A₁.1} (· ≤ ·) :=
  ⟨fun A₁ A₂ ↦ ⟨⟨⟨A₁.1.1 ⊔ A₂.1.1, A₁.1.2.sup A₂.1.2⟩, A₁.2.trans (le_sup_left : A₁.1.1 ≤ _)⟩,
    (le_sup_left : A₁.1.1 ≤ A₁.1.1 ⊔ A₂.1.1), (le_sup_right : A₂.1.1 ≤ A₁.1.1 ⊔ A₂.1.1)⟩⟩

instance (A₀ : FGSubalgebra R A) : Nonempty {A₁ : FGSubalgebra R A // A₀.1 ≤ A₁.1} := ⟨⟨A₀, le_rfl⟩⟩

/--
@isnad1 id=nonempty.1h3v.s7.668f040f63fe from=translated src=- shape=93f51473 vocab=7ed83faf
-/
lemma nonempty_subtype_le (A₀ : Subalgebra R A) (h : A₀.FG) :
    Nonempty {A₁ : FGSubalgebra R A // A₀ ≤ A₁.1} := ⟨⟨⟨A₀, h⟩, le_rfl⟩⟩

instance : IsCofiltered (FGSubalgebra R A)ᵒᵖ := inferInstance

noncomputable def diagram : FGSubalgebra R A ⥤ CommRingCat.{u} where
  obj A₀ := CommRingCat.of A₀.1
  map {A₀ A₁} h := CommRingCat.ofHom (Subalgebra.inclusion (R := R) (show A₀.1 ≤ A₁.1 from h.le)).toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

noncomputable def cocone : Cocone (diagram R A) where
  pt := CommRingCat.of A
  ι := { app A₀ := CommRingCat.ofHom A₀.1.val.toRingHom
         naturality _ _ _ := by ext; rfl }

/--
@isnad1 id=eq.0h3v.s7.30735a24ac7e from=translated src=- shape=8ddb7674 vocab=5f68f055
-/
lemma diagram_obj (A₀ : FGSubalgebra R A) : (diagram R A).obj A₀ = CommRingCat.of A₀.1 := rfl

/--
@isnad1 id=eq.0h5v.s10.42f7ec9b52a4 from=translated src=- shape=6fbd7d61 vocab=dbabf08f
-/
lemma diagram_map {A₀ A₁ : FGSubalgebra R A} (h : A₀ ⟶ A₁) :
    (diagram R A).map h =
      CommRingCat.ofHom (Subalgebra.inclusion (R := R) (show A₀.1 ≤ A₁.1 from h.le)).toRingHom := rfl

/--
@isnad1 id=eq.0h2v.s6.1b769f064050 from=translated src=- shape=9d0d572a vocab=eb9bbaa8
-/
lemma cocone_pt : (cocone R A).pt = CommRingCat.of A := rfl

/--
@isnad1 id=eq.0h4v.s11.f1f2ebab4c12 from=translated src=- shape=3dc6c009 vocab=234d26c4
-/
@[simp] lemma cocone_ι_app_apply (A₀ : FGSubalgebra R A) (x : A₀.1) :
    (cocone R A).ι.app A₀ x = (x : A) := rfl

noncomputable def specDiagram : (FGSubalgebra R A)ᵒᵖ ⥤ Scheme.{u} :=
  (diagram R A).op ⋙ Scheme.Spec

noncomputable def specCone : Cone (specDiagram R A) :=
  Scheme.Spec.mapCone (cocone R A).op

noncomputable def specOver :
    specDiagram R A ⟶ (Functor.const _).obj (Spec (CommRingCat.of R)) where
  app i := Spec.map (CommRingCat.ofHom (algebraMap R i.unop.1))
  naturality i j f := by
    obtain ⟨A₁⟩ := i; obtain ⟨A₀⟩ := j
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    change (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (R := R)
        (show A₀.1 ≤ A₁.1 from f.unop.le)).toRingHom) : Spec (CommRingCat.of A₁.1) ⟶ Spec (CommRingCat.of A₀.1)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A₀.1)) = Spec.map (CommRingCat.ofHom (algebraMap R A₁.1))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2

/--
@isnad1 id=eq.0h3v.s8.258f84c61f6c from=translated src=- shape=73fbac91 vocab=78b24b67
-/
lemma specDiagram_obj (A₀ : FGSubalgebra R A) :
    (specDiagram R A).obj (op A₀) = Spec (CommRingCat.of A₀.1) := rfl

/--
@isnad1 id=eq.0h5v.s10.3135d9cd298c from=translated src=- shape=76f6d01f vocab=e8505e3b
-/
lemma specDiagram_map {A₀ A₁ : FGSubalgebra R A} (h : A₀ ⟶ A₁) :
    (specDiagram R A).map h.op =
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (R := R) (show A₀.1 ≤ A₁.1 from h.le)).toRingHom) :=
  rfl

/--
@isnad1 id=eq.0h2v.s7.fee13d66b502 from=translated src=- shape=ba28c71c vocab=69be5211
-/
lemma specCone_pt : (specCone R A).pt = Spec (CommRingCat.of A) := rfl

/--
@isnad1 id=eq.0h3v.s10.d68e4990f880 from=translated src=- shape=5644e303 vocab=529dc669
-/
lemma specOver_app (A₀ : FGSubalgebra R A) :
    (specOver R A).app (op A₀) = Spec.map (CommRingCat.ofHom (algebraMap R A₀.1)) := rfl

/--
@isnad1 id=eq.0h2v.s11.db0ca2e27e4a from=translated src=- shape=9e8b6fed vocab=c3951aab
-/
lemma specCone_π_comp_specOver :
    (specCone R A).π ≫ specOver R A =
      (Functor.const _).map (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  ext ⟨A₀⟩
  change (Spec.map (CommRingCat.ofHom A₀.1.val.toRingHom) : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A₀.1)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A₀.1)) = Spec.map (CommRingCat.ofHom (algebraMap R A))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

instance (i : (FGSubalgebra R A)ᵒᵖ) : IsAffine ((specDiagram R A).obj i) :=
  inferInstanceAs (IsAffine (Spec _))

instance (i : (FGSubalgebra R A)ᵒᵖ) : CompactSpace ((specDiagram R A).obj i) :=
  inferInstanceAs (CompactSpace (Spec _))

instance (i : (FGSubalgebra R A)ᵒᵖ) : QuasiSeparatedSpace ((specDiagram R A).obj i) :=
  inferInstanceAs (QuasiSeparatedSpace (Spec _))

instance {i j : (FGSubalgebra R A)ᵒᵖ} (f : i ⟶ j) : IsAffineHom ((specDiagram R A).map f) :=
  isAffineHom_of_isAffine _

end FGSubalgebra

end AlgebraicGeometry
