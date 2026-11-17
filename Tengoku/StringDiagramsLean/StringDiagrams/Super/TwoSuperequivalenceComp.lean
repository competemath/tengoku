import Tengoku.StringDiagramsLean.StringDiagrams.Super.TwoSuperequivalenceWhitehead

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 2-superequivalence is an equivalence relation

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 2.2. The paper uses without comment that being 2-superequivalent is symmetric and
transitive (e.g. in the proof of Corollary 5.6). We record:

* `Supercategory.Superequivalence.comp`: superequivalences of supercategories compose;
* `TwoSuperfunctor.isSuperequivalence_map`: a 2-superfunctor preserves superequivalence
  1-morphisms;
* `TwoSupercategory.Superequivalent.trans`: superequivalence of objects of a 2-supercategory is
  transitive (it is reflexive and symmetric by `Superequivalent.refl`, `Superequivalent.symm`);
* `TwoSuperfunctor.IsLocalTwoSuperequivalence.comp`: local 2-superequivalences (second
  formulation of Definition 2.2) compose;
* `TwoSuperfunctor.TwoSuperequivalent.symm`, `.trans` (first formulation;
  transitivity via the Whitehead theorem `twoSuperequivalent_iff_localTwoSuperequivalent`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w₁ v₁ u₁ w₂ v₂ u₂ w₃ v₃ u₃ w

variable {R : Type w} [CommRing R]

/-! ## Composition of superequivalences of supercategories -/

namespace Supercategory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C] [Supercategory R C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D] [Supercategory R D]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E] [Linear R E] [Supercategory R E]

/-- A superequivalence is an equivalence of the underlying categories.
@isnad1 id=isequiva.0h5v.s6.082ee433830a from=translated src=- shape=ca9cea12 vocab=fa630601
-/
theorem Superequivalence.isEquivalence {F : C ⥤ D} (e : Superequivalence R F) :
    F.IsEquivalence :=
  (CategoryTheory.Equivalence.mk F e.inverse e.unitIso e.counitIso).isEquivalence_functor

/-- **Brundan–Ellis, Definition 1.1(iv).** The composite of two superequivalences is a
superequivalence.-/
def Superequivalence.comp {F : C ⥤ D} [F.Additive] [F.Linear R] [IsSuperfunctor R F]
    {G : D ⥤ E} [G.Additive] [G.Linear R] [IsSuperfunctor R G] (e₁ : Superequivalence R F)
    (e₂ : Superequivalence R G) : Superequivalence R (F ⋙ G) :=
  haveI := e₁.isEquivalence
  haveI := e₂.isEquivalence
  Superequivalence.ofFullyFaithful _ fun Z =>
    ⟨e₁.inverse.obj (e₂.inverse.obj Z),
      G.mapIso (e₁.counitIso.app (e₂.inverse.obj Z)) ≪≫ e₂.counitIso.app Z, by
        simpa using comp_mem (map_mem G (e₁.counitIso_mem (e₂.inverse.obj Z)))
          (e₂.counitIso_mem Z)⟩

end Supercategory

variable {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]
  {D : Type u₃} [BicategoryStruct.{w₃, v₃} D]
  [∀ a b : D, Preadditive (a ⟶ b)] [∀ a b : D, Linear R (a ⟶ b)]
  [∀ a b : D, Supercategory R (a ⟶ b)] [TwoSupercategory R D]

/-! ## Superequivalent objects -/

namespace TwoSupercategory

open BicategoryStruct

variable {a b c : B}

variable (R) in
/-- Two 1-morphisms are isomorphic via an even 2-isomorphism (auxiliary).-/
def EvenlyIsomorphic (f g : a ⟶ b) : Prop := ∃ e : f ≅ g, e.hom ∈ parity (R := R) f g 0

namespace EvenlyIsomorphic

omit [TwoSupercategory R B] in
/--
@isnad1 id=evenlyis.2h7v.s7.95cd3b0e8657 from=translated src=- shape=03b678e6 vocab=99e29674
-/
theorem trans {f g h : a ⟶ b} (h₁ : EvenlyIsomorphic R f g) (h₂ : EvenlyIsomorphic R g h) :
    EvenlyIsomorphic R f h := by
  obtain ⟨e, he⟩ := h₁
  obtain ⟨e', he'⟩ := h₂
  exact ⟨e ≪≫ e', by simpa using comp_mem he he'⟩

omit [TwoSupercategory R B] in
/--
@isnad1 id=evenlyis.1h6v.s7.38ed7a8b860e from=translated src=- shape=41ed532f vocab=99e29674
-/
theorem symm {f g : a ⟶ b} (h : EvenlyIsomorphic R f g) : EvenlyIsomorphic R g f := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, inv_mem e he⟩

/--
@isnad1 id=evenlyis.1h8v.s7.823c94ed5769 from=translated src=- shape=b61981b0 vocab=436c02aa
-/
theorem whiskerLeft (f : a ⟶ b) {g h : b ⟶ c} (hgh : EvenlyIsomorphic R g h) :
    EvenlyIsomorphic R (f ≫ g) (f ≫ h) := by
  obtain ⟨e, he⟩ := hgh
  exact ⟨whiskerLeftIso (R := R) f e, whiskerLeft_mem f he⟩

/--
@isnad1 id=evenlyis.1h8v.s7.2051521dbf3c from=translated src=- shape=1de280c1 vocab=436c02aa
-/
theorem whiskerRight {f g : a ⟶ b} (hfg : EvenlyIsomorphic R f g) (h : b ⟶ c) :
    EvenlyIsomorphic R (f ≫ h) (g ≫ h) := by
  obtain ⟨e, he⟩ := hfg
  exact ⟨whiskerRightIso (R := R) e h, whiskerRight_mem h he⟩

variable (R) in
/--
@isnad1 id=evenlyis.0h9v.s7.ff6dab1a4eef from=translated src=- shape=cc8dd1a6 vocab=436c02aa
-/
theorem associator {d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    EvenlyIsomorphic R ((f ≫ g) ≫ h) (f ≫ g ≫ h) :=
  ⟨BicategoryStruct.associator f g h, associator_hom_mem (R := R) f g h⟩

variable (R) in
/--
@isnad1 id=evenlyis.0h5v.s7.358800cb9c2c from=translated src=- shape=a38f2741 vocab=de3a969a
-/
theorem leftUnitor (f : a ⟶ b) : EvenlyIsomorphic R (𝟙 a ≫ f) f :=
  ⟨BicategoryStruct.leftUnitor f, leftUnitor_hom_mem (R := R) f⟩

end EvenlyIsomorphic

/-- The composite of two superequivalence 1-morphisms is a superequivalence.
@isnad1 id=issupere.2h7v.s7.c5d8d1aeba41 from=translated src=- shape=54c43e9a vocab=f8e79159
-/
theorem IsSuperequivalence.comp {f : a ⟶ b} {g : b ⟶ c} (hf : IsSuperequivalence R f)
    (hg : IsSuperequivalence R g) : IsSuperequivalence R (f ≫ g) := by
  obtain ⟨f', e₁, e₂, h₁, h₂⟩ := hf
  obtain ⟨g', e₃, e₄, h₃, h₄⟩ := hg
  obtain ⟨E₁, hE₁⟩ : EvenlyIsomorphic R ((f ≫ g) ≫ g' ≫ f') (𝟙 a) :=
    (EvenlyIsomorphic.associator R _ _ _).trans <|
      (EvenlyIsomorphic.whiskerLeft f <| (EvenlyIsomorphic.associator R _ _ _).symm.trans <|
        (EvenlyIsomorphic.whiskerRight ⟨e₃, h₃⟩ f').trans (EvenlyIsomorphic.leftUnitor R f')).trans
        ⟨e₁, h₁⟩
  obtain ⟨E₂, hE₂⟩ : EvenlyIsomorphic R ((g' ≫ f') ≫ f ≫ g) (𝟙 c) :=
    (EvenlyIsomorphic.associator R _ _ _).trans <|
      (EvenlyIsomorphic.whiskerLeft g' <| (EvenlyIsomorphic.associator R _ _ _).symm.trans <|
        (EvenlyIsomorphic.whiskerRight ⟨e₂, h₂⟩ g).trans (EvenlyIsomorphic.leftUnitor R g)).trans
        ⟨e₄, h₄⟩
  exact ⟨g' ≫ f', E₁, E₂, hE₁, hE₂⟩

/-- **Brundan–Ellis, Definition 2.2.** Superequivalence of objects of a 2-supercategory is
transitive.
@isnad1 id=superequ.2h5v.s7.b1b11331fdc3 from=translated src=- shape=f350b1cd vocab=0dfe6ed8
-/
theorem Superequivalent.trans (h₁ : Superequivalent R a b) (h₂ : Superequivalent R b c) :
    Superequivalent R a c := by
  obtain ⟨f, hf⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  exact ⟨f ≫ g, hf.comp hg⟩

end TwoSupercategory

/-! ## 2-superequivalences -/

namespace TwoSuperfunctor

open TwoSupercategory

omit [TwoSupercategory R B] [TwoSupercategory R C] in
/-- A 2-superfunctor carries superequivalence 1-morphisms to superequivalence 1-morphisms.
@isnad1 id=issupere.1h7v.s8.2f196d32b1f2 from=translated src=- shape=04263ee9 vocab=4e6556fd
-/
theorem isSuperequivalence_map (F : TwoSuperfunctor R B C) {a b : B} {f : a ⟶ b}
    (hf : IsSuperequivalence R f) : IsSuperequivalence R (F.map f) := by
  obtain ⟨g, e₁, e₂, h₁, h₂⟩ := hf
  refine ⟨F.map g, F.mapComp f g ≪≫ F.map₂Iso e₁ ≪≫ (F.mapId a).symm,
    F.mapComp g f ≪≫ F.map₂Iso e₂ ≪≫ (F.mapId b).symm, ?_, ?_⟩
  · simpa using comp_mem (comp_mem (F.mapComp_hom_mem f g) (F.map₂_mem h₁))
      (inv_mem _ (F.mapId_hom_mem a))
  · simpa using comp_mem (comp_mem (F.mapComp_hom_mem g f) (F.map₂_mem h₂))
      (inv_mem _ (F.mapId_hom_mem b))

omit [TwoSupercategory R B] [TwoSupercategory R C] in
/-- A 2-superfunctor preserves superequivalence of objects.
@isnad1 id=superequ.1h6v.s7.43b4230ec7ad from=translated src=- shape=7cf83adf vocab=8e2688be
-/
theorem superequivalent_obj (F : TwoSuperfunctor R B C) {a b : B} (h : Superequivalent R a b) :
    Superequivalent R (F.obj a) (F.obj b) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨F.map f, F.isSuperequivalence_map hf⟩

omit [TwoSupercategory R B] [TwoSupercategory R C] in
/-- Local 2-superequivalences (second formulation of Definition 2.2) compose.
@isnad1 id=islocalt.2h6v.s8.e50be819e807 from=translated src=- shape=99501dc7 vocab=f9aa30cb
-/
theorem IsLocalTwoSuperequivalence.comp {F : TwoSuperfunctor R B C} {G : TwoSuperfunctor R C D}
    (hF : F.IsLocalTwoSuperequivalence) (hG : G.IsLocalTwoSuperequivalence) :
    (F.comp G).IsLocalTwoSuperequivalence where
  hom a b := ⟨(hF.hom a b).some.comp (hG.hom (F.obj a) (F.obj b)).some⟩
  essSurj d := by
    obtain ⟨c, hc⟩ := hG.essSurj d
    obtain ⟨a, ha⟩ := hF.essSurj c
    exact ⟨a, (G.superequivalent_obj ha).trans hc⟩

/-- Being 2-superequivalent (first formulation of Definition 2.2) is symmetric.
@isnad1 id=twosuper.1h3v.s7.691d79cda0dd from=translated src=- shape=c88994da vocab=63943111
-/
theorem TwoSuperequivalent.symm (h : TwoSuperequivalent R B C) : TwoSuperequivalent R C B := by
  obtain ⟨F, G, h₁, h₂⟩ := h
  exact ⟨G, F, h₂, h₁⟩

/-- Being 2-superequivalent (first formulation of Definition 2.2) is transitive.
@isnad1 id=twosuper.2h4v.s8.3f78e230baca from=translated src=- shape=f700f186 vocab=63943111
-/
theorem TwoSuperequivalent.trans (h₁ : TwoSuperequivalent R B C) (h₂ : TwoSuperequivalent R C D) :
    TwoSuperequivalent R B D := by
  obtain ⟨F, hF⟩ := h₁.localTwoSuperequivalent
  obtain ⟨G, hG⟩ := h₂.localTwoSuperequivalent
  exact LocalTwoSuperequivalent.twoSuperequivalent ⟨F.comp G, hF.comp hG⟩

end TwoSuperfunctor

end StringDiagrams

end
