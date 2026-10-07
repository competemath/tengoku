/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Homology.HomologicalComplex

/-!
# Bicomplexes

Given a category `C` with zero morphisms and two complex shapes
`c₁ : ComplexShape I₁` and `c₂ : ComplexShape I₂`, we define
the type of bicomplexes `HomologicalComplex₂ C c₁ c₂` as an
abbreviation for `HomologicalComplex (HomologicalComplex C c₂) c₁`.
In particular, if `K : HomologicalComplex₂ C c₁ c₂`, then
for each `i₁ : I₁`, `K.X i₁` is a column of `K`.

In this file, we obtain the equivalence of categories
`HomologicalComplex₂.flipEquivalence : HomologicalComplex₂ C c₁ c₂ ≌ HomologicalComplex₂ C c₂ c₁`
which is obtained by exchanging the horizontal and vertical directions.

-/

@[expose] public section


open CategoryTheory Limits

variable (C : Type*) [Category* C] [HasZeroMorphisms C]
  {I₁ I₂ : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)

/-- Given a category `C` and two complex shapes `c₁` and `c₂` on types `I₁` and `I₂`,
the associated type of bicomplexes `HomologicalComplex₂ C c₁ c₂` is
`K : HomologicalComplex (HomologicalComplex C c₂) c₁`. Then, the object in
position `⟨i₁, i₂⟩` can be obtained as `(K.X i₁).X i₂`. -/
abbrev HomologicalComplex₂ :=
  HomologicalComplex (HomologicalComplex C c₂) c₁

namespace HomologicalComplex₂

open HomologicalComplex

variable {C c₁ c₂}

/-- The graded object indexed by `I₁ × I₂` induced by a bicomplex. -/
def toGradedObject (K : HomologicalComplex₂ C c₁ c₂) :
    GradedObject (I₁ × I₂) C :=
  fun ⟨i₁, i₂⟩ => (K.X i₁).X i₂

/-- The morphism of graded objects induced by a morphism of bicomplexes. -/
def toGradedObjectMap {K L : HomologicalComplex₂ C c₁ c₂} (φ : K ⟶ L) :
    K.toGradedObject ⟶ L.toGradedObject :=
  fun ⟨i₁, i₂⟩ => (φ.f i₁).f i₂

/--
@isnad1 id=eq.0h10v.s8.8edb4942f3e1 from=seed src=0 shape=3f05a370 vocab=5981bf09
-/
@[simp]
lemma toGradedObjectMap_apply {K L : HomologicalComplex₂ C c₁ c₂} (φ : K ⟶ L) (i₁ : I₁) (i₂ : I₂) :
    toGradedObjectMap φ ⟨i₁, i₂⟩ = (φ.f i₁).f i₂ := rfl

variable (C c₁ c₂) in
/-- The functor which sends a bicomplex to its associated graded object. -/
@[simps]
def toGradedObjectFunctor : HomologicalComplex₂ C c₁ c₂ ⥤ GradedObject (I₁ × I₂) C where
  obj K := K.toGradedObject
  map φ := toGradedObjectMap φ

instance : (toGradedObjectFunctor C c₁ c₂).Faithful where
  map_injective {_ _ φ₁ φ₂} h := by
    ext i₁ i₂
    exact congr_fun h ⟨i₁, i₂⟩

section OfGradedObject

variable (c₁ c₂)
variable (X : GradedObject (I₁ × I₂) C)
    (d₁ : ∀ (i₁ i₁' : I₁) (i₂ : I₂), X ⟨i₁, i₂⟩ ⟶ X ⟨i₁', i₂⟩)
    (d₂ : ∀ (i₁ : I₁) (i₂ i₂' : I₂), X ⟨i₁, i₂⟩ ⟶ X ⟨i₁, i₂'⟩)
    (shape₁ : ∀ (i₁ i₁' : I₁) (_ : ¬c₁.Rel i₁ i₁') (i₂ : I₂), d₁ i₁ i₁' i₂ = 0)
    (shape₂ : ∀ (i₁ : I₁) (i₂ i₂' : I₂) (_ : ¬c₂.Rel i₂ i₂'), d₂ i₁ i₂ i₂' = 0)
    (d₁_comp_d₁ : ∀ (i₁ i₁' i₁'' : I₁) (i₂ : I₂), d₁ i₁ i₁' i₂ ≫ d₁ i₁' i₁'' i₂ = 0)
    (d₂_comp_d₂ : ∀ (i₁ : I₁) (i₂ i₂' i₂'' : I₂), d₂ i₁ i₂ i₂' ≫ d₂ i₁ i₂' i₂'' = 0)
    (comm : ∀ (i₁ i₁' : I₁) (i₂ i₂' : I₂), d₁ i₁ i₁' i₂ ≫ d₂ i₁' i₂ i₂' =
      d₂ i₁ i₂ i₂' ≫ d₁ i₁ i₁' i₂')

/-- Constructor for bicomplexes taking as inputs a graded object, horizontal differentials
and vertical differentials satisfying suitable relations. -/
@[simps]
def ofGradedObject :
    HomologicalComplex₂ C c₁ c₂ where
  X i₁ :=
    { X := fun i₂ => X ⟨i₁, i₂⟩
      d := fun i₂ i₂' => d₂ i₁ i₂ i₂'
      shape := shape₂ i₁
      d_comp_d' := by intros; apply d₂_comp_d₂ }
  d i₁ i₁' :=
    { f := fun i₂ => d₁ i₁ i₁' i₂
      comm' := by intros; apply comm }
  shape i₁ i₁' h := by
    ext i₂
    exact shape₁ i₁ i₁' h i₂
  d_comp_d' i₁ i₁' i₁'' _ _ := by ext i₂; apply d₁_comp_d₁

/--
@isnad1 id=eq.5h8v.s9.710156781c80 from=seed src=0 shape=f1f25ded vocab=94033cbf
-/
@[simp]
lemma ofGradedObject_toGradedObject :
    (ofGradedObject c₁ c₂ X d₁ d₂ shape₁ shape₂ d₁_comp_d₁ d₂_comp_d₂ comm).toGradedObject = X :=
  rfl

end OfGradedObject

/-- Constructor for a morphism `K ⟶ L` in the category `HomologicalComplex₂ C c₁ c₂` which
takes as inputs a morphism `f : K.toGradedObject ⟶ L.toGradedObject` and
the compatibilities with both horizontal and vertical differentials. -/
@[simps!]
def homMk {K L : HomologicalComplex₂ C c₁ c₂}
    (f : K.toGradedObject ⟶ L.toGradedObject)
    (comm₁ : ∀ i₁ i₁' i₂, c₁.Rel i₁ i₁' →
      f ⟨i₁, i₂⟩ ≫ (L.d i₁ i₁').f i₂ = (K.d i₁ i₁').f i₂ ≫ f ⟨i₁', i₂⟩)
    (comm₂ : ∀ i₁ i₂ i₂', c₂.Rel i₂ i₂' →
      f ⟨i₁, i₂⟩ ≫ (L.X i₁).d i₂ i₂' = (K.X i₁).d i₂ i₂' ≫ f ⟨i₁, i₂'⟩) : K ⟶ L where
  f i₁ :=
    { f := fun i₂ => f ⟨i₁, i₂⟩
      comm' := comm₂ i₁ }
  comm' i₁ i₁' h₁ := by
    ext i₂
    exact comm₁ i₁ i₁' i₂ h₁

/--
@isnad1 id=eq.1h9v.s8.94c15d89e719 from=seed src=0 shape=ae0d6504 vocab=3314abce
-/
lemma shape_f (K : HomologicalComplex₂ C c₁ c₂) (i₁ i₁' : I₁) (h : ¬ c₁.Rel i₁ i₁') (i₂ : I₂) :
    (K.d i₁ i₁').f i₂ = 0 := by
  rw [K.shape _ _ h, zero_f]

/--
@isnad1 id=eq.0h10v.s9.09e6d6414bfd from=seed src=0 shape=d48a92ab vocab=b7ab55a0
-/
@[reassoc (attr := simp)]
lemma d_f_comp_d_f (K : HomologicalComplex₂ C c₁ c₂)
    (i₁ i₁' i₁'' : I₁) (i₂ : I₂) :
    (K.d i₁ i₁').f i₂ ≫ (K.d i₁' i₁'').f i₂ = 0 := by
  rw [← comp_f, d_comp_d, zero_f]

/--
@isnad1 id=eq.0h10v.s8.407c98562c25 from=seed src=0 shape=1b05e73f vocab=b7ab55a0
-/
@[reassoc]
lemma d_comm (K : HomologicalComplex₂ C c₁ c₂) (i₁ i₁' : I₁) (i₂ i₂' : I₂) :
    (K.d i₁ i₁').f i₂ ≫ (K.X i₁').d i₂ i₂' = (K.X i₁).d i₂ i₂' ≫ (K.d i₁ i₁').f i₂' := by
  simp

/--
@isnad1 id=eq.0h11v.s9.6eb478b199c4 from=seed src=0 shape=e3585d52 vocab=b7ab55a0
-/
@[reassoc (attr := simp)]
lemma comm_f {K L : HomologicalComplex₂ C c₁ c₂} (f : K ⟶ L) (i₁ i₁' : I₁) (i₂ : I₂) :
    (f.f i₁).f i₂ ≫ (L.d i₁ i₁').f i₂ = (K.d i₁ i₁').f i₂ ≫ (f.f i₁').f i₂ :=
  congr_hom (f.comm i₁ i₁') i₂

/-- Flip a complex of complexes over the diagonal,
exchanging the horizontal and vertical directions.
-/
@[simps]
def flip (K : HomologicalComplex₂ C c₁ c₂) : HomologicalComplex₂ C c₂ c₁ where
  X i :=
    { X := fun j => (K.X j).X i
      d := fun j j' => (K.d j j').f i
      shape := fun _ _ w => K.shape_f _ _ w i }
  d i i' := { f := fun j => (K.X j).d i i' }
  shape i i' w := by
    ext j
    exact (K.X j).shape i i' w

/--
@isnad1 id=eq.0h6v.s5.b28cbc0ddf48 from=seed src=0 shape=8348eb54 vocab=2d5377ce
-/
@[simp]
lemma flip_flip (K : HomologicalComplex₂ C c₁ c₂) : K.flip.flip = K := rfl

variable (C c₁ c₂)

set_option backward.defeqAttrib.useBackward true in
/-- Flipping a complex of complexes over the diagonal, as a functor. -/
@[simps]
def flipFunctor :
    HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex₂ C c₂ c₁ where
  obj K := K.flip
  map {K L} f :=
    { f := fun i =>
        { f := fun j => (f.f j).f i
          comm' := by intros; simp }
      comm' := by intros; ext; simp }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `HomologicalComplex₂.flipEquivalence`. -/
@[simps!]
def flipEquivalenceUnitIso :
    𝟭 (HomologicalComplex₂ C c₁ c₂) ≅ flipFunctor C c₁ c₂ ⋙ flipFunctor C c₂ c₁ :=
  NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun i₁ =>
    HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by simp)) (by cat_disch)) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `HomologicalComplex₂.flipEquivalence`. -/
@[simps!]
def flipEquivalenceCounitIso :
    flipFunctor C c₂ c₁ ⋙ flipFunctor C c₁ c₂ ≅ 𝟭 (HomologicalComplex₂ C c₂ c₁) :=
  NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun i₂ =>
    HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by simp)) (by cat_disch)) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Flipping a complex of complexes over the diagonal, as an equivalence of categories. -/
@[simps]
def flipEquivalence :
    HomologicalComplex₂ C c₁ c₂ ≌ HomologicalComplex₂ C c₂ c₁ where
  functor := flipFunctor C c₁ c₂
  inverse := flipFunctor C c₂ c₁
  unitIso := flipEquivalenceUnitIso C c₁ c₂
  counitIso := flipEquivalenceCounitIso C c₁ c₂

variable (K : HomologicalComplex₂ C c₁ c₂)

/-- The obvious isomorphism `(K.X x₁).X x₂ ≅ (K.X y₁).X y₂` when `x₁ = y₁` and `x₂ = y₂`. -/
def XXIsoOfEq {x₁ y₁ : I₁} (h₁ : x₁ = y₁) {x₂ y₂ : I₂} (h₂ : x₂ = y₂) :
    (K.X x₁).X x₂ ≅ (K.X y₁).X y₂ :=
  eqToIso (by subst h₁ h₂; rfl)

/--
@isnad1 id=eq.0h8v.s7.419d273a92d4 from=seed src=0 shape=ff8463b3 vocab=25a68d07
-/
@[simp]
lemma XXIsoOfEq_rfl (i₁ : I₁) (i₂ : I₂) :
    K.XXIsoOfEq _ _ _ (rfl : i₁ = i₁) (rfl : i₂ = i₂) = Iso.refl _ := rfl


end HomologicalComplex₂
