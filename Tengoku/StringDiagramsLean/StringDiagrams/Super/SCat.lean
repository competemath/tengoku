import Tengoku.StringDiagramsLean.StringDiagrams.Super.FunctorCategory
import Tengoku.StringDiagramsLean.StringDiagrams.Super.Bicategory
import Tengoku.StringDiagramsLean.StringDiagrams.Super.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The strict 2-supercategories `𝔖ℭ𝔞𝔱` and `Π-𝔖ℭ𝔞𝔱`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Section 2 (after Definition 2.1) and Section 3 (before Lemma 3.2).

`SCat R` is the type of (small, in fixed universes) supercategories over `R`: an `R`-linear
category with a supercategory structure (`StringDiagrams.Supercategory`). It is a strict
2-supercategory (in the unpacked form `TwoSupercategory` of Definition 2.2(i), with
`BicategoryStruct.Strict`, i.e. Definition 2.1):

* the morphism supercategories are the supercategories `ℋom(A, B)` of superfunctors and
  supernatural transformations (`Supercategory.Superfunctor R A B`, Example 1.2(iv));
* horizontal composition of 1-morphisms is composition of superfunctors (`G F := G ∘ F`, in
  diagrammatic order `F ≫ G`);
* horizontal composition of supernatural transformations is
  `(yx)_λ := y_{Hλ} ∘ G x_λ` (`Superfunctor.hcomp`), obtained from the whiskerings
  `Superfunctor.whiskerLeft` and `Superfunctor.whiskerRight`;
* the associator and unitors are identities, and the super interchange law is
  `Superfunctor.whisker_exchange`.

`PiSCat R` is the type of Π-supercategories (Definition 1.7). With superfunctors and
supernatural transformations it is the strict 2-supercategory `Π-𝔖ℭ𝔞𝔱`; its Π-2-supercategory
structure (Definition 3.1) is in `StringDiagrams.Super.PiTwo`.

## Main definitions

* `SCat R`, with instances `BicategoryStruct (SCat R)`, `TwoSupercategory R (SCat R)` and
  `BicategoryStruct.Strict (SCat R)`.
* `PiSCat R`, with the same instances.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w v u

variable (R : Type w) [CommRing R]

/-- A supercategory over `R` (Brundan–Ellis, Definition 1.1(i)), bundled: an `R`-linear
category `carrier` with a supercategory structure.-/
structure SCat where
  /-- The objects.-/
  carrier : Type u
  [str : Category.{v} carrier]
  [preadditive : Preadditive carrier]
  [linear : Linear R carrier]
  [super : Supercategory R carrier]

namespace SCat

attribute [instance] str preadditive linear super

variable {R}

instance : CoeSort (SCat.{w, v, u} R) (Type u) := ⟨SCat.carrier⟩

variable (R) in
/-- The bundled supercategory of a supercategory.-/
abbrev of (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C] [Supercategory R C] :
    SCat.{w, v, u} R :=
  ⟨C⟩

/-- The horizontal composition data of `𝔖ℭ𝔞𝔱`: superfunctors, supernatural transformations,
their whiskerings, and identity coherence maps.-/
instance : BicategoryStruct.{max u v, max u v} (SCat.{w, v, u} R) where
  Hom A B := Superfunctor R A B
  id A := Superfunctor.id R A
  comp F G := F.comp G
  homCategory _ _ := inferInstance
  whiskerLeft F _ _ y := Superfunctor.whiskerLeft F y
  whiskerRight x G := Superfunctor.whiskerRight x G
  associator F G H := Iso.refl (F.comp (G.comp H))
  leftUnitor F := Iso.refl F
  rightUnitor F := Iso.refl F

instance (A B : SCat.{w, v, u} R) : Preadditive (A ⟶ B) :=
  inferInstanceAs (Preadditive (Superfunctor R A B))

instance (A B : SCat.{w, v, u} R) : Linear R (A ⟶ B) :=
  inferInstanceAs (Linear R (Superfunctor R A B))

instance (A B : SCat.{w, v, u} R) : Supercategory R (A ⟶ B) :=
  inferInstanceAs (Supercategory R (Superfunctor R A B))

open BicategoryStruct

/--
@isnad1 id=eq.0h3v.s6.cdea62c44b97 from=translated src=- shape=e2574bf3 vocab=643bba6e
-/
theorem hom_def (A B : SCat.{w, v, u} R) : (A ⟶ B) = Superfunctor R A B := rfl

/--
@isnad1 id=eq.0h6v.s7.7256b2dbc700 from=translated src=- shape=890ca8ed vocab=13ac7bed
-/
theorem comp_def {A B C : SCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C) : F ≫ G = F.comp G := rfl

/--
@isnad1 id=eq.0h2v.s5.8bf202409d47 from=translated src=- shape=115edee1 vocab=cd9ca3d7
-/
theorem id_def (A : SCat.{w, v, u} R) : 𝟙 A = Superfunctor.id R A := rfl

/--
@isnad1 id=eq.0h8v.s8.023185dba790 from=translated src=- shape=af9f796d vocab=c3494009
-/
theorem whiskerLeft_def {A B C : SCat.{w, v, u} R} (F : A ⟶ B) {G K : B ⟶ C} (y : G ⟶ K) :
    F ◁ y = Superfunctor.whiskerLeft F y := rfl

/--
@isnad1 id=eq.0h8v.s8.a9502d4c8f9c from=translated src=- shape=a49d649d vocab=a5adec56
-/
theorem whiskerRight_def {A B C : SCat.{w, v, u} R} {F H : A ⟶ B} (x : F ⟶ H) (G : B ⟶ C) :
    x ▷ G = Superfunctor.whiskerRight x G := rfl

/--
@isnad1 id=eq.0h8v.s8.491c642dc38c from=translated src=- shape=019c06be vocab=0004058d
-/
@[simp] theorem associator_hom {A B C D : SCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C)
    (H : C ⟶ D) : (associator F G H).hom = 𝟙 (F ≫ G ≫ H) := rfl

/--
@isnad1 id=eq.0h8v.s8.44599957495e from=translated src=- shape=d6acb92e vocab=ff9f3443
-/
@[simp] theorem associator_inv {A B C D : SCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C)
    (H : C ⟶ D) : (associator F G H).inv = 𝟙 (F ≫ G ≫ H) := rfl

/--
@isnad1 id=eq.0h4v.s7.6f32c4038d9b from=translated src=- shape=4a3d7ab8 vocab=5398e79e
-/
@[simp] theorem leftUnitor_hom {A B : SCat.{w, v, u} R} (F : A ⟶ B) :
    (leftUnitor F).hom = 𝟙 F := rfl

/--
@isnad1 id=eq.0h4v.s7.f1c0c776a70c from=translated src=- shape=342726aa vocab=3d50bd8f
-/
@[simp] theorem leftUnitor_inv {A B : SCat.{w, v, u} R} (F : A ⟶ B) :
    (leftUnitor F).inv = 𝟙 F := rfl

/--
@isnad1 id=eq.0h4v.s7.4c6f69a9b28c from=translated src=- shape=2929adf1 vocab=ebc87f28
-/
@[simp] theorem rightUnitor_hom {A B : SCat.{w, v, u} R} (F : A ⟶ B) :
    (rightUnitor F).hom = 𝟙 F := rfl

/--
@isnad1 id=eq.0h4v.s7.fb2c9b2a6f9c from=translated src=- shape=14a7ed85 vocab=6bf2196c
-/
@[simp] theorem rightUnitor_inv {A B : SCat.{w, v, u} R} (F : A ⟶ B) :
    (rightUnitor F).inv = 𝟙 F := rfl

section App

variable {A B C : SCat.{w, v, u} R}

/--
@isnad1 id=eq.0h9v.s11.90c5a1e96a0f from=translated src=- shape=2bd02d0e vocab=102449f1
-/
@[simp] theorem comp_app_zero {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H) (X : A.carrier) :
    (x ≫ y).app 0 X = x.app 0 X ≫ y.app 0 X + x.app 1 X ≫ y.app 1 X :=
  Superfunctor.comp_app_zero x y X

/--
@isnad1 id=eq.0h9v.s11.035c2943054c from=translated src=- shape=2bd02d0e vocab=102449f1
-/
@[simp] theorem comp_app_one {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H) (X : A.carrier) :
    (x ≫ y).app 1 X = x.app 0 X ≫ y.app 1 X + x.app 1 X ≫ y.app 0 X :=
  Superfunctor.comp_app_one x y X

/--
@isnad1 id=eq.0h10v.s11.0fe65b0ca0cd from=translated src=- shape=8425a693 vocab=102449f1
-/
theorem comp_app {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H) (r : ZMod 2) (X : A.carrier) :
    (x ≫ y).app r X = x.app 0 X ≫ y.app r X + x.app 1 X ≫ y.app (r + 1) X := rfl

/--
@isnad1 id=eq.0h5v.s8.0cd865193672 from=translated src=- shape=8d9c20c4 vocab=6263d034
-/
@[simp] theorem id_app_zero (F : A ⟶ B) (X : A.carrier) :
    (𝟙 F : F ⟶ F).app 0 X = 𝟙 (F.obj X) := rfl

/--
@isnad1 id=eq.0h5v.s9.07923bfffddd from=translated src=- shape=80b251e0 vocab=1252eb03
-/
@[simp] theorem id_app_one (F : A ⟶ B) (X : A.carrier) : (𝟙 F : F ⟶ F).app 1 X = 0 := rfl

/--
@isnad1 id=eq.0h9v.s11.883177f07a3f from=translated src=- shape=1db123b2 vocab=488c5eed
-/
@[simp] theorem add_app {F G : A ⟶ B} (x y : F ⟶ G) (p : ZMod 2) (X : A.carrier) :
    (x + y).app p X = x.app p X + y.app p X := rfl

/--
@isnad1 id=eq.0h8v.s10.edf5009afab2 from=translated src=- shape=db6bfec8 vocab=f05b82b6
-/
@[simp] theorem neg_app {F G : A ⟶ B} (x : F ⟶ G) (p : ZMod 2) (X : A.carrier) :
    (-x).app p X = -x.app p X := rfl

/--
@isnad1 id=eq.0h9v.s12.6e0e2e363952 from=translated src=- shape=c0bd3939 vocab=f639de60
-/
@[simp] theorem smul_app {F G : A ⟶ B} (r : R) (x : F ⟶ G) (p : ZMod 2) (X : A.carrier) :
    (r • x).app p X = r • x.app p X := rfl

/--
@isnad1 id=eq.0h7v.s9.5be24136dce7 from=translated src=- shape=871b0eeb vocab=d70b450d
-/
@[simp] theorem zero_app {F G : A ⟶ B} (p : ZMod 2) (X : A.carrier) :
    (0 : F ⟶ G).app p X = 0 := rfl

/--
@isnad1 id=eq.0h10v.s9.90984cbad2fe from=translated src=- shape=0f9c329d vocab=2c6c8b75
-/
@[simp] theorem whiskerLeft_app (F : A ⟶ B) {G K : B ⟶ C} (y : G ⟶ K) (p : ZMod 2)
    (X : A.carrier) : (F ◁ y).app p X = y.app p (F.obj X) := rfl

/--
@isnad1 id=eq.0h10v.s9.6640b16752ea from=translated src=- shape=dcbe1f5d vocab=6f0ab06d
-/
@[simp] theorem whiskerRight_app {F H : A ⟶ B} (x : F ⟶ H) (G : B ⟶ C) (p : ZMod 2)
    (X : A.carrier) : (x ▷ G).app p X = G.map (x.app p X) := rfl

/--
@isnad1 id=eq.0h7v.s7.5f0f7c37c2ce from=translated src=- shape=21525f8e vocab=40315f3d
-/
@[simp] theorem comp_obj (F : A ⟶ B) (G : B ⟶ C) (X : A.carrier) :
    Superfunctor.obj (F ≫ G) X = G.obj (F.obj X) := rfl

/--
@isnad1 id=eq.0h9v.s8.4c560bf14648 from=translated src=- shape=ee34d3af vocab=36392ab2
-/
@[simp] theorem comp_map (F : A ⟶ B) (G : B ⟶ C) {X Y : A.carrier} (f : X ⟶ Y) :
    Superfunctor.map (F ≫ G) f = G.map (F.map f) := rfl

/--
@isnad1 id=eq.0h3v.s6.1849c9f341d8 from=translated src=- shape=d4621898 vocab=7cb5cb6e
-/
@[simp] theorem id_obj (X : A.carrier) : Superfunctor.obj (𝟙 A) X = X := rfl

/--
@isnad1 id=eq.0h5v.s7.a90cc2e102b2 from=translated src=- shape=967195be vocab=4d3aab42
-/
@[simp] theorem id_map {X Y : A.carrier} (f : X ⟶ Y) : Superfunctor.map (𝟙 A) f = f := rfl

/--
@isnad1 id=eq.2h7v.s10.b4d523717ef0 from=translated src=- shape=62f36f2d vocab=d70b450d
-/
theorem hom_ext {F G : A ⟶ B} {x y : F ⟶ G} (h0 : ∀ X, x.app 0 X = y.app 0 X)
    (h1 : ∀ X, x.app 1 X = y.app 1 X) : x = y :=
  Superfunctor.hom_ext_parity h0 h1

end App

set_option backward.isDefEq.respectTransparency false in
/-- **Brundan–Ellis, Section 2.** Supercategories, superfunctors and supernatural
transformations form a 2-supercategory `𝔖ℭ𝔞𝔱`.-/
instance : TwoSupercategory R (SCat.{w, v, u} R) where
  whiskerLeft_id F G := Superfunctor.whiskerLeft_id F G
  whiskerLeft_comp F _ _ _ y z := Superfunctor.whiskerLeft_comp F y z
  id_whiskerLeft y := by
    rw [leftUnitor_hom, leftUnitor_inv]; erw [Category.id_comp, Category.comp_id]; rfl
  comp_whiskerLeft F G _ _ y := by
    rw [associator_hom, associator_inv]; erw [Category.id_comp, Category.comp_id]; rfl
  id_whiskerRight F G := Superfunctor.id_whiskerRight F G
  comp_whiskerRight x z G := Superfunctor.comp_whiskerRight x z G
  whiskerRight_id x := by
    rw [rightUnitor_hom, rightUnitor_inv]; erw [Category.id_comp, Category.comp_id]
    exact Superfunctor.hom_ext fun _ _ => rfl
  whiskerRight_comp x G H := by
    rw [associator_hom, associator_inv]; erw [Category.id_comp, Category.comp_id]; rfl
  whisker_assoc F _ _ y H := by
    rw [associator_hom, associator_inv]; erw [Category.id_comp, Category.comp_id]; rfl
  pentagon F G H K := by
    simp only [associator_hom]; erw [Category.id_comp]
    change Superfunctor.whiskerRight (𝟙 (F.comp (G.comp H))) K ≫
      Superfunctor.whiskerLeft F (𝟙 (G.comp (H.comp K))) =
      Superfunctor.whiskerLeft F (𝟙 (G.comp (H.comp K)))
    rw [Superfunctor.id_whiskerRight, Superfunctor.whiskerLeft_id, Category.id_comp]
  triangle F G := by
    simp only [associator_hom, leftUnitor_hom, rightUnitor_hom]; erw [Category.id_comp]
    exact (Superfunctor.whiskerLeft_id F G).trans (Superfunctor.id_whiskerRight F G).symm
  whiskerLeft_add F _ _ y z := Superfunctor.whiskerLeft_add F y z
  add_whiskerRight x z G := Superfunctor.add_whiskerRight x z G
  whiskerLeft_smul F _ _ r y := Superfunctor.whiskerLeft_smul F r y
  smul_whiskerRight r x G := Superfunctor.smul_whiskerRight r x G
  whiskerLeft_mem F _ _ _ _ hy := Superfunctor.whiskerLeft_mem F hy
  whiskerRight_mem G hx := Superfunctor.whiskerRight_mem hx G
  super_interchange hx hy := Superfunctor.whisker_exchange hx hy
  associator_hom_mem _ _ _ := id_mem _
  leftUnitor_hom_mem _ := id_mem _
  rightUnitor_hom_mem _ := id_mem _

end SCat

/-! ## Π-supercategories -/

/-- A Π-supercategory over `R` (Brundan–Ellis, Definition 1.7), bundled.-/
structure PiSCat extends SCat.{w, v, u} R where
  [pi : PiSupercategory R carrier]

namespace PiSCat

attribute [instance] pi

variable {R}

instance : CoeSort (PiSCat.{w, v, u} R) (Type u) := ⟨fun A => A.carrier⟩

variable (R) in
/-- The bundled Π-supercategory of a Π-supercategory.-/
abbrev of (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C] [Supercategory R C]
    [PiSupercategory R C] : PiSCat.{w, v, u} R :=
  ⟨SCat.of R C⟩

open BicategoryStruct

/-- The data of the 2-supercategory `Π-𝔖ℭ𝔞𝔱` of Π-supercategories, superfunctors and
supernatural transformations: that of `𝔖ℭ𝔞𝔱` on the underlying supercategories.-/
instance : BicategoryStruct.{max u v, max u v} (PiSCat.{w, v, u} R) where
  Hom A B := A.toSCat ⟶ B.toSCat
  id A := 𝟙 A.toSCat
  comp F G := F ≫ G
  homCategory A B := inferInstanceAs (Category (A.toSCat ⟶ B.toSCat))
  whiskerLeft F _ _ y := F ◁ y
  whiskerRight x G := x ▷ G
  associator F G H := associator (B := SCat R) F G H
  leftUnitor F := leftUnitor (B := SCat R) F
  rightUnitor F := rightUnitor (B := SCat R) F

instance (A B : PiSCat.{w, v, u} R) : Preadditive (A ⟶ B) :=
  inferInstanceAs (Preadditive (A.toSCat ⟶ B.toSCat))

instance (A B : PiSCat.{w, v, u} R) : Linear R (A ⟶ B) :=
  inferInstanceAs (Linear R (A.toSCat ⟶ B.toSCat))

instance (A B : PiSCat.{w, v, u} R) : Supercategory R (A ⟶ B) :=
  inferInstanceAs (Supercategory R (A.toSCat ⟶ B.toSCat))

/--
@isnad1 id=eq.0h3v.s6.783b2271f5e5 from=translated src=- shape=68bfd8f2 vocab=13ea2838
-/
theorem hom_def (A B : PiSCat.{w, v, u} R) : (A ⟶ B) = Superfunctor R A B := rfl

/--
@isnad1 id=eq.0h6v.s7.a2c342eba1b5 from=translated src=- shape=295ff44a vocab=1f48d804
-/
theorem comp_def {A B C : PiSCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C) :
    F ≫ G = Superfunctor.comp F G := rfl

/--
@isnad1 id=eq.0h2v.s6.be5d8dd85a30 from=translated src=- shape=7f96a4f9 vocab=15195009
-/
theorem id_def (A : PiSCat.{w, v, u} R) : 𝟙 A = Superfunctor.id R A := rfl

/--
@isnad1 id=eq.0h8v.s8.e1987d10818f from=translated src=- shape=1db021ba vocab=966d7de5
-/
theorem whiskerLeft_def {A B C : PiSCat.{w, v, u} R} (F : A ⟶ B) {G K : B ⟶ C} (y : G ⟶ K) :
    F ◁ y = Superfunctor.whiskerLeft F y := rfl

/--
@isnad1 id=eq.0h8v.s8.ee077e7a75b5 from=translated src=- shape=644b4a85 vocab=e7997e76
-/
theorem whiskerRight_def {A B C : PiSCat.{w, v, u} R} {F H : A ⟶ B} (x : F ⟶ H)
    (G : B ⟶ C) : x ▷ G = Superfunctor.whiskerRight x G := rfl

section App

variable {A B C : PiSCat.{w, v, u} R}

/--
@isnad1 id=eq.0h9v.s12.1f70825597fb from=translated src=- shape=7053f685 vocab=8000003c
-/
@[simp] theorem comp_app_zero {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H) (X : A.carrier) :
    (x ≫ y).app 0 X = x.app 0 X ≫ y.app 0 X + x.app 1 X ≫ y.app 1 X :=
  Superfunctor.comp_app_zero x y X

/--
@isnad1 id=eq.0h9v.s12.6563a89d8edc from=translated src=- shape=7053f685 vocab=8000003c
-/
@[simp] theorem comp_app_one {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H) (X : A.carrier) :
    (x ≫ y).app 1 X = x.app 0 X ≫ y.app 1 X + x.app 1 X ≫ y.app 0 X :=
  Superfunctor.comp_app_one x y X

/--
@isnad1 id=eq.0h10v.s12.df0463e0ca5c from=translated src=- shape=493e3843 vocab=8000003c
-/
theorem comp_app {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H) (r : ZMod 2) (X : A.carrier) :
    (x ≫ y).app r X = x.app 0 X ≫ y.app r X + x.app 1 X ≫ y.app (r + 1) X := rfl

/--
@isnad1 id=eq.0h5v.s9.83b820c3955f from=translated src=- shape=269ae4db vocab=82a829e1
-/
@[simp] theorem id_app_zero (F : A ⟶ B) (X : A.carrier) :
    (𝟙 F : F ⟶ F).app 0 X = 𝟙 (F.obj X) := rfl

/--
@isnad1 id=eq.0h5v.s10.7e292d4fe153 from=translated src=- shape=aede4c6d vocab=ea2def87
-/
@[simp] theorem id_app_one (F : A ⟶ B) (X : A.carrier) : (𝟙 F : F ⟶ F).app 1 X = 0 := rfl

/--
@isnad1 id=eq.0h9v.s11.015d06165e70 from=translated src=- shape=6c541ea5 vocab=b0226707
-/
@[simp] theorem add_app {F G : A ⟶ B} (x y : F ⟶ G) (p : ZMod 2) (X : A.carrier) :
    (x + y).app p X = x.app p X + y.app p X := rfl

/--
@isnad1 id=eq.0h8v.s11.1f38413b4c6f from=translated src=- shape=cbe95a53 vocab=7fddcbd2
-/
@[simp] theorem neg_app {F G : A ⟶ B} (x : F ⟶ G) (p : ZMod 2) (X : A.carrier) :
    (-x).app p X = -x.app p X := rfl

/--
@isnad1 id=eq.0h9v.s13.f259d2db8594 from=translated src=- shape=4971ece3 vocab=61ebf5f1
-/
@[simp] theorem smul_app {F G : A ⟶ B} (r : R) (x : F ⟶ G) (p : ZMod 2) (X : A.carrier) :
    (r • x).app p X = r • x.app p X := rfl

/--
@isnad1 id=eq.0h7v.s10.9e2465f2e2e2 from=translated src=- shape=ba37c9dc vocab=01c577d6
-/
@[simp] theorem zero_app {F G : A ⟶ B} (p : ZMod 2) (X : A.carrier) :
    (0 : F ⟶ G).app p X = 0 := rfl

/--
@isnad1 id=eq.0h10v.s9.5eb8cfc6d9d2 from=translated src=- shape=f6956f75 vocab=62914c05
-/
@[simp] theorem whiskerLeft_app (F : A ⟶ B) {G K : B ⟶ C} (y : G ⟶ K) (p : ZMod 2)
    (X : A.carrier) : (F ◁ y).app p X = y.app p (F.obj X) := rfl

/--
@isnad1 id=eq.0h10v.s10.c55745de66b3 from=translated src=- shape=ad62ce15 vocab=20ed89af
-/
@[simp] theorem whiskerRight_app {F H : A ⟶ B} (x : F ⟶ H) (G : B ⟶ C) (p : ZMod 2)
    (X : A.carrier) : (x ▷ G).app p X = G.map (x.app p X) := rfl

/--
@isnad1 id=eq.0h7v.s8.5df96bc1a230 from=translated src=- shape=7131e5ae vocab=04543bdc
-/
@[simp] theorem comp_obj (F : A ⟶ B) (G : B ⟶ C) (X : A.carrier) :
    Superfunctor.obj (F ≫ G) X = G.obj (F.obj X) := rfl

/--
@isnad1 id=eq.0h9v.s9.3eaed5e94605 from=translated src=- shape=5ee2a2bb vocab=bf1d49d9
-/
@[simp] theorem comp_map (F : A ⟶ B) (G : B ⟶ C) {X Y : A.carrier} (f : X ⟶ Y) :
    Superfunctor.map (F ≫ G) f = G.map (F.map f) := rfl

/--
@isnad1 id=eq.0h3v.s6.c0971c885fee from=translated src=- shape=d2a9ac3d vocab=19895a8b
-/
@[simp] theorem id_obj (X : A.carrier) : Superfunctor.obj (𝟙 A) X = X := rfl

/--
@isnad1 id=eq.0h5v.s8.f92a76c77ea0 from=translated src=- shape=61431faf vocab=e4e990e4
-/
@[simp] theorem id_map {X Y : A.carrier} (f : X ⟶ Y) : Superfunctor.map (𝟙 A) f = f := rfl

/--
@isnad1 id=eq.2h7v.s10.a32cc2968816 from=translated src=- shape=ebb592f6 vocab=01c577d6
-/
theorem hom_ext {F G : A ⟶ B} {x y : F ⟶ G} (h0 : ∀ X, x.app 0 X = y.app 0 X)
    (h1 : ∀ X, x.app 1 X = y.app 1 X) : x = y :=
  Superfunctor.hom_ext_parity h0 h1

end App

/-- **Brundan–Ellis, Section 3.** Π-supercategories, superfunctors and supernatural
transformations form a 2-supercategory `Π-𝔖ℭ𝔞𝔱`.-/
instance : TwoSupercategory R (PiSCat.{w, v, u} R) where
  whiskerLeft_id F G := TwoSupercategory.whiskerLeft_id (R := R) (B := SCat R) F G
  whiskerLeft_comp F _ _ _ y z := TwoSupercategory.whiskerLeft_comp (R := R) (B := SCat R) F y z
  id_whiskerLeft y := TwoSupercategory.id_whiskerLeft (R := R) (B := SCat R) y
  comp_whiskerLeft F G _ _ y := TwoSupercategory.comp_whiskerLeft (R := R) (B := SCat R) F G y
  id_whiskerRight F G := TwoSupercategory.id_whiskerRight (R := R) (B := SCat R) F G
  comp_whiskerRight x z G := TwoSupercategory.comp_whiskerRight (R := R) (B := SCat R) x z G
  whiskerRight_id x := TwoSupercategory.whiskerRight_id (R := R) (B := SCat R) x
  whiskerRight_comp x G H := TwoSupercategory.whiskerRight_comp (R := R) (B := SCat R) x G H
  whisker_assoc F _ _ y H := TwoSupercategory.whisker_assoc (R := R) (B := SCat R) F y H
  pentagon F G H K := TwoSupercategory.pentagon (R := R) (B := SCat R) F G H K
  triangle F G := TwoSupercategory.triangle (R := R) (B := SCat R) F G
  whiskerLeft_add F _ _ y z := TwoSupercategory.whiskerLeft_add (R := R) (B := SCat R) F y z
  add_whiskerRight x z G := TwoSupercategory.add_whiskerRight (R := R) (B := SCat R) x z G
  whiskerLeft_smul F _ _ r y := TwoSupercategory.whiskerLeft_smul (B := SCat R) F r y
  smul_whiskerRight r x G := TwoSupercategory.smul_whiskerRight (B := SCat R) r x G
  whiskerLeft_mem F _ _ _ _ hy := TwoSupercategory.whiskerLeft_mem (B := SCat R) F hy
  whiskerRight_mem G hx := TwoSupercategory.whiskerRight_mem (B := SCat R) G hx
  super_interchange hx hy := TwoSupercategory.super_interchange (B := SCat R) hx hy
  associator_hom_mem F G H := TwoSupercategory.associator_hom_mem (B := SCat R) F G H
  leftUnitor_hom_mem F := TwoSupercategory.leftUnitor_hom_mem (B := SCat R) F
  rightUnitor_hom_mem F := TwoSupercategory.rightUnitor_hom_mem (B := SCat R) F

/--
@isnad1 id=eq.0h8v.s8.9cdb2c8d2ab0 from=translated src=- shape=019c06be vocab=17b42a27
-/
@[simp] theorem associator_hom {A B C D : PiSCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C)
    (H : C ⟶ D) : (associator F G H).hom = 𝟙 (F ≫ G ≫ H) := rfl

/--
@isnad1 id=eq.0h8v.s8.395bfed74ca1 from=translated src=- shape=d6acb92e vocab=ff951580
-/
@[simp] theorem associator_inv {A B C D : PiSCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C)
    (H : C ⟶ D) : (associator F G H).inv = 𝟙 (F ≫ G ≫ H) := rfl

/--
@isnad1 id=eq.0h4v.s7.9c5fa2d85fa1 from=translated src=- shape=4a3d7ab8 vocab=05a69006
-/
@[simp] theorem leftUnitor_hom {A B : PiSCat.{w, v, u} R} (F : A ⟶ B) :
    (leftUnitor F).hom = 𝟙 F := rfl

/--
@isnad1 id=eq.0h4v.s7.bfaf24c1ae12 from=translated src=- shape=342726aa vocab=3c18b059
-/
@[simp] theorem leftUnitor_inv {A B : PiSCat.{w, v, u} R} (F : A ⟶ B) :
    (leftUnitor F).inv = 𝟙 F := rfl

/--
@isnad1 id=eq.0h4v.s7.341b5d67442e from=translated src=- shape=2929adf1 vocab=62114e3a
-/
@[simp] theorem rightUnitor_hom {A B : PiSCat.{w, v, u} R} (F : A ⟶ B) :
    (rightUnitor F).hom = 𝟙 F := rfl

/--
@isnad1 id=eq.0h4v.s7.147d6204a784 from=translated src=- shape=14a7ed85 vocab=b9bb1f64
-/
@[simp] theorem rightUnitor_inv {A B : PiSCat.{w, v, u} R} (F : A ⟶ B) :
    (rightUnitor F).inv = 𝟙 F := rfl

end PiSCat

end StringDiagrams

end
