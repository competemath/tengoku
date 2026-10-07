/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Homology.Additive
public import Tengoku.Seed.Algebra.Homology.ShortComplex.Abelian
public import Tengoku.Seed.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Left resolutions

Given a fully faithful functor `ι : C ⥤ A` to an abelian category,
we introduce a structure `Abelian.LeftResolution ι` which gives
a functor `F : A ⥤ C` and a natural epimorphism
`π.app X : ι.obj (F.obj X) ⟶ X` for all `X : A`.
This is used in order to construct a resolution functor
`LeftResolution.chainComplexFunctor : A ⥤ ChainComplex C ℕ`.

This shall be used in order to construct functorial flat resolutions.

-/

@[expose] public section

namespace CategoryTheory.Abelian

open Category Limits Preadditive ZeroObject

variable {A C : Type*} [Category* C] [Category* A] (ι : C ⥤ A)

/-- Given a fully faithful functor `ι : C ⥤ A`, this structure contains the data
of a functor `F : A ⥤ C` and a functorial epimorphism
`π.app X : ι.obj (F.obj X) ⟶ X` for all `X : A`. -/
structure LeftResolution where
  /-- a functor which sends `X : A` to an object `F.obj X` with an epimorphism
    `π.app X : ι.obj (F.obj X) ⟶ X` -/
  F : A ⥤ C
  /-- the natural epimorphism -/
  π : F ⋙ ι ⟶ 𝟭 A
  epi_π_app (X : A) : Epi (π.app X) := by infer_instance

namespace LeftResolution

attribute [instance] epi_π_app

variable {ι} (Λ : LeftResolution ι) (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z)

/--
@isnad1 id=eq.0h7v.s8.9f19ce2d6bf4 from=seed src=0 shape=be6a0201 vocab=86d95d60
-/
@[reassoc (attr := simp)]
lemma π_naturality : ι.map (Λ.F.map f) ≫ Λ.π.app Y = Λ.π.app X ≫ f :=
  Λ.π.naturality f

variable [ι.Full] [ι.Faithful] [HasZeroMorphisms C] [Abelian A]

/-- Given `ι : C ⥤ A`, `Λ : LeftResolution ι`, `X : A`, this is a chain complex
which is a (functorial) resolution of `A` that is obtained inductively by using
the epimorphisms given by `Λ`. -/
noncomputable def chainComplex : ChainComplex C ℕ :=
  ChainComplex.mk' _ _ (ι.preimage (Λ.π.app (kernel (Λ.π.app X)) ≫ kernel.ι _))
    (fun f => ⟨_, ι.preimage (Λ.π.app (kernel (ι.map f)) ≫ kernel.ι _),
      ι.map_injective (by simp)⟩)

/-- Given `Λ : LeftResolution ι`, the chain complex `Λ.chainComplex X`
identifies in degree `0` to `Λ.F.obj X`. -/
noncomputable def chainComplexXZeroIso :
    (Λ.chainComplex X).X 0 ≅ Λ.F.obj X := Iso.refl _

/-- Given `Λ : LeftResolution ι`, the chain complex `Λ.chainComplex X`
identifies in degree `1` to `Λ.F.obj (kernel (Λ.π.app X))`. -/
noncomputable def chainComplexXOneIso :
    (Λ.chainComplex X).X 1 ≅ Λ.F.obj (kernel (Λ.π.app X)) := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=eq.0h5v.s10.8eaa7e551f96 from=seed src=0 shape=6c8dab99 vocab=b9fb47a4
-/
@[reassoc]
lemma map_chainComplex_d_1_0 :
    ι.map ((Λ.chainComplex X).d 1 0) =
      ι.map (Λ.chainComplexXOneIso X).hom ≫ Λ.π.app (kernel (Λ.π.app X)) ≫ kernel.ι _ ≫
      ι.map (Λ.chainComplexXZeroIso X).inv := by
  simp [chainComplexXOneIso, chainComplexXZeroIso, chainComplex]

/-- The isomorphism which gives the inductive step of the construction of `Λ.chainComplex X`. -/
noncomputable def chainComplexXIso (n : ℕ) :
    (Λ.chainComplex X).X (n + 2) ≅ Λ.F.obj (kernel (ι.map ((Λ.chainComplex X).d (n + 1) n))) := by
  apply ChainComplex.mk'XIso

/--
@isnad1 id=eq.0h6v.s11.c88d9fde080a from=seed src=0 shape=49cba045 vocab=bab8b10f
-/
lemma map_chainComplex_d (n : ℕ) :
    ι.map ((Λ.chainComplex X).d (n + 2) (n + 1)) =
    ι.map (Λ.chainComplexXIso X n).hom ≫ Λ.π.app (kernel (ι.map ((Λ.chainComplex X).d (n + 1) n))) ≫
      kernel.ι (ι.map ((Λ.chainComplex X).d (n + 1) n)) := by
  have := ι.map_preimage (Λ.π.app _ ≫ kernel.ι (ι.map ((Λ.chainComplex X).d (n + 1) n)))
  dsimp at this
  rw [← this, ← Functor.map_comp]
  congr 1
  apply ChainComplex.mk'_d

attribute [irreducible] chainComplex

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=exactat.0h6v.s7.6940216c3b6d from=seed src=0 shape=dba3c17d vocab=adaf4f25
-/
lemma exactAt_map_chainComplex_succ (n : ℕ) :
    ((ι.mapHomologicalComplex _).obj (Λ.chainComplex X)).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n
    (ComplexShape.prev_eq' _ (by dsimp; lia)) (by simp),
    ShortComplex.exact_iff_epi_kernel_lift]
  convert! epi_comp (ι.map (Λ.chainComplexXIso X n).hom) (Λ.π.app _)
  rw [← cancel_mono (kernel.ι _), kernel.lift_ι]
  simp [map_chainComplex_d]

variable {X Y Z}

set_option backward.defeqAttrib.useBackward true in
/-- The morphism `Λ.chainComplex X ⟶ Λ.chainComplex Y` of chain complexes
induced by `f : X ⟶ Y`. -/
noncomputable def chainComplexMap : Λ.chainComplex X ⟶ Λ.chainComplex Y :=
  ChainComplex.mkHom _ _
    ((Λ.chainComplexXZeroIso X).hom ≫ Λ.F.map f ≫ (Λ.chainComplexXZeroIso Y).inv)
    ((Λ.chainComplexXOneIso X).hom ≫
      Λ.F.map (kernel.map _ _ (ι.map (Λ.F.map f)) f (Λ.π.naturality f).symm) ≫
      (Λ.chainComplexXOneIso Y).inv)
    (ι.map_injective (by
        dsimp
        simp only [Category.assoc, Functor.map_comp, map_chainComplex_d_1_0]
        simp only [← ι.map_comp, ← ι.map_comp_assoc]
        simp))
    (fun n p ↦
      ⟨(Λ.chainComplexXIso X n).hom ≫ (Λ.F.map
        (kernel.map _ _ (ι.map p.2.1) (ι.map p.1) (by
          rw [← ι.map_comp, ← ι.map_comp, p.2.2]))) ≫ (Λ.chainComplexXIso Y n).inv,
            ι.map_injective (by simp [map_chainComplex_d])⟩)

/--
@isnad1 id=eq.0h7v.s8.397deed04dde from=seed src=0 shape=09643788 vocab=9fa5c62b
-/
@[simp]
lemma chainComplexMap_f_0 :
    (Λ.chainComplexMap f).f 0 =
      ((Λ.chainComplexXZeroIso X).hom ≫ Λ.F.map f ≫ (Λ.chainComplexXZeroIso Y).inv) := rfl

/--
@isnad1 id=eq.0h7v.s10.8dc5ba02b54a from=seed src=0 shape=72f9decb vocab=56193888
-/
@[simp]
lemma chainComplexMap_f_1 :
    (Λ.chainComplexMap f).f 1 =
    (Λ.chainComplexXOneIso X).hom ≫
      Λ.F.map (kernel.map _ _ (ι.map (Λ.F.map f)) f (Λ.π.naturality f).symm) ≫
      (Λ.chainComplexXOneIso Y).inv := rfl

/--
@isnad1 id=eq.0h8v.s11.8d90e2572054 from=seed src=0 shape=b1a0ca9a vocab=624ca8ac
-/
@[simp]
lemma chainComplexMap_f_succ_succ (n : ℕ) :
    (Λ.chainComplexMap f).f (n + 2) =
      (Λ.chainComplexXIso X n).hom ≫
        Λ.F.map (kernel.map _ _ (ι.map ((Λ.chainComplexMap f).f (n + 1)))
          (ι.map ((Λ.chainComplexMap f).f n))
          (by rw [← ι.map_comp, ← ι.map_comp, HomologicalComplex.Hom.comm])) ≫
          (Λ.chainComplexXIso Y n).inv := by
  apply ChainComplex.mkHom_f_succ_succ

set_option backward.defeqAttrib.useBackward true in
variable (X) in
/--
@isnad1 id=eq.0h5v.s7.30f44f6a7f2a from=seed src=0 shape=cc71cbb6 vocab=a0272519
-/
@[simp]
lemma chainComplexMap_id : Λ.chainComplexMap (𝟙 X) = 𝟙 _ := by
  ext n
  induction n with
  | zero => simp
  | succ n hn => obtain _ | n := n <;> simp [hn]

set_option backward.defeqAttrib.useBackward true in
variable (X Y) in
/--
@isnad1 id=eq.0h6v.s8.07f55882bd12 from=seed src=0 shape=535912d0 vocab=3e0f9249
-/
@[simp]
lemma chainComplexMap_zero [Λ.F.PreservesZeroMorphisms] :
    Λ.chainComplexMap (0 : X ⟶ Y) = 0 := by
  ext n
  induction n with
  | zero => simp
  | succ n hn => obtain _ | n := n <;> simp [hn]

set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=eq.0h9v.s8.55d6721ae8b7 from=seed src=0 shape=1fb7f439 vocab=93ffc699
-/
@[reassoc, simp]
lemma chainComplexMap_comp :
    Λ.chainComplexMap (f ≫ g) = Λ.chainComplexMap f ≫ Λ.chainComplexMap g := by
  ext n
  induction n with
  | zero => simp
  | succ n hn =>
    obtain _ | n := n
    all_goals
      dsimp
      simp only [chainComplexMap_f_succ_succ, assoc, Iso.cancel_iso_hom_left,
        Iso.inv_hom_id_assoc, ← Λ.F.map_comp_assoc, Iso.cancel_iso_inv_right_assoc]
      congr 1
      cat_disch

/-- Given `ι : C ⥤ A`, `Λ : LeftResolution ι`, this is a
functor `A ⥤ ChainComplex C ℕ` which sends `X : A` to a resolution consisting
of objects in `C`. -/
noncomputable def chainComplexFunctor : A ⥤ ChainComplex C ℕ where
  obj X := Λ.chainComplex X
  map f := Λ.chainComplexMap f

end LeftResolution

end CategoryTheory.Abelian
