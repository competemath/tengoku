/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.CategoryTheory.Monoidal.Transport
public import Tengoku.Seed.Algebra.Category.AlgCat.Basic
public import Tengoku.Seed.Algebra.Category.ModuleCat.Monoidal.Basic
public import Tengoku.Seed.RingTheory.TensorProduct.Maps

/-!
# The monoidal category structure on R-algebras
-/

public section

open CategoryTheory
open scoped MonoidalCategory

universe v u

variable {R : Type u} [CommRing R]

namespace AlgCat

noncomputable section

namespace instMonoidalCategory

open scoped TensorProduct

/-- Auxiliary definition used to fight a timeout when building
`AlgCat.instMonoidalCategory`. -/
@[simps!]
noncomputable abbrev tensorObj (X Y : AlgCat.{u} R) : AlgCat.{u} R :=
  of R (X ⊗[R] Y)

/-- Auxiliary definition used to fight a timeout when building
`AlgCat.instMonoidalCategory`. -/
noncomputable abbrev tensorHom {W X Y Z : AlgCat.{u} R} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorObj W Y ⟶ tensorObj X Z :=
  ofHom <| Algebra.TensorProduct.map f.hom g.hom

end instMonoidalCategory

open instMonoidalCategory

instance : MonoidalCategoryStruct (AlgCat.{u} R) where
  tensorObj := instMonoidalCategory.tensorObj
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight {X₁ X₂} (f : X₁ ⟶ X₂) Y := tensorHom f (𝟙 Y)
  tensorHom := tensorHom
  tensorUnit := of R R
  associator X Y Z := (Algebra.TensorProduct.assoc R R R X Y Z).toAlgebraIso
  leftUnitor X := (Algebra.TensorProduct.lid R X).toAlgebraIso
  rightUnitor X := (Algebra.TensorProduct.rid R R X).toAlgebraIso

/--
@isnad1 id=eq.0h7v.s8.3829efaee9c9 from=seed src=0 shape=026c0b2d vocab=a0265466
-/
theorem hom_tensorHom {K L M N : AlgCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) :
    (f ⊗ₘ g).hom = Algebra.TensorProduct.map f.hom g.hom :=
  rfl

/--
@isnad1 id=eq.0h5v.s8.e62e70758a7b from=seed src=0 shape=626c1e40 vocab=c4d657ec
-/
theorem hom_whiskerLeft (L : AlgCat.{u} R) {M N : AlgCat.{u} R} (f : M ⟶ N) :
    (L ◁ f).hom = Algebra.TensorProduct.map (.id _ _) f.hom :=
  rfl

/--
@isnad1 id=eq.0h5v.s8.3eb088c9b3ec from=seed src=0 shape=70f656fc vocab=a9859715
-/
theorem hom_whiskerRight {L M : AlgCat.{u} R} (f : L ⟶ M) (N : AlgCat.{u} R) :
    (f ▷ N).hom = Algebra.TensorProduct.map f.hom (.id _ _) :=
  rfl

/--
@isnad1 id=eq.0h2v.s8.fc05310d117a from=seed src=0 shape=1132733a vocab=4069c67e
-/
theorem hom_hom_leftUnitor {M : AlgCat.{u} R} :
    (λ_ M).hom.hom = (Algebra.TensorProduct.lid _ _).toAlgHom :=
  rfl

/--
@isnad1 id=eq.0h2v.s9.051c2bd0f36a from=seed src=0 shape=c3eabe4f vocab=6821f4e7
-/
theorem hom_inv_leftUnitor {M : AlgCat.{u} R} :
    (λ_ M).inv.hom = (Algebra.TensorProduct.lid _ _).symm.toAlgHom :=
  rfl

/--
@isnad1 id=eq.0h2v.s9.afcdc4bf6d34 from=seed src=0 shape=dee0f35e vocab=9f5d6b97
-/
theorem hom_hom_rightUnitor {M : AlgCat.{u} R} :
    (ρ_ M).hom.hom = (Algebra.TensorProduct.rid _ _ _).toAlgHom :=
  rfl

/--
@isnad1 id=eq.0h2v.s9.4c119331ae1b from=seed src=0 shape=cc417739 vocab=0cb8b4b3
-/
theorem hom_inv_rightUnitor {M : AlgCat.{u} R} :
    (ρ_ M).inv.hom = (Algebra.TensorProduct.rid _ _ _).symm.toAlgHom :=
  rfl

/--
@isnad1 id=eq.0h4v.s10.7ae16fb0407d from=seed src=0 shape=6d0d849d vocab=99d4955d
-/
theorem hom_hom_associator {M N K : AlgCat.{u} R} :
    (α_ M N K).hom.hom = (Algebra.TensorProduct.assoc R R R M N K).toAlgHom :=
  rfl

/--
@isnad1 id=eq.0h4v.s11.e2f2b56174ca from=seed src=0 shape=c45f2ed4 vocab=82aaed9f
-/
theorem hom_inv_associator {M N K : AlgCat.{u} R} :
    (α_ M N K).inv.hom = (Algebra.TensorProduct.assoc R R R M N K).symm.toAlgHom :=
  rfl

noncomputable instance instMonoidalCategory : MonoidalCategory (AlgCat.{u} R) :=
  Monoidal.induced
    (forget₂ (AlgCat R) (ModuleCat R))
    { μIso := fun _ _ => Iso.refl _
      εIso := Iso.refl _
      associator_eq := fun _ _ _ =>
        ModuleCat.hom_ext <| TensorProduct.ext_threefold (fun _ _ _ => rfl)
      leftUnitor_eq := fun _ => ModuleCat.hom_ext <| TensorProduct.ext' (fun _ _ => rfl)
      rightUnitor_eq := fun _ => ModuleCat.hom_ext <| TensorProduct.ext' (fun _ _ => rfl) }

/-- `forget₂ (AlgCat R) (ModuleCat R)` as a monoidal functor. -/
example : (forget₂ (AlgCat R) (ModuleCat R)).Monoidal := inferInstance

end

end AlgCat
