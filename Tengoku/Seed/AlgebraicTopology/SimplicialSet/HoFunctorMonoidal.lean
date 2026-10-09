/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Tengoku.Seed.CategoryTheory.Functor.CurryingThree
public import Tengoku.Seed.CategoryTheory.Monoidal.Cartesian.Cat

/-!
# The homotopy category functor is monoidal

Given `2`-truncated simplicial sets `X` and `Y`, we introduce ad operation
`Truncated.Edge.tensor : Edge x x' → Edge y y' → Edge (x, y) (x', y')`.
We use this in order to construct an equivalence of categories
`(X ⊗ Y).HomotopyCategory ≌ X.HomotopyCategory × Y.HomotopyCategory`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Simplicial SimplicialObject.Truncated
  CartesianMonoidalCategory Limits

namespace SSet

namespace Truncated

namespace Edge

variable {X Y X' Y' Z : Truncated.{u} 2}

/-- The external product of edges of `2`-truncated simplicial sets. -/
@[simps]
def tensor {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') :
    Edge (X := X ⊗ Y) (x, y) (x', y') where
  edge := (e₁.edge, e₂.edge)
  src_eq := Prod.ext e₁.src_eq e₂.src_eq
  tgt_eq := Prod.ext e₁.tgt_eq e₂.tgt_eq

/--
@isnad1 id=ex.0h7v.s9.b78e2446261f from=seed src=0 shape=89dc7b6f vocab=45862722
-/
lemma tensor_surjective {x x' : X _⦋0⦌₂} {y y' : Y _⦋0⦌₂}
    (e : Edge (X := X ⊗ Y) (x, y) (x', y')) :
    ∃ (e₁ : Edge x x') (e₂ : Edge y y'), e₁.tensor e₂ = e :=
  ⟨e.map (fst _ _), e.map (snd _ _), rfl⟩

/--
@isnad1 id=eq.0h4v.s9.35ccf300425b from=seed src=0 shape=b34e9175 vocab=330dc8c2
-/
@[simp]
lemma id_tensor_id (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (id x).tensor (id y) = id (X := X ⊗ Y) (x, y) := rfl

/--
@isnad1 id=eq.0h12v.s12.bd9709b43014 from=seed src=0 shape=5ea2d175 vocab=cc15c9b3
-/
@[simp]
lemma map_tensorHom {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') (f : X ⟶ X') (g : Y ⟶ Y') :
    (e₁.tensor e₂).map (f ⊗ₘ g) =
      (e₁.map f).tensor (e₂.map g) := rfl

/--
@isnad1 id=eq.0h10v.s12.2823d07340ad from=seed src=0 shape=175d5980 vocab=b3777877
-/
@[simp]
lemma map_whiskerRight {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') (f : X ⟶ X') :
    (e₁.tensor e₂).map (f ▷ _) =
      (e₁.map f).tensor e₂ := rfl

/--
@isnad1 id=eq.0h10v.s12.7b2a109aabe7 from=seed src=0 shape=6c47dbd7 vocab=7516a46a
-/
@[simp]
lemma map_whiskerLeft {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') (g : Y ⟶ Y') :
    (e₁.tensor e₂).map (_ ◁ g) =
      e₁.tensor (e₂.map g) := rfl

/--
@isnad1 id=eq.0h12v.s13.e77d0ed1002e from=seed src=0 shape=93434b1b vocab=6664317c
-/
@[simp]
lemma map_associator_hom {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂} (e₂ : Edge y y')
    {z z' : Z _⦋0⦌₂} (e₃ : Edge z z') :
    ((e₁.tensor e₂).tensor e₃).map (α_ _ _ _).hom = e₁.tensor (e₂.tensor e₃) :=
  rfl

/--
@isnad1 id=eq.0h8v.s11.5015050e3389 from=seed src=0 shape=80df2d72 vocab=f017e805
-/
@[simp]
lemma map_fst {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') :
    (e₁.tensor e₂).map (fst _ _) = e₁ := rfl

/--
@isnad1 id=eq.0h8v.s11.849e84bff203 from=seed src=0 shape=28ec56f7 vocab=cd5638b4
-/
@[simp]
lemma map_snd {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') :
    (e₁.tensor e₂).map (snd _ _) = e₂ := rfl

/-- The external product of `CompStruct` between edges of `2`-truncated simplicial sets. -/
@[simps simplex_fst simplex_snd]
def CompStruct.tensor
    {x₀ x₁ x₂ : X _⦋0⦌₂} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (hx : CompStruct e₀₁ e₁₂ e₀₂)
    {y₀ y₁ y₂ : Y _⦋0⦌₂} {e'₀₁ : Edge y₀ y₁} {e'₁₂ : Edge y₁ y₂} {e'₀₂ : Edge y₀ y₂}
    (hy : CompStruct e'₀₁ e'₁₂ e'₀₂) :
    CompStruct (e₀₁.tensor e'₀₁) (e₁₂.tensor e'₁₂) (e₀₂.tensor e'₀₂) where
  simplex := (hx.simplex, hy.simplex)
  d₂ := Prod.ext hx.d₂ hy.d₂
  d₀ := Prod.ext hx.d₀ hy.d₀
  d₁ := Prod.ext hx.d₁ hy.d₁

end Edge

namespace HomotopyCategory

instance {n : ℕ} (d : (SimplexCategory.Truncated n)ᵒᵖ) :
    Unique ((𝟙_ (Truncated.{u} n)).obj d) :=
  inferInstanceAs (Unique PUnit)

/-- If `X : Truncated 2` has a unique `0`-simplex and (at most) one `1`-simplex,
this is the isomorphism `Cat.of X.HomotopyCategory ≅ Cat.chosenTerminal` in `Cat`. -/
def isoTerminal (X : Truncated.{u} 2) [Unique (X _⦋0⦌₂)] [Subsingleton (X _⦋1⦌₂)] :
    Cat.of X.HomotopyCategory ≅ Cat.chosenTerminal :=
  IsTerminal.uniqueUpToIso (isTerminal _) Cat.chosenTerminalIsTerminal

namespace BinaryProduct

/--
@isnad1 id=eq.0h8v.s12.157bcca79440 from=seed src=0 shape=ec7648d5 vocab=8a2cf02c
-/
lemma square {X Y : Truncated.{u} 2}
    {x₀ x₁ : X _⦋0⦌₂} (ex : Edge x₀ x₁) {y₀ y₁ : Y _⦋0⦌₂} (ey : Edge y₀ y₁) :
    homMk (ex.tensor (.id y₀)) ≫ homMk (Edge.tensor (.id x₁) ey) =
      homMk (Edge.tensor (.id x₀) ey) ≫ homMk (ex.tensor (.id y₁)) := by
  rw [homMk_comp_homMk ((Edge.CompStruct.idComp ex).tensor (Edge.CompStruct.compId ey)),
    homMk_comp_homMk ((Edge.CompStruct.compId ex).tensor (Edge.CompStruct.idComp ey))]

variable {X X' Y Y' Z : Truncated.{u} 2}

variable (X Y) in
/-- The functor `(X ⊗ Y).HomotopyCategory ⥤ X.HomotopyCategory × Y.HomotopyCategory`
when `X` and `Y` are `2`-truncated simplicial sets. -/
def functor : (X ⊗ Y).HomotopyCategory ⥤ X.HomotopyCategory × Y.HomotopyCategory :=
  (mapHomotopyCategory (fst _ _)).prod' (mapHomotopyCategory (snd _ _))

/--
@isnad1 id=eq.0h4v.s9.5e5dbd2e76a8 from=seed src=0 shape=f13197b3 vocab=d8667e93
-/
@[simp]
lemma functor_obj (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (functor X Y).obj (mk (x, y)) = (mk x, mk y) := rfl

/--
@isnad1 id=eq.0h8v.s11.9304268db6db from=seed src=0 shape=374cac82 vocab=aa3032e4
-/
@[simp]
lemma functor_map {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁)
    {y₀ y₁ : Y _⦋0⦌₂} (e' : Edge y₀ y₁) :
    (functor X Y).map (homMk (e.tensor e')) = (homMk e, homMk e') := rfl

set_option backward.isDefEq.respectTransparency.types false in
variable (X Y) in
/-- The functor `X.HomotopyCategory ⥤ Y.HomotopyCategory ⥤ (X ⊗ Y).HomotopyCategory`
when `X` and `Y` are `2`-truncated simplicial sets. -/
def curriedInverse : X.HomotopyCategory ⥤ Y.HomotopyCategory ⥤ (X ⊗ Y).HomotopyCategory :=
  lift (fun x ↦ lift (fun y ↦ mk (x, y)) (fun {y₀ y₁} e ↦ homMk (Edge.tensor (.id _) e)) (by simp)
    (fun {y₀ y₁ y₁ e₀₁ e₁₂ e₀₂ h} ↦ homMk_comp_homMk ((Edge.CompStruct.idCompId x).tensor h)))
    (fun {x₀ x₁} e ↦ mkNatTrans (fun y ↦ homMk (V := X ⊗ Y) (x₀ := (x₀, y))
      (x₁ := (x₁, y)) (e.tensor (.id y))) (fun y₀ y₁ e' ↦ by simp [square]))
    (by cat_disch) (fun {x₀ x₁ x₂ e₀₁ e₁₂ e₀₂} h ↦ by
      ext y
      obtain ⟨y, rfl⟩ := mk_surjective y
      simpa using homMk_comp_homMk (h.tensor (.idCompId y)))

variable (X Y) in
/-- The functor `X.HomotopyCategory × Y.HomotopyCategory ⥤ (X ⊗ Y).HomotopyCategory`
when `X` and `Y` are `2`-truncated simplicial sets. -/
def inverse : X.HomotopyCategory × Y.HomotopyCategory ⥤ (X ⊗ Y).HomotopyCategory :=
  Functor.uncurry.obj (curriedInverse X Y)

/--
@isnad1 id=eq.0h4v.s9.68ae0199f0f6 from=seed src=0 shape=a5b96959 vocab=ee781389
-/
@[simp]
lemma inverse_obj (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) : (inverse X Y).obj (mk x, mk y) = mk (x, y) := rfl

/--
@isnad1 id=eq.0h6v.s10.a83e9ea0fc1d from=seed src=0 shape=57b6f356 vocab=730d34d7
-/
@[simp]
lemma inverse_map_mkHom_homMk_id {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁) (y : Y _⦋0⦌₂) :
    (inverse X Y).map (Prod.mkHom (homMk e) (𝟙 (mk y))) = homMk (e.tensor (.id y)) := rfl

/--
@isnad1 id=eq.0h6v.s10.7206f7972c9f from=seed src=0 shape=5617f2c2 vocab=730d34d7
-/
@[simp]
lemma inverse_map_mkHom_id_homMk (x : X _⦋0⦌₂) {y₀ y₁ : Y _⦋0⦌₂} (e : Edge y₀ y₁) :
    (inverse X Y).map (Prod.mkHom (𝟙 (mk x)) (homMk e)) = homMk ((Edge.id x).tensor e) := rfl

/--
@isnad1 id=eq.0h8v.s10.3dfc0fb7159c from=seed src=0 shape=f4a833d4 vocab=255d5df1
-/
lemma inverse_map_mkHom_homMk_homMk {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁)
    {y₀ y₁ : Y _⦋0⦌₂} (e' : Edge y₀ y₁) :
    (inverse X Y).map (Prod.mkHom (homMk e) (homMk e')) = homMk (e.tensor e') :=
  homMk_comp_homMk ((Edge.CompStruct.compId e).tensor (Edge.CompStruct.idComp e'))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (X Y) in
/-- Auxiliary definition for `equivalence`. -/
def functorCompInverseIso : functor X Y ⋙ inverse X Y ≅ 𝟭 _ :=
  mkNatIso (fun _ ↦ Iso.refl _) (by
    rintro ⟨x₀, y₀⟩ ⟨x₁, y₁⟩ e
    obtain ⟨ex, ey, rfl⟩ := e.tensor_surjective
    dsimp
    rw [Category.comp_id, Category.id_comp, inverse_map_mkHom_homMk_homMk])

/--
@isnad1 id=eq.0h4v.s12.d6be4fcee4c9 from=seed src=0 shape=8feb5835 vocab=568a1cd3
-/
@[simp]
lemma functorCompInverseIso_hom_app (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (functorCompInverseIso X Y).hom.app (mk (x, y)) = 𝟙 _ := rfl

/--
@isnad1 id=eq.0h4v.s12.c4e2323bb737 from=seed src=0 shape=a77fb2d7 vocab=308e1ff9
-/
@[simp]
lemma functorCompInverseIso_inv_app (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (functorCompInverseIso X Y).inv.app (mk (x, y)) = 𝟙 _ := rfl

variable (X Y) in
/-- Auxiliary definition for `equivalence`. -/
def inverseCompFunctorIso : inverse X Y ⋙ functor X Y ≅ 𝟭 _ :=
  Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x ↦ mkNatIso (fun y ↦ Iso.refl _))
      (fun x₀ x₁ e ↦ by
        ext y : 2
        obtain ⟨y, rfl⟩ := y.mk_surjective
        cat_disch))

/--
@isnad1 id=eq.0h4v.s10.51b8d8209004 from=seed src=0 shape=84339f7d vocab=339ccc16
-/
@[simp]
lemma inverseCompFunctorIso_hom_app (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (inverseCompFunctorIso X Y).hom.app (mk x, mk y) = 𝟙 _ := rfl

/--
@isnad1 id=eq.0h4v.s10.221349e258f4 from=seed src=0 shape=b216e149 vocab=b28bfba4
-/
@[simp]
lemma inverseCompFunctorIso_inv_app (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (inverseCompFunctorIso X Y).inv.app (mk x, mk y) = 𝟙 _ := rfl

variable (X Y)

/--
@isnad1 id=eq.0h2v.s9.7c0529e16be3 from=seed src=0 shape=19d0d115 vocab=416f8aea
-/
lemma functor_comp_inverse : functor X Y ⋙ inverse X Y = 𝟭 _ :=
  Functor.ext_of_iso (functorCompInverseIso X Y) (fun _ ↦ rfl)

/--
@isnad1 id=eq.0h2v.s8.706bdae47f95 from=seed src=0 shape=b21a3d09 vocab=416f8aea
-/
lemma inverse_comp_functor : inverse X Y ⋙ functor X Y = 𝟭 _ :=
  Functor.ext_of_iso (inverseCompFunctorIso X Y) (fun _ ↦ rfl)

/-- The equivalence `(X ⊗ Y).HomotopyCategory ≌ X.HomotopyCategory ⥤ Y.HomotopyCategory`
when `X` and `Y` are `2`-truncated simplicial sets. -/
def equivalence :
    (X ⊗ Y).HomotopyCategory ≌ X.HomotopyCategory × Y.HomotopyCategory where
  functor := functor X Y
  inverse := inverse X Y
  unitIso := (functorCompInverseIso X Y).symm
  counitIso := inverseCompFunctorIso X Y

/-- The isomorphism of categories between
`(X ⊗ Y).HomotopyCategory` and `X.HomotopyCategory ⥤ Y.HomotopyCategory`. -/
@[simps]
def iso :
    Cat.of ((X ⊗ Y).HomotopyCategory) ≅ Cat.of (X.HomotopyCategory × Y.HomotopyCategory) where
  hom := Cat.Hom.ofFunctor (functor X Y)
  inv := Cat.Hom.ofFunctor (inverse X Y)
  hom_inv_id := by ext; exact functor_comp_inverse X Y
  inv_hom_id := by ext; exact inverse_comp_functor X Y

set_option backward.isDefEq.respectTransparency.types false in
variable {X} in
/-- The naturality of `HomotopyCategory.BinaryProduct.inverse`
with respect to the first variable. -/
def mapHomotopyCategoryProdIdCompInverseIso (f : X ⟶ X') :
    (mapHomotopyCategory f).prod (𝟭 _) ⋙ inverse X' Y ≅
      inverse X Y ⋙ mapHomotopyCategory (f ▷ Y) :=
  Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x ↦ mkNatIso (fun y ↦ Iso.refl _)) (fun x₀ x₁ e ↦ by
      ext y
      obtain ⟨y, rfl⟩ := y.mk_surjective
      simp
      rfl))

set_option backward.isDefEq.respectTransparency.types false in
variable {Y} in
/-- The naturality of `HomotopyCategory.BinaryProduct.inverse`
with respect to the second variable. -/
def idProdMapHomotopyCategoryCompInverseIso (g : Y ⟶ Y') :
    Functor.prod (𝟭 _) (mapHomotopyCategory g) ⋙ inverse X Y' ≅
      inverse X Y ⋙ mapHomotopyCategory (X ◁ g) :=
  Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x ↦ mkNatIso (fun y ↦ Iso.refl _)) (fun x₀ x₁ e ↦ by
      ext y
      obtain ⟨y, rfl⟩ := y.mk_surjective
      simp
      rfl))

variable {X} in
/--
@isnad1 id=eq.0h4v.s10.c84310f45215 from=seed src=0 shape=0fdd4bd6 vocab=b7c6fbe0
-/
lemma mapHomotopyCategory_prod_id_comp_inverse (f : X ⟶ X') :
    (mapHomotopyCategory f).prod (𝟭 _) ⋙ inverse X' Y =
      inverse X Y ⋙ mapHomotopyCategory (f ▷ Y) :=
  Functor.ext_of_iso (mapHomotopyCategoryProdIdCompInverseIso _ _) (fun _ ↦ rfl)

variable {Y} in
/--
@isnad1 id=eq.0h4v.s10.40ef30db8194 from=seed src=0 shape=de09b174 vocab=7b0d692a
-/
lemma id_prod_mapHomotopyCategory_comp_inverse (g : Y ⟶ Y') :
    Functor.prod (𝟭 _) (mapHomotopyCategory g) ⋙ inverse X Y' =
      inverse X Y ⋙ mapHomotopyCategory (X ◁ g) :=
  Functor.ext_of_iso (idProdMapHomotopyCategoryCompInverseIso _ _) (fun _ ↦ rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The compatibility of `HomotopyCategory.BinaryProduct.inverse`
with respect to the first projection. -/
def inverseCompMapHomotopyCategoryFstIso :
    inverse X Y ⋙ mapHomotopyCategory (fst _ _) ≅ CategoryTheory.Prod.fst _ _ :=
  Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x ↦ mkNatIso (fun y ↦ Iso.refl _) (fun y₀ y₁ e ↦ by
      dsimp
      rw [Category.comp_id]
      exact homMk_id x)) (fun x₀ x₁ e ↦ by
      ext y
      obtain ⟨y, rfl⟩ := y.mk_surjective
      simp))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The compatibility of `HomotopyCategory.BinaryProduct.inverse`
with respect to the second projection. -/
def inverseCompMapHomotopyCategorySndIso :
    inverse X Y ⋙ mapHomotopyCategory (snd _ _) ≅ CategoryTheory.Prod.snd _ _ :=
  Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x ↦ mkNatIso (fun y ↦ Iso.refl _)) (fun x₀ x₁ e ↦ by
      ext y
      obtain ⟨y, rfl⟩ := y.mk_surjective
      dsimp
      simp only [Category.comp_id]
      exact homMk_id y))

/--
@isnad1 id=eq.0h2v.s8.ad365d14e759 from=seed src=0 shape=dd194cf2 vocab=07bcc3d9
-/
lemma inverse_comp_mapHomotopyCategory_fst :
    inverse X Y ⋙ mapHomotopyCategory (fst _ _) = CategoryTheory.Prod.fst _ _ :=
  Functor.ext_of_iso (inverseCompMapHomotopyCategoryFstIso _ _) (fun _ ↦ rfl)

/--
@isnad1 id=eq.0h2v.s8.de11b24c6350 from=seed src=0 shape=086a5292 vocab=c5bb7da3
-/
lemma inverse_comp_mapHomotopyCategory_snd :
    inverse X Y ⋙ mapHomotopyCategory (snd _ _) = CategoryTheory.Prod.snd _ _ :=
  Functor.ext_of_iso (inverseCompMapHomotopyCategorySndIso _ _) (fun _ ↦ rfl)

/--
@isnad1 id=eq.0h2v.s9.e84f94e2ae61 from=seed src=0 shape=adf23d96 vocab=938fc2cd
-/
lemma left_unitality [Unique (X _⦋0⦌₂)] [Subsingleton (X _⦋1⦌₂)] :
    CategoryTheory.Prod.snd _ _ = Functor.prod (isoTerminal X).inv.toFunctor (𝟭 _) ⋙
      inverse X Y ⋙ mapHomotopyCategory (snd _ _) := by
  rw [inverse_comp_mapHomotopyCategory_snd]
  rfl

/--
@isnad1 id=eq.0h2v.s9.5ff146db9019 from=seed src=0 shape=ec254ec6 vocab=5907586c
-/
lemma right_unitality [Unique (Y _⦋0⦌₂)] [Subsingleton (Y _⦋1⦌₂)] :
    CategoryTheory.Prod.fst _ _ = Functor.prod (𝟭 _) (isoTerminal Y).inv.toFunctor ⋙
      inverse X Y ⋙ mapHomotopyCategory (fst _ _) := by
  rw [inverse_comp_mapHomotopyCategory_fst]
  rfl

variable (Z)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `associativityIso`. -/
def associativity'Iso :
    (prod.associativity ..).inverse ⋙ (inverse X Y).prod (𝟭 _) ⋙ inverse (X ⊗ Y) Z ⋙
      mapHomotopyCategory (α_ _ _ _).hom ≅
    Functor.prod (𝟭 _) (inverse Y Z) ⋙ inverse X (Y ⊗ Z) :=
  Functor.fullyFaithfulCurry₃.preimageIso
    (mkNatIso (fun x ↦ mkNatIso (fun y ↦ mkNatIso (fun z ↦ Iso.refl _)
      (fun z₀ z₁ e ↦ by
        dsimp
        rw [Category.comp_id, Category.id_comp, ← prod_id,
          inverse_map_mkHom_id_homMk, inverse_map_mkHom_id_homMk,
          CategoryTheory.Functor.map_id]
        dsimp [← Edge.id_tensor_id]))
      (fun y₀ y₁ e ↦ by
        ext z
        obtain ⟨z, rfl⟩ := z.mk_surjective
        dsimp
        rw [Category.comp_id, Category.id_comp,
          inverse_map_mkHom_homMk_id, inverse_map_mkHom_id_homMk]))
      (fun x₀ x₁ e ↦ by
        ext y z
        obtain ⟨y, rfl⟩ := y.mk_surjective
        obtain ⟨z, rfl⟩ := z.mk_surjective
        dsimp
        simp only [Category.comp_id, Category.id_comp, ← prod_id',
          CategoryTheory.Functor.map_id, inverse_obj, inverse_map_mkHom_homMk_id]))

set_option backward.isDefEq.respectTransparency.types false in
variable {X Y Z} in
/--
@isnad1 id=eq.0h4v.s14.4e773d7bd9fd from=seed src=0 shape=0f2a1a52 vocab=55f71b1b
-/
lemma associativity'Iso_hom_app (xyz) :
    (associativity'Iso X Y Z).hom.app xyz = 𝟙 _ := by
  change 𝟙 _ ≫ _ ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]
  rfl

open Functor in
/-- The compatibility of `HomotopyCategory.BinaryProduct.inverse`
with respect to associators. -/
def associativityIso :
    (inverse X Y).prod (𝟭 _) ⋙ inverse (X ⊗ Y) Z ⋙ mapHomotopyCategory (α_ _ _ _).hom ≅
      (prod.associativity _ _ _).functor ⋙ Functor.prod (𝟭 _) (inverse Y Z) ⋙
        inverse X (Y ⊗ Z) :=
  (Functor.leftUnitor _).symm ≪≫ isoWhiskerRight (Equivalence.unitIso _) _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft (prod.associativity _ _ _).functor (associativity'Iso X Y Z)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {X Y Z} in
/--
@isnad1 id=eq.0h4v.s14.f1d481812c22 from=seed src=0 shape=c8faf3a1 vocab=2e75c7ac
-/
lemma associativityIso_hom_app (xyz) :
    (associativityIso X Y Z).hom.app xyz = 𝟙 _ := by
  dsimp [associativityIso]
  rw [associativity'Iso_hom_app _]
  dsimp
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Category.comp_id, ← prod_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]

/--
@isnad1 id=eq.0h3v.s12.9a9c74c70ce2 from=seed src=0 shape=3abec57f vocab=8e69b078
-/
lemma associativity :
    (inverse X Y).prod (𝟭 _) ⋙ inverse (X ⊗ Y) Z ⋙ mapHomotopyCategory (α_ _ _ _).hom =
    (prod.associativity _ _ _).functor ⋙ Functor.prod (𝟭 _) (inverse Y Z) ⋙
      inverse X (Y ⊗ Z) :=
  Functor.ext_of_iso (associativityIso _ _ _) (fun _ ↦ rfl) associativityIso_hom_app

end BinaryProduct

end HomotopyCategory

open HomotopyCategory.BinaryProduct in
instance : hoFunctor₂.{u}.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := (HomotopyCategory.isoTerminal _).symm
      μIso X Y := (iso X Y).symm
      μIso_hom_natural_left _ _ := by ext; apply mapHomotopyCategory_prod_id_comp_inverse
      μIso_hom_natural_right _ _ := by ext; apply id_prod_mapHomotopyCategory_comp_inverse
      left_unitality Y := by ext; apply left_unitality
      right_unitality X := by ext; apply right_unitality
      associativity _ _ _ := by ext; apply associativity }

/-- The homotopy category functor `hoFunctor : SSet.{u} ⥤ Cat.{u, u}` is (cartesian) monoidal. -/
instance hoFunctor.monoidal : hoFunctor.{u}.Monoidal :=
  inferInstanceAs (truncation 2 ⋙ hoFunctor₂).Monoidal

end Truncated

/-- An equivalence between the vertices of a simplicial set `X` and the
objects of `hoFunctor.obj X`. -/
def hoFunctor.unitHomEquiv (X : SSet.{u}) :
    (𝟙_ SSet ⟶ X) ≃ Cat.chosenTerminal ⥤ hoFunctor.obj X :=
  (SSet.unitHomEquiv X).trans <|
    HomotopyCategory.objEquiv.symm.trans Cat.fromChosenTerminalEquiv.symm

/--
@isnad1 id=eq.0h2v.s9.e5224c733916 from=seed src=0 shape=c16eb0ba vocab=12a48025
-/
theorem hoFunctor.unitHomEquiv_eq (X : SSet.{u}) (x : 𝟙_ SSet ⟶ X) :
    hoFunctor.unitHomEquiv X x =
      (Functor.LaxMonoidal.ε hoFunctor.{u}).toFunctor ⋙ (hoFunctor.map x).toFunctor :=
  rfl

end SSet
