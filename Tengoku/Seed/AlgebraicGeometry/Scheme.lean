/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.Spec
public import Tengoku.Seed.Algebra.Category.Ring.Constructions
public import Tengoku.Seed.CategoryTheory.Elementwise

/-!
# The category of schemes

A scheme is a locally ringed space such that every point is contained in some open set
where there is an isomorphism of presheaves between the restriction to that open set,
and the structure sheaf of `Spec R`, for some commutative ring `R`.

A morphism of schemes is just a morphism of the underlying locally ringed spaces.

-/

@[expose] public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737


universe u

noncomputable section

open TopologicalSpace CategoryTheory TopCat Opposite

namespace AlgebraicGeometry

/-- We define `Scheme` as an `X : LocallyRingedSpace`,
along with a proof that every point has an open neighbourhood `U`
so that the restriction of `X` to `U` is isomorphic,
as a locally ringed space, to `Spec.toLocallyRingedSpace.obj (op R)`
for some `R : CommRingCat`.
-/
structure Scheme extends LocallyRingedSpace where
  local_affine :
    ∀ x : toLocallyRingedSpace,
      ∃ (U : OpenNhds x) (R : CommRingCat),
        Nonempty
          (toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spec.toLocallyRingedSpace.obj (op R))

namespace Scheme

instance : CoeSort Scheme Type* where
  coe X := X.carrier

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Pretty printer for coercing schemes to types. -/
@[app_delab TopCat.carrier]
meta def delabAdjoinNotation : Delab := whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``TopCat.carrier 1
  withNaryArg 0 do
  guard <| (← getExpr).isAppOfArity ``PresheafedSpace.carrier 3
  withNaryArg 2 do
  guard <| (← getExpr).isAppOfArity ``SheafedSpace.toPresheafedSpace 3
  withNaryArg 2 do
  guard <| (← getExpr).isAppOfArity ``LocallyRingedSpace.toSheafedSpace 1
  withNaryArg 0 do
  guard <| (← getExpr).isAppOfArity ``Scheme.toLocallyRingedSpace 1
  withNaryArg 0 do
  `(↥$(← delab))

/-- The type of open sets of a scheme. -/
abbrev Opens (X : Scheme) : Type* := TopologicalSpace.Opens X

/-- A morphism between schemes is a morphism between the underlying locally ringed spaces. -/
structure Hom (X Y : Scheme)
  extends toLRSHom' : X.toLocallyRingedSpace.Hom Y.toLocallyRingedSpace where

/-- Cast a morphism of schemes into morphisms of local ringed spaces. -/
abbrev Hom.toLRSHom {X Y : Scheme.{u}} (f : X.Hom Y) :
    X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace :=
  f.toLRSHom'

/-- See Note [custom simps projection] -/
def Hom.Simps.toLRSHom {X Y : Scheme.{u}} (f : X.Hom Y) :
    X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace :=
  f.toLRSHom

initialize_simps_projections Hom (toLRSHom' → toLRSHom)

/-- Schemes are a full subcategory of locally ringed spaces.
-/
instance : Category Scheme where
  Hom := Hom
  id X := Hom.mk (𝟙 X.toLocallyRingedSpace)
  comp f g := Hom.mk (f.toLRSHom ≫ g.toLRSHom)

/-- `f ⁻¹ᵁ U` is notation for `(Opens.map f.base).obj U`, the preimage of an open set `U` under `f`.
The preferred name in lemmas is `preimage` and it should be treated as an infix. -/
scoped[AlgebraicGeometry] notation3:90 f:91 " ⁻¹ᵁ " U:90 =>
  @Functor.obj (Scheme.Opens _) _ (Scheme.Opens _) _
    (Opens.map (f : Scheme.Hom _ _).base) U

/-- `Γ(X, U)` is notation for `X.presheaf.obj (op U)`. -/
scoped[AlgebraicGeometry] notation3 "Γ(" X ", " U ")" =>
  (PresheafedSpace.presheaf (SheafedSpace.toPresheafedSpace
    (LocallyRingedSpace.toSheafedSpace (Scheme.toLocallyRingedSpace X)))).obj
    (op (α := Scheme.Opens _) U)

instance {X Y : Scheme.{u}} : CoeFun (X ⟶ Y) (fun _ ↦ X → Y) where
  coe f := f.base

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Pretty printer for coercing morphisms between schemes to functions. -/
@[app_delab DFunLike.coe]
meta def delabCoeFunNotation : Delab := whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``DFunLike.coe 5
  withNaryArg 4 do
  guard <| (← getExpr).isAppOfArity ``CategoryTheory.ConcreteCategory.hom 9
  withNaryArg 8 do
  guard <| (← getExpr).isAppOfArity ``PresheafedSpace.Hom.base 5
  withNaryArg 4 do
  guard <| (← getExpr).isAppOfArity ``LocallyRingedSpace.Hom.toHom 3
  withNaryArg 2 do
  guard <| (← getExpr).isAppOfArity ``Scheme.Hom.toLRSHom' 3
  withNaryArg 2 do
  `(⇑$(← delab))

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Pretty printer for applying morphisms of schemes to set-theoretic points. -/
@[app_delab DFunLike.coe]
meta def delabCoeFunAppNotation : Delab := whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``DFunLike.coe 6
  let func ← do
    withNaryArg 4 do
    guard <| (← getExpr).isAppOfArity ``CategoryTheory.ConcreteCategory.hom 9
    withNaryArg 8 do
    guard <| (← getExpr).isAppOfArity ``PresheafedSpace.Hom.base 5
    withNaryArg 4 do
    guard <| (← getExpr).isAppOfArity ``LocallyRingedSpace.Hom.toHom 3
    withNaryArg 2 do
    guard <| (← getExpr).isAppOfArity ``Scheme.Hom.toLRSHom' 3
    withNaryArg 2 do
    delab
  `($func $(← withNaryArg 5 do delab))

instance {X : Scheme.{u}} : Subsingleton Γ(X, ⊥) :=
  CommRingCat.subsingleton_of_isTerminal X.sheaf.isTerminalOfEmpty

/--
@isnad1 id=continuo.0h3v.s7.eb61da53b277 from=seed src=0 shape=40327c0a vocab=890882b7
-/
@[continuity, fun_prop]
lemma Hom.continuous {X Y : Scheme} (f : X ⟶ Y) : Continuous f := f.base.hom.2

/-- The structure sheaf of a scheme. -/
protected abbrev sheaf (X : Scheme) :=
  X.toSheafedSpace.sheaf

/--
We give schemes the specialization preorder by default.
-/
instance {X : Scheme.{u}} : Preorder X := specializationPreorder X

/--
@isnad1 id=iff.0h3v.s6.e3063b2cd391 from=seed src=0 shape=9115fa2d vocab=c0d7d592
-/
lemma le_iff_specializes {X : Scheme.{u}} {a b : X} : a ≤ b ↔ b ⤳ a := by rfl

open Order in
/--
@isnad1 id=eq.1h2v.s6.8a54bd032c8a from=seed src=0 shape=081aaeab vocab=fa8c1863
-/
lemma height_of_isClosed {X : Scheme} {x : X} (hx : IsClosed {x}) : height x = 0 := by
  simp only [height_eq_zero]
  intro b _
  obtain rfl | h := eq_or_ne b x
  · assumption
  · have := IsClosed.not_specializes hx rfl h
    contradiction

namespace Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens}

/-- Given a morphism of schemes `f : X ⟶ Y`, and open `U ⊆ Y`,
this is the induced map `Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ U)`.

This is treated as a suffix in lemma names. -/
abbrev app (U : Y.Opens) : Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ U) :=
  f.c.app (op U)

/-- Given a morphism of schemes `f : X ⟶ Y`, this is the induced map `Γ(Y, ⊤) ⟶ Γ(X, ⊤)`.
This is treated as a suffix in lemma names. -/
abbrev appTop : Γ(Y, ⊤) ⟶ Γ(X, ⊤) :=
  f.app ⊤

/--
@isnad1 id=eq.0h6v.s11.1cec00c5d3e5 from=seed src=0 shape=aec27b1a vocab=4ceb49a9
-/
@[reassoc]
lemma naturality (i : op U' ⟶ op U) :
    Y.presheaf.map i ≫ f.app U = f.app U' ≫ X.presheaf.map ((Opens.map f.base).map i.unop).op :=
  f.c.naturality i

/-- Given a morphism of schemes `f : X ⟶ Y`, and open sets `U ⊆ Y`, `V ⊆ f ⁻¹' U`,
this is the induced map `Γ(Y, U) ⟶ Γ(X, V)`.

This is treated as a suffix in lemma names. -/
def appLE (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) : Γ(Y, U) ⟶ Γ(X, V) :=
  f.app U ≫ X.presheaf.map (homOfLE e).op

/--
@isnad1 id=eq.1h7v.s10.54e60bb141ec from=seed src=0 shape=d98db70e vocab=f184610a
-/
@[reassoc (attr := simp)]
lemma appLE_map (e : V ≤ f ⁻¹ᵁ U) (i : op V ⟶ op V') :
    f.appLE U V e ≫ X.presheaf.map i = f.appLE U V' (i.unop.le.trans e) := by
  rw [Hom.appLE, Category.assoc, ← Functor.map_comp]
  rfl

/--
@isnad1 id=eq.2h6v.s10.7760a9eeb8c3 from=seed src=0 shape=7b96ebf1 vocab=84a7ce69
-/
@[reassoc]
lemma appLE_map' (e : V ≤ f ⁻¹ᵁ U) (i : V = V') :
    f.appLE U V' (i ▸ e) ≫ X.presheaf.map (eqToHom i).op = f.appLE U V e :=
  appLE_map _ _ _

/--
@isnad1 id=eq.1h7v.s10.51f1e7688475 from=seed src=0 shape=1e851d8b vocab=f184610a
-/
@[reassoc (attr := simp)]
lemma map_appLE (e : V ≤ f ⁻¹ᵁ U) (i : op U' ⟶ op U) :
    Y.presheaf.map i ≫ f.appLE U V e =
      f.appLE U' V (e.trans ((Opens.map f.base).map i.unop).le) := by
  rw [Hom.appLE, f.naturality_assoc, ← Functor.map_comp]
  rfl

/--
@isnad1 id=eq.2h6v.s10.d071d15554d8 from=seed src=0 shape=b0c2845f vocab=111659d2
-/
@[reassoc]
lemma map_appLE' (e : V ≤ f ⁻¹ᵁ U) (i : U' = U) :
    Y.presheaf.map (eqToHom i).op ≫ f.appLE U' V (i ▸ e) = f.appLE U V e :=
  map_appLE _ _ _

/--
@isnad1 id=eq.0h4v.s9.2eb79f348986 from=seed src=0 shape=25bbf94a vocab=3af26205
-/
lemma app_eq_appLE {U : Y.Opens} :
    f.app U = f.appLE U _ le_rfl := by
  simp [Hom.appLE]

/--
@isnad1 id=eq.0h4v.s8.c3e80618c89f from=seed src=0 shape=b3bb378a vocab=3af26205
-/
lemma appLE_eq_app {U : Y.Opens} :
    f.appLE U (f ⁻¹ᵁ U) le_rfl = f.app U :=
  (app_eq_appLE f).symm

/--
@isnad1 id=iff.3h8v.s10.d0022d52cbfc from=seed src=0 shape=812e6656 vocab=a3599977
-/
lemma appLE_congr (e : V ≤ f ⁻¹ᵁ U) (e₁ : U = U') (e₂ : V = V')
    (P : ∀ {R S : CommRingCat.{u}} (_ : R ⟶ S), Prop) :
    P (f.appLE U V e) ↔ P (f.appLE U' V' (e₁ ▸ e₂ ▸ e)) := by
  subst e₁; subst e₂; rfl

/-- A morphism of schemes `f : X ⟶ Y` induces a local ring homomorphism from
`Y.presheaf.stalk (f x)` to `X.presheaf.stalk x` for any `x : X`. -/
def stalkMap (x : X) : Y.presheaf.stalk (f x) ⟶ X.presheaf.stalk x :=
  f.toLRSHom.stalkMap x

/--
@isnad1 id=eq.2h4v.s12.1fc595529acc from=seed src=0 shape=307231f2 vocab=e69aea7d
-/
protected lemma ext {f g : X ⟶ Y} (h_base : f.base = g.base)
    (h_app : ∀ U, f.app U ≫ X.presheaf.map
      (eqToHom congr((Opens.map $h_base.symm).obj U)).op = g.app U) : f = g := by
  cases f; cases g; congr 1
  apply LocallyRingedSpace.Hom.ext'
  ext : 1
  · exact h_base
  · exact TopCat.Presheaf.ext (fun U ↦ by simpa using! h_app U)

/-- An alternative ext lemma for scheme morphisms.
@isnad1 id=eq.1h4v.s5.8772a8eb5c7d from=seed src=0 shape=fe7c8f1a vocab=49887dcd
-/
protected lemma ext' {f g : X ⟶ Y} (h : f.toLRSHom = g.toLRSHom) : f = g := by
  cases f; cases g; congr 1

/--
@isnad1 id=iff.0h5v.s8.dde198d27d10 from=seed src=0 shape=1399b005 vocab=a3a2914b
-/
lemma mem_preimage {x : X} {U : Opens Y} : x ∈ f ⁻¹ᵁ U ↔ f x ∈ U := .rfl

/--
@isnad1 id=eq.0h4v.s8.44da1b134a08 from=seed src=0 shape=7ca15b9c vocab=11dd1e15
-/
lemma coe_preimage {U : Opens Y} : f ⁻¹ᵁ U = f ⁻¹' U := rfl

/--
@isnad1 id=eq.0h5v.s8.6d426137c3a3 from=seed src=0 shape=b1561bd3 vocab=9a20c7ec
-/
lemma preimage_sup {U V : Opens Y} : f ⁻¹ᵁ (U ⊔ V) = f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V := rfl
/--
@isnad1 id=eq.0h5v.s8.697834d39bdc from=seed src=0 shape=b1561bd3 vocab=db09d1b7
-/
lemma preimage_inf {U V : Opens Y} : f ⁻¹ᵁ (U ⊓ V) = f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V := rfl
/--
@isnad1 id=eq.0h3v.s8.7d7ef555a81c from=seed src=0 shape=ed96841e vocab=a6055720
-/
@[simp] lemma preimage_top : f ⁻¹ᵁ ⊤ = ⊤ := rfl
/--
@isnad1 id=eq.0h3v.s8.6ecec06d50e5 from=seed src=0 shape=ed96841e vocab=37c15c16
-/
@[simp] lemma preimage_bot : f ⁻¹ᵁ ⊥ = ⊥ := rfl

/--
@isnad1 id=eq.0h5v.s8.ad631e991eb3 from=seed src=0 shape=8b840f4a vocab=7c23e291
-/
lemma preimage_iSup {ι} (U : ι → Opens Y) : f ⁻¹ᵁ iSup U = ⨆ i, f ⁻¹ᵁ U i :=
  Opens.ext (by simp)

/--
@isnad1 id=eq.1h5v.s8.fd7472e9f8b8 from=seed src=0 shape=1909aa3e vocab=38182989
-/
lemma iSup_preimage_eq_top {ι} {U : ι → Opens Y} (hU : iSup U = ⊤) :
    ⨆ i, f ⁻¹ᵁ U i = ⊤ := f.preimage_iSup U ▸ hU ▸ rfl

/--
@isnad1 id=le.1h5v.s8.6741d920db73 from=seed src=0 shape=102114d9 vocab=8b4475ec
-/
@[gcongr]
lemma preimage_mono {U U' : Y.Opens} (hUU' : U ≤ U') :
    f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U' :=
  fun _ ha ↦ hUU' ha

/--
@isnad1 id=eq.0h2v.s7.80c4b4f8c725 from=seed src=0 shape=b460cf38 vocab=0901baf1
-/
lemma id_preimage (U : X.Opens) : (𝟙 X) ⁻¹ᵁ U = U := rfl

/--
@isnad1 id=eq.0h6v.s8.62c3a8b8d84b from=seed src=0 shape=759191a9 vocab=6e6b36cb
-/
@[simp]
lemma comp_preimage {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (f ≫ g) ⁻¹ᵁ U = f ⁻¹ᵁ g ⁻¹ᵁ U := rfl

end Hom

/-- The forgetful functor from `Scheme` to `LocallyRingedSpace`. -/
@[simps!]
def forgetToLocallyRingedSpace : Scheme ⥤ LocallyRingedSpace where
  obj := toLocallyRingedSpace
  map := Hom.toLRSHom

/-- The forget functor `Scheme ⥤ LocallyRingedSpace` is fully faithful. -/
@[simps preimage_toLRSHom]
def fullyFaithfulForgetToLocallyRingedSpace :
    forgetToLocallyRingedSpace.FullyFaithful where
  preimage := Hom.mk

instance : forgetToLocallyRingedSpace.Full :=
  fullyFaithfulForgetToLocallyRingedSpace.full

instance : forgetToLocallyRingedSpace.Faithful :=
  fullyFaithfulForgetToLocallyRingedSpace.faithful

/-- The forgetful functor from `Scheme` to `TopCat`. -/
@[simps!]
def forgetToTop : Scheme ⥤ TopCat :=
  Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToTop

/-- An isomorphism of schemes induces a homeomorphism of the underlying topological spaces. -/
noncomputable def homeoOfIso {X Y : Scheme.{u}} (e : X ≅ Y) : X ≃ₜ Y :=
  TopCat.homeoOfIso (forgetToTop.mapIso e)

/--
@isnad1 id=eq.0h3v.s8.c353a1326a4c from=seed src=0 shape=81c5310f vocab=eada11da
-/
@[simp]
lemma coe_homeoOfIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    ⇑(homeoOfIso e) = e.hom := rfl

/--
@isnad1 id=eq.0h3v.s8.831647169371 from=seed src=0 shape=4758368a vocab=7246a4a0
-/
@[simp]
lemma coe_homeoOfIso_symm {X Y : Scheme.{u}} (e : X ≅ Y) :
    ⇑(homeoOfIso e.symm) = e.inv := rfl

/--
@isnad1 id=eq.0h3v.s6.731b0937f2d8 from=seed src=0 shape=ba8c4579 vocab=124e0a4f
-/
@[simp]
lemma homeoOfIso_symm {X Y : Scheme} (e : X ≅ Y) :
    (homeoOfIso e).symm = homeoOfIso e.symm := rfl

/--
@isnad1 id=eq.0h4v.s8.381e7558710c from=seed src=0 shape=d85d8dc7 vocab=eada11da
-/
lemma homeoOfIso_apply {X Y : Scheme} (e : X ≅ Y) (x : X) :
    homeoOfIso e x = e.hom x := rfl

alias _root_.CategoryTheory.Iso.schemeIsoToHomeo := homeoOfIso

/-- An isomorphism of schemes induces a homeomorphism of the underlying topological spaces. -/
noncomputable def Hom.homeomorph {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f] :
    X ≃ₜ Y :=
  (asIso f).schemeIsoToHomeo

/--
@isnad1 id=eq.0h4v.s8.ee00fa2e2f9a from=seed src=0 shape=e727e016 vocab=61180df4
-/
@[simp]
lemma Hom.homeomorph_apply {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f] (x) :
    f.homeomorph x = f x := rfl

instance hasCoeToTopCat : CoeOut Scheme TopCat where
  coe X := X.carrier

/-- forgetful functor to `TopCat` is the same as coercion -/
unif_hint forgetToTop_obj_eq_coe (X : Scheme) where ⊢ forgetToTop.obj X ≟ (X : TopCat)

/-- The forgetful functor from `Scheme` to `Type`. -/
nonrec def forget : Scheme.{u} ⥤ Type u := Scheme.forgetToTop ⋙ forget TopCat

/--
@isnad1 id=eq.0h0v.s5.627a3372427c from=seed src=0 shape=15e996be vocab=bf36837d
-/
lemma forgetToTop_comp_forget : forgetToTop ⋙ CategoryTheory.forget TopCat = forget := rfl

/-- forgetful functor to `Scheme` is the same as coercion -/
-- Schemes are often coerced as types, and it would be useful to have definitionally equal types
-- to be reducibly equal. The alternative is to make `forget` reducible but that option has
-- poor performance consequences.
unif_hint forget_obj_eq_coe (X : Scheme) where ⊢ forget.obj X ≟ (X : Type*)

/--
@isnad1 id=eq.0h1v.s4.aa46008bfe91 from=seed src=0 shape=ee8cb063 vocab=b5b5fd5b
-/
@[simp] lemma forget_obj (X) : Scheme.forget.obj X = X := rfl
/--
@isnad1 id=eq.0h3v.s8.7cede7685e88 from=seed src=0 shape=e18b6a04 vocab=965e9fe2
-/
lemma forget_map' {X Y} (f : X ⟶ Y) : (forget.map f : _ → _) = f := rfl
/--
@isnad1 id=eq.0h3v.s7.32b831e03c87 from=seed src=0 shape=dca405c1 vocab=6986d764
-/
@[simp] lemma forget_map {X Y} (f : X ⟶ Y) : forget.map f = ↾f := rfl

namespace Hom

/--
@isnad1 id=eq.0h1v.s6.ed4c32e71d57 from=seed src=0 shape=3479da71 vocab=0f302625
-/
@[simp]
theorem id_base (X : Scheme) : (𝟙 X :).base = 𝟙 _ :=
  rfl

/--
@isnad1 id=eq.0h2v.s8.7887be905c1f from=seed src=0 shape=52fd05f9 vocab=64e8ac54
-/
@[simp]
theorem id_app {X : Scheme} (U : X.Opens) :
    (𝟙 X :).app U = 𝟙 _ := rfl

/--
@isnad1 id=eq.0h1v.s9.73a820af3ac2 from=seed src=0 shape=e038ed7f vocab=0a8fc67c
-/
@[simp]
theorem id_appTop {X : Scheme} :
    (𝟙 X :).appTop = 𝟙 _ :=
  rfl

/--
@isnad1 id=eq.0h5v.s6.9ac2d0b3a8cf from=seed src=0 shape=b7ba3b21 vocab=1d42ccb0
-/
@[reassoc]
theorem comp_toLRSHom {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toLRSHom = f.toLRSHom ≫ g.toLRSHom :=
  rfl

/--
@isnad1 id=eq.0h5v.s7.340315f39de5 from=seed src=0 shape=5d417cc4 vocab=a606e2f5
-/
@[simp, reassoc]
theorem comp_base {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

/--
@isnad1 id=eq.0h6v.s9.d1ae4823a53a from=seed src=0 shape=842ede5d vocab=c9e49479
-/
theorem comp_apply {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by
  simp

/--
@isnad1 id=eq.0h6v.s10.aa42712df81f from=seed src=0 shape=0890623d vocab=ff32d640
-/
@[simp, reassoc] -- reassoc lemma does not need `simp`
theorem comp_app {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (f ≫ g).app U = g.app U ≫ f.app _ :=
  rfl

/--
@isnad1 id=eq.0h5v.s10.e19b91b548f2 from=seed src=0 shape=e3739bd5 vocab=c8028efb
-/
@[simp, reassoc] -- reassoc lemma does not need `simp`
theorem comp_appTop {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).appTop = g.appTop ≫ f.appTop :=
  rfl

/--
@isnad1 id=eq.2h8v.s10.738e773bba86 from=seed src=0 shape=ef675c20 vocab=fc6e28f6
-/
@[reassoc]
theorem appLE_comp_appLE {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U V W e₁ e₂) :
    g.appLE U V e₁ ≫ f.appLE V W e₂ =
      (f ≫ g).appLE U W (e₂.trans ((Opens.map f.base).map (homOfLE e₁)).le) := by
  dsimp [Hom.appLE]
  rw [Category.assoc, f.naturality_assoc, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.1h7v.s10.d8045f79e5ee from=seed src=0 shape=2cf81b22 vocab=eda741b8
-/
@[simp, reassoc] -- reassoc lemma does not need `simp`
theorem comp_appLE {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U V e) :
    (f ≫ g).appLE U V e = g.app U ≫ f.appLE _ V e := by
  rw [g.app_eq_appLE, appLE_comp_appLE]

/--
@isnad1 id=eq.1h5v.s10.90a5cec73932 from=seed src=0 shape=07a694d6 vocab=a863268a
-/
theorem congr_app {X Y : Scheme} {f g : X ⟶ Y} (e : f = g) (U) :
    f.app U = g.app U ≫ X.presheaf.map (eqToHom (by subst e; rfl)).op := by
  subst e; simp

/--
@isnad1 id=eq.1h5v.s11.faa072f1df69 from=seed src=0 shape=d79c1f08 vocab=87f3160f
-/
theorem app_eq {X Y : Scheme} (f : X ⟶ Y) {U V : Y.Opens} (e : U = V) :
    f.app U =
      Y.presheaf.map (eqToHom e.symm).op ≫ f.app V ≫ X.presheaf.map (eqToHom (e ▸ rfl)).op := by
  aesop

/--
@isnad1 id=eq.1h3v.s9.d20f68563e4a from=seed src=0 shape=ecb1d10a vocab=e12eee56
-/
theorem eqToHom_app {X Y : Scheme} (e : X = Y) (U) :
    (eqToHom e).app U = eqToHom (by subst e; rfl) := by subst e; rfl

/--
@isnad1 id=isiso.0h3v.s5.7abf08ae6597 from=seed src=0 shape=2683812d vocab=d64c1d94
-/
instance isIso_toLRSHom {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : IsIso f.toLRSHom :=
  forgetToLocallyRingedSpace.map_isIso f

/--
@isnad1 id=isiso.0h3v.s6.165df9967f2d from=seed src=0 shape=9c7e9c64 vocab=6301d185
-/
instance isIso_toPshHom {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : IsIso f.toPshHom :=
  inferInstanceAs (IsIso ((LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace).map f.toLRSHom))

/--
@isnad1 id=isiso.0h3v.s6.7c69948f2720 from=seed src=0 shape=d683b5d3 vocab=6c465a9b
-/
instance isIso_base {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : IsIso f.base :=
  Scheme.forgetToTop.map_isIso f

instance {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U) : IsIso (f.app U) :=
  haveI := PresheafedSpace.c_isIso_of_iso f.toPshHom
  NatIso.isIso_app_of_isIso f.c _

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h4v.s11.430717f60287 from=seed src=0 shape=525c2067 vocab=d927e513
-/
@[simp]
theorem inv_app {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U : X.Opens) :
    (inv f).app U =
      X.presheaf.map (eqToHom (show (f ≫ inv f) ⁻¹ᵁ U = U by rw [IsIso.hom_inv_id]; rfl)).op ≫
        inv (f.app ((inv f) ⁻¹ᵁ U)) := by
  rw [IsIso.eq_comp_inv, ← comp_app, congr_app (IsIso.hom_inv_id f), id_app, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h3v.s9.54ee83122d2f from=seed src=0 shape=332b4a6b vocab=25aadcd9
-/
theorem inv_appTop {X Y : Scheme} (f : X ⟶ Y) [IsIso f] :
    (inv f).appTop = inv f.appTop := by simp

/-- Copies a morphism with a different underlying map -/
def copyBase {X Y : Scheme} (f : X.Hom Y) (g : X → Y) (h : f.base = g) : X ⟶ Y where
  base := TopCat.ofHom ⟨g, h ▸ f.base.1.2⟩
  c := f.c ≫ (TopCat.Presheaf.pushforwardEq (by subst h; rfl) _).hom
  prop x := by
    subst h
    convert! f.prop x using 4
    cat_disch

/--
@isnad1 id=eq.1h4v.s7.1f382d2d46a6 from=seed src=0 shape=2c49ba56 vocab=874d8e3e
-/
lemma copyBase_eq {X Y : Scheme} (f : X.Hom Y) (g : X → Y) (h : f.base = g) :
    f.copyBase g h = f := by
  subst h
  obtain ⟨⟨⟨f₁, f₂⟩, f₃⟩, f₄⟩ := f
  simp only [Hom.copyBase]
  congr
  cat_disch

end Hom

end Scheme

/-- The spectrum of a commutative ring, as a scheme. -/
def Spec (R : CommRingCat) : Scheme where
  local_affine _ := ⟨⟨⊤, trivial⟩, R, ⟨(Spec.toLocallyRingedSpace.obj (op R)).restrictTopIso⟩⟩
  toLocallyRingedSpace := Spec.locallyRingedSpaceObj R

/--
@isnad1 id=eq.0h1v.s3.097e21ab6f63 from=seed src=0 shape=7718e021 vocab=475aff34
-/
theorem Spec_toLocallyRingedSpace (R : CommRingCat) :
    (Spec R).toLocallyRingedSpace = Spec.locallyRingedSpaceObj R :=
  rfl

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of schemes. -/
def Spec.map {R S : CommRingCat} (f : R ⟶ S) : Spec S ⟶ Spec R :=
  ⟨Spec.locallyRingedSpaceMap f⟩

/--
@isnad1 id=eq.0h1v.s4.ac0dec853a10 from=seed src=0 shape=b11b3d58 vocab=e2c5bc5a
-/
@[simp]
theorem Spec.map_id (R : CommRingCat) : Spec.map (𝟙 R) = 𝟙 (Spec R) :=
  Scheme.Hom.ext' <| Spec.locallyRingedSpaceMap_id R

/--
@isnad1 id=eq.0h5v.s6.6d485b052117 from=seed src=0 shape=e9cd887f vocab=3de41be7
-/
@[reassoc, simp]
theorem Spec.map_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.map (f ≫ g) = Spec.map g ≫ Spec.map f :=
  Scheme.Hom.ext' <| Spec.locallyRingedSpaceMap_comp f g

/-- The spectrum, as a contravariant functor from commutative rings to schemes. -/
@[simps, implicit_reducible]
protected def Scheme.Spec : CommRingCatᵒᵖ ⥤ Scheme where
  obj R := Spec (unop R)
  map f := Spec.map f.unop
  map_id R := by simp
  map_comp f g := by simp

/--
@isnad1 id=eq.1h2v.s5.8cebbf22a94d from=seed src=0 shape=4a5b220c vocab=fdeac9cd
-/
lemma Spec.map_eqToHom {R S : CommRingCat} (e : R = S) :
    Spec.map (eqToHom e) = eqToHom (e ▸ rfl) := by
  subst e; exact Spec.map_id _

instance {R S : CommRingCat} (f : R ⟶ S) [IsIso f] : IsIso (Spec.map f) :=
  inferInstanceAs (IsIso <| Scheme.Spec.map f.op)

/--
@isnad1 id=eq.0h3v.s5.269aa7bbf418 from=seed src=0 shape=e24b0105 vocab=b2f43817
-/
@[simp]
lemma Spec.map_inv {R S : CommRingCat} (f : R ⟶ S) [IsIso f] :
    Spec.map (inv f) = inv (Spec.map f) := by
  change Scheme.Spec.map (inv f).op = inv (Scheme.Spec.map f.op)
  rw [op_inv, ← Scheme.Spec.map_inv]

/-- `Spec R` with the specialization order is order isomorphic to the dual of the prime
spectrum of `R`. -/
@[simps]
def specOrderIsoPrimeSpectrum (R : CommRingCat) : Spec R ≃o (PrimeSpectrum R)ᵒᵈ where
  toFun x := .toDual x
  invFun x := OrderDual.ofDual x
  map_rel_iff' {a b} := PrimeSpectrum.le_iff_specializes b a

/-- `PrimeSpectrum R` with the inclusion order is order isomorphic to the dual of `Spec R`. -/
@[simps]
def primeSpectrumOrderIsoSpec (R : Type u) [CommRing R] : PrimeSpectrum R ≃o (Spec (.of R))ᵒᵈ where
  toFun x := .toDual x
  invFun x := OrderDual.ofDual x
  map_rel_iff' {a b} := (PrimeSpectrum.le_iff_specializes a b).symm

section

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

-- The lemmas below are not tagged simp to respect the abstraction.
/--
@isnad1 id=eq.0h1v.s4.0cdefb01f0f7 from=seed src=0 shape=55041ccc vocab=3c03e973
-/
lemma Spec_carrier (R : CommRingCat.{u}) : (Spec R).carrier = PrimeSpectrum R := rfl
/--
@isnad1 id=eq.0h1v.s4.4a0f1c94f81c from=seed src=0 shape=7440f9c3 vocab=3944d0c9
-/
lemma Spec_sheaf (R : CommRingCat.{u}) : (Spec R).sheaf = Spec.structureSheaf R := rfl
/--
@isnad1 id=eq.0h1v.s7.e083e91715c7 from=seed src=0 shape=951d8f85 vocab=37c58294
-/
lemma Spec_presheaf (R : CommRingCat.{u}) : (Spec R).presheaf = (Spec.structureSheaf R).1 := rfl
/--
@isnad1 id=eq.0h3v.s7.bd9c811b275e from=seed src=0 shape=a334e84f vocab=17371034
-/
lemma Spec.map_base : (Spec.map f).base = ofHom ⟨_, PrimeSpectrum.continuous_comap f.hom⟩ := rfl
/--
@isnad1 id=eq.0h4v.s7.b85359054236 from=seed src=0 shape=c5c69969 vocab=7c0bf1ef
-/
lemma Spec.map_apply (x : Spec S) : Spec.map f x = PrimeSpectrum.comap f.hom x := rfl

/--
@isnad1 id=eq.0h4v.s10.d4f7ef96c6f8 from=seed src=0 shape=ee369b0a vocab=8ada82eb
-/
lemma Spec.map_app (U) :
    (Spec.map f).app U =
      CommRingCat.ofHom (StructureSheaf.comap f.hom U (Spec.map f ⁻¹ᵁ U) le_rfl) := rfl

/--
@isnad1 id=eq.1h5v.s10.9fd5aa758edb from=seed src=0 shape=4bab1fb0 vocab=9a28c73f
-/
lemma Spec.map_appLE {U V} (e : U ≤ Spec.map f ⁻¹ᵁ V) :
    (Spec.map f).appLE V U e = CommRingCat.ofHom (StructureSheaf.comap f.hom V U e) := rfl

instance {A : CommRingCat} [Nontrivial A] : Nonempty (Spec A) :=
  inferInstanceAs <| Nonempty (PrimeSpectrum A)

end

namespace Scheme

/--
@isnad1 id=isempty.2h8v.s9.f627fbe2ce2b from=seed src=0 shape=888ab2b3 vocab=75faeca7
-/
theorem isEmpty_of_commSq {W X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {i : W ⟶ X} {j : W ⟶ Y} (h : CommSq i j f g)
    (H : Disjoint (Set.range f) (Set.range g)) : IsEmpty W :=
  ⟨fun x ↦ (Set.disjoint_iff_inter_eq_empty.mp H).le
    ⟨⟨i x, congr($(h.w) x)⟩, ⟨j x, rfl⟩⟩⟩

/-- The empty scheme. -/
@[simps]
def empty : Scheme where
  carrier := TopCat.of PEmpty
  presheaf := (CategoryTheory.Functor.const _).obj (CommRingCat.of PUnit)
  IsSheaf := Presheaf.isSheaf_of_isTerminal _ CommRingCat.punitIsTerminal
  isLocalRing x := PEmpty.elim x
  local_affine x := PEmpty.elim x

instance : EmptyCollection Scheme :=
  ⟨empty⟩

/-- The global sections as a functor. For the global section themselves, use `Γ(X, ⊤)` instead. -/
def Γ : Schemeᵒᵖ ⥤ CommRingCat :=
  Scheme.forgetToLocallyRingedSpace.op ⋙ LocallyRingedSpace.Γ

/--
@isnad1 id=eq.0h0v.s4.b228e11eef94 from=seed src=0 shape=f23915d6 vocab=4e4eab9a
-/
theorem Γ_def : Γ = Scheme.forgetToLocallyRingedSpace.op ⋙ LocallyRingedSpace.Γ :=
  rfl

/--
@isnad1 id=eq.0h1v.s8.6e78d5b8a739 from=seed src=0 shape=21a8ae52 vocab=e3ea93c0
-/
@[simp]
theorem Γ_obj (X : Schemeᵒᵖ) : Γ.obj X = Γ(unop X, ⊤) :=
  rfl

/--
@isnad1 id=eq.0h1v.s7.670c6ca78751 from=seed src=0 shape=d5cfdd2b vocab=89eb59ec
-/
theorem Γ_obj_op (X : Scheme) : Γ.obj (op X) = Γ(X, ⊤) :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.5227782c32d9 from=seed src=0 shape=5496dd23 vocab=9f1b11d9
-/
@[simp]
theorem Γ_map {X Y : Schemeᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.appTop :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.2f7619d85222 from=seed src=0 shape=e0a5d352 vocab=a1cc38e3
-/
theorem Γ_map_op {X Y : Scheme} (f : X ⟶ Y) : Γ.map f.op = f.appTop :=
  rfl

/--
The counit (`SpecΓIdentity.inv.op`) of the adjunction `Γ ⊣ Spec` as a natural isomorphism.
This is almost never needed in practical use cases. Use `ΓSpecIso` instead.
-/
def SpecΓIdentity : Scheme.Spec.rightOp ⋙ Scheme.Γ ≅ 𝟭 _ :=
  LocallyRingedSpace.SpecΓIdentity

variable (R : CommRingCat.{u})

/-- The global sections of `Spec R` is isomorphic to `R`. -/
def ΓSpecIso : Γ(Spec R, ⊤) ≅ R := SpecΓIdentity.app R

/--
@isnad1 id=eq.0h1v.s6.d2dfdab97748 from=seed src=0 shape=51210725 vocab=463c9f46
-/
@[simp] lemma SpecΓIdentity_app : SpecΓIdentity.app R = ΓSpecIso R := rfl
/--
@isnad1 id=eq.0h1v.s8.d0382f81dd16 from=seed src=0 shape=358c7ca0 vocab=47ff54e1
-/
@[simp] lemma SpecΓIdentity_hom_app : SpecΓIdentity.hom.app R = (ΓSpecIso R).hom := rfl
/--
@isnad1 id=eq.0h1v.s8.5d3f1eac7dba from=seed src=0 shape=730bcb05 vocab=f939a009
-/
@[simp] lemma SpecΓIdentity_inv_app : SpecΓIdentity.inv.app R = (ΓSpecIso R).inv := rfl

/--
@isnad1 id=eq.0h3v.s10.e59269120a03 from=seed src=0 shape=05666b74 vocab=3baddae6
-/
@[reassoc (attr := simp)]
lemma ΓSpecIso_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (Spec.map f).appTop ≫ (ΓSpecIso S).hom = (ΓSpecIso R).hom ≫ f := SpecΓIdentity.hom.naturality f

-- The RHS is not necessarily simpler than the LHS, but this direction coincides with the simp
-- direction of `NatTrans.naturality`.
/--
@isnad1 id=eq.0h3v.s10.5503e47f163e from=seed src=0 shape=3d0527de vocab=7a7b3bb5
-/
@[reassoc (attr := simp)]
lemma ΓSpecIso_inv_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f ≫ (ΓSpecIso S).inv = (ΓSpecIso R).inv ≫ (Spec.map f).appTop := SpecΓIdentity.inv.naturality f

set_option backward.isDefEq.respectTransparency.types false in
-- This is not marked simp to respect the abstraction
/--
@isnad1 id=eq.0h1v.s11.0f6d6551d322 from=seed src=0 shape=6ec66e61 vocab=7bcebea4
-/
lemma ΓSpecIso_inv : (ΓSpecIso R).inv = CommRingCat.ofHom (algebraMap _ _) := rfl

/--
@isnad1 id=eq.0h2v.s11.6ee9036c86df from=seed src=0 shape=3d664c6b vocab=644ab9dd
-/
lemma toOpen_eq (U) :
    CommRingCat.ofHom (algebraMap R <| (Spec.structureSheaf R).presheaf.obj (.op U)) =
    (ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE le_top).op := rfl

instance {K} [Field K] : Unique <| Spec <| .of K :=
  inferInstanceAs <| Unique (PrimeSpectrum K)

/--
@isnad1 id=eq.0h1v.s7.b3031e304930 from=seed src=0 shape=a357774f vocab=2e85515a
-/
@[simp]
lemma default_asIdeal {K} [Field K] : (default : Spec (.of K)).asIdeal = ⊥ := rfl

section BasicOpen

variable (X : Scheme) {V U : X.Opens} (f g : Γ(X, U))

/-- The subset of the underlying space where the given section does not vanish. -/
def basicOpen : X.Opens :=
  X.toLocallyRingedSpace.toRingedSpace.basicOpen f

/--
@isnad1 id=iff.1h4v.s10.207746be5aea from=seed src=0 shape=af9bd01c vocab=65cf45c5
-/
theorem mem_basicOpen (x : X) (hx : x ∈ U) :
    x ∈ X.basicOpen f ↔ IsUnit (X.presheaf.germ U x hx f) :=
  RingedSpace.mem_basicOpen _ _ _ _

/-- A variant of `mem_basicOpen` for bundled `x : U`.
@isnad1 id=iff.0h4v.s11.7eadbac96aa8 from=seed src=0 shape=04ce8984 vocab=016eeb61
-/
@[simp]
theorem mem_basicOpen' (x : U) : ↑x ∈ X.basicOpen f ↔ IsUnit (X.presheaf.germ U x x.2 f) :=
  RingedSpace.mem_basicOpen _ _ _ _

/-- A variant of `mem_basicOpen` without the `x ∈ U` assumption.
@isnad1 id=iff.0h4v.s10.000b94b4f371 from=seed src=0 shape=a7b3457e vocab=65cf45c5
-/
theorem mem_basicOpen'' {U : X.Opens} (f : Γ(X, U)) (x : X) :
    x ∈ X.basicOpen f ↔ ∃ (m : x ∈ U), IsUnit (X.presheaf.germ U x m f) :=
  Iff.rfl

/--
@isnad1 id=iff.0h3v.s11.54458575c3f0 from=seed src=0 shape=83be5d94 vocab=70683df7
-/
theorem mem_basicOpen_top (f : Γ(X, ⊤)) (x : X) :
    x ∈ X.basicOpen f ↔ IsUnit (X.presheaf.germ ⊤ x trivial f) :=
  RingedSpace.mem_top_basicOpen _ f x

/--
@isnad1 id=eq.0h5v.s10.26ec984ced22 from=seed src=0 shape=5b923836 vocab=cb53c70b
-/
@[simp]
theorem basicOpen_res (i : op U ⟶ op V) : X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f :=
  RingedSpace.basicOpen_res _ i f

-- This should fire before `basicOpen_res`.
/--
@isnad1 id=eq.0h5v.s10.68bf56bcb04a from=seed src=0 shape=ca13fbec vocab=053e8d39
-/
@[simp 1100]
theorem basicOpen_res_eq (i : op U ⟶ op V) [IsIso i] :
    X.basicOpen (X.presheaf.map i f) = X.basicOpen f :=
  RingedSpace.basicOpen_res_eq _ i f

/--
@isnad1 id=le.0h3v.s7.bf0ce4fc3437 from=seed src=0 shape=7c0d4e1e vocab=0b4a2c8f
-/
@[sheaf_restrict]
theorem basicOpen_le : X.basicOpen f ≤ U :=
  RingedSpace.basicOpen_le _ _

/--
@isnad1 id=le.0h5v.s8.7d30711f9844 from=seed src=0 shape=c1ff2600 vocab=795de5d4
-/
@[sheaf_restrict]
lemma basicOpen_restrict (i : V ⟶ U) (f : Γ(X, U)) :
    X.basicOpen (TopCat.Presheaf.restrict f i) ≤ X.basicOpen f :=
  (Scheme.basicOpen_res _ _ _).trans_le inf_le_right

/--
@isnad1 id=eq.0h5v.s11.8ad451ef02b0 from=seed src=0 shape=7a76a7a5 vocab=e27eb57d
-/
@[simp]
theorem preimage_basicOpen {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (r : Γ(Y, U)) :
    f ⁻¹ᵁ Y.basicOpen r = X.basicOpen (f.app U r) :=
  LocallyRingedSpace.preimage_basicOpen f.toLRSHom r

/--
@isnad1 id=eq.0h5v.s11.8ad451ef02b0 from=seed src=0 shape=7a76a7a5 vocab=e27eb57d
-/
alias Hom.preimage_basicOpen := preimage_basicOpen

/--
@isnad1 id=eq.0h4v.s11.4ab52c984986 from=seed src=0 shape=d258985c vocab=d3bb0c3c
-/
theorem preimage_basicOpen_top {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(Y, ⊤)) :
    f ⁻¹ᵁ Y.basicOpen r = X.basicOpen (f.appTop r) :=
  preimage_basicOpen ..

/--
@isnad1 id=eq.0h4v.s11.4ab52c984986 from=seed src=0 shape=d258985c vocab=d3bb0c3c
-/
alias Hom.preimage_basicOpen_top := preimage_basicOpen_top

/--
@isnad1 id=eq.1h6v.s10.6ee18f774c42 from=seed src=0 shape=4bc5b7bf vocab=f6890741
-/
lemma basicOpen_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e : U ≤ f ⁻¹ᵁ V)
    (s : Γ(Y, V)) : X.basicOpen (f.appLE V U e s) = U ⊓ f ⁻¹ᵁ (Y.basicOpen s) := by
  simp only [preimage_basicOpen, Hom.appLE, CommRingCat.comp_apply]
  rw [basicOpen_res]

/--
@isnad1 id=eq.0h2v.s9.d29bdd5613e5 from=seed src=0 shape=4d6ed3ea vocab=3fda94cf
-/
@[simp]
theorem basicOpen_zero (U : X.Opens) : X.basicOpen (0 : Γ(X, U)) = ⊥ :=
  LocallyRingedSpace.basicOpen_zero _ U

/--
@isnad1 id=eq.0h4v.s10.541afca6fa55 from=seed src=0 shape=ec78aa54 vocab=ab75c1db
-/
@[simp]
theorem basicOpen_mul : X.basicOpen (f * g) = X.basicOpen f ⊓ X.basicOpen g :=
  RingedSpace.basicOpen_mul _ _ _

/--
@isnad1 id=eq.1h4v.s10.457a24c6a1e5 from=seed src=0 shape=1464cab1 vocab=ed90d0f4
-/
lemma basicOpen_pow {n : ℕ} (h : 0 < n) : X.basicOpen (f ^ n) = X.basicOpen f :=
  RingedSpace.basicOpen_pow _ _ _ h

/--
@isnad1 id=le.0h4v.s10.2d99f9e62e5c from=seed src=0 shape=ec78aa54 vocab=0a5e4af0
-/
lemma basicOpen_add_le :
    X.basicOpen (f + g) ≤ X.basicOpen f ⊔ X.basicOpen g := by
  intro x hx
  have hxU : x ∈ U := X.basicOpen_le _ hx
  simp_rw [← SetLike.mem_coe, Opens.coe_sup, Set.mem_union, SetLike.mem_coe] -- TODO : Opens.mem_sup
  simp only [Scheme.mem_basicOpen _ _ _ hxU, map_add] at hx ⊢
  exact IsLocalRing.isUnit_or_isUnit_of_isUnit_add hx

/--
@isnad1 id=eq.1h3v.s9.74f19a057449 from=seed src=0 shape=1397b543 vocab=be0f23bb
-/
theorem basicOpen_of_isUnit {f : Γ(X, U)} (hf : IsUnit f) : X.basicOpen f = U :=
  RingedSpace.basicOpen_of_isUnit _ hf

/--
@isnad1 id=eq.0h2v.s9.edbd1c73b127 from=seed src=0 shape=503f63fa vocab=333b4de3
-/
@[simp]
theorem basicOpen_one : X.basicOpen (1 : Γ(X, U)) = U :=
  X.basicOpen_of_isUnit isUnit_one

instance algebra_section_section_basicOpen {X : Scheme} {U : X.Opens} (f : Γ(X, U)) :
    Algebra Γ(X, U) Γ(X, X.basicOpen f) :=
  (X.presheaf.map (homOfLE <| X.basicOpen_le f : _ ⟶ U).op).hom.toAlgebra

@[simp]
lemma _root_.AlgebraicGeometry.SpecMap_preimage_basicOpen {R S : CommRingCat} (f : R ⟶ S) (r : R) :
    Spec.map f ⁻¹ᵁ PrimeSpectrum.basicOpen r = PrimeSpectrum.basicOpen (f r) := rfl

end BasicOpen

section ZeroLocus

variable (X : Scheme.{u})

/--
The zero locus of a set of sections `s` over an open set `U` is the closed set consisting of
the complement of `U` and of all points of `U`, where all elements of `f` vanish.
-/
def zeroLocus {U : X.Opens} (s : Set Γ(X, U)) : Set X := X.toRingedSpace.zeroLocus s

/--
@isnad1 id=eq.0h3v.s10.dc08acad5cde from=seed src=0 shape=f2b87bc6 vocab=a1ce57d2
-/
lemma zeroLocus_def {U : X.Opens} (s : Set Γ(X, U)) :
    X.zeroLocus s = ⋂ f ∈ s, (X.basicOpen f).carrierᶜ :=
  rfl

/--
@isnad1 id=isclosed.0h3v.s7.604e1b586e09 from=seed src=0 shape=bc7dbdcb vocab=43c1fdc9
-/
lemma zeroLocus_isClosed {U : X.Opens} (s : Set Γ(X, U)) :
    IsClosed (X.zeroLocus s) :=
  X.toRingedSpace.zeroLocus_isClosed s

/--
@isnad1 id=eq.0h3v.s9.d413a5aafef8 from=seed src=0 shape=7e8ae576 vocab=010b2a2f
-/
lemma zeroLocus_singleton {U : X.Opens} (f : Γ(X, U)) :
    X.zeroLocus {f} = (↑(X.basicOpen f))ᶜ :=
  X.toRingedSpace.zeroLocus_singleton f

/--
@isnad1 id=eq.0h2v.s8.515314f2585a from=seed src=0 shape=60abcfa4 vocab=5f123462
-/
@[simp]
lemma zeroLocus_empty_eq_univ {U : X.Opens} :
    X.zeroLocus (∅ : Set Γ(X, U)) = Set.univ :=
  X.toRingedSpace.zeroLocus_empty_eq_univ

/--
@isnad1 id=iff.0h4v.s9.801d19fb8b09 from=seed src=0 shape=3c71bf15 vocab=c80169d2
-/
@[simp]
lemma mem_zeroLocus_iff {U : X.Opens} (s : Set Γ(X, U)) (x : X) :
    x ∈ X.zeroLocus s ↔ ∀ f ∈ s, x ∉ X.basicOpen f :=
  X.toRingedSpace.mem_zeroLocus_iff s x

/--
@isnad1 id=codisjoi.0h3v.s7.f113d3aa953a from=seed src=0 shape=9d277cc5 vocab=d7d91ea6
-/
lemma codisjoint_zeroLocus {U : X.Opens}
    (s : Set Γ(X, U)) : Codisjoint (X.zeroLocus s) U := by
  have (x : X) : ∀ f ∈ s, x ∈ X.basicOpen f → x ∈ U := fun _ _ h ↦ X.basicOpen_le _ h
  simpa [codisjoint_iff_le_sup, Set.ext_iff, or_iff_not_imp_left]

/--
@isnad1 id=eq.0h3v.s11.d4454a042004 from=seed src=0 shape=7a4d09e9 vocab=a3824464
-/
lemma zeroLocus_span {U : X.Opens} (s : Set Γ(X, U)) :
    X.zeroLocus (U := U) (Ideal.span s) = X.zeroLocus s := by
  ext x
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe]
  refine ⟨fun H f hfs ↦ H f (Ideal.subset_span hfs), fun H f ↦ Submodule.span_induction H ?_ ?_ ?_⟩
  · simp only [Scheme.basicOpen_zero]; exact not_false
  · exact fun a b _ _ ha hb H ↦ (X.basicOpen_add_le a b H).elim ha hb
  · simp +contextual

open scoped Pointwise in
/--
@isnad1 id=eq.0h4v.s10.2b8ffc3dd594 from=seed src=0 shape=7818ca64 vocab=335e7a0c
-/
lemma zeroLocus_setMul {U : X.Opens} (s t : Set Γ(X, U)) :
    X.zeroLocus (s * t) = X.zeroLocus s ∪ X.zeroLocus t := by
  simp only [← Set.image2_mul, zeroLocus_def, Set.biInter_image2]
  simp [Set.compl_inter, ← Set.union_iInter₂, ← Set.iInter₂_union]

open scoped Pointwise in
/--
@isnad1 id=eq.0h4v.s13.85bf03bfbfc1 from=seed src=0 shape=1f163e4c vocab=3fe30135
-/
lemma zeroLocus_mul {U : X.Opens} (I J : Ideal Γ(X, U)) :
    X.zeroLocus (U := U) ↑(I * J) = X.zeroLocus (U := U) I ∪ X.zeroLocus (U := U) J := by
  rw [← X.zeroLocus_setMul, ← X.zeroLocus_span (U := U) (↑I * ↑J), ← Ideal.span_mul_span]
  simp

/--
@isnad1 id=eq.1h4v.s11.dd7638e0c646 from=seed src=0 shape=967f3f60 vocab=d6f3a39a
-/
lemma zeroLocus_map {U V : X.Opens} (i : U ≤ V) (s : Set Γ(X, V)) :
    X.zeroLocus ((X.presheaf.map (homOfLE i).op).hom '' s) = X.zeroLocus s ∪ Uᶜ := by
  ext x
  suffices (∀ f ∈ s, x ∈ U → x ∉ X.basicOpen f) ↔ x ∈ U → (∀ f ∈ s, x ∉ X.basicOpen f) by
    simpa [or_iff_not_imp_right]
  grind

/--
@isnad1 id=eq.1h4v.s11.ebe2b6dbda29 from=seed src=0 shape=4c6d1c5b vocab=250ff379
-/
lemma zeroLocus_map_of_eq {U V : X.Opens} (i : U = V) (s : Set Γ(X, V)) :
    X.zeroLocus ((X.presheaf.map (eqToHom i).op).hom '' s) = X.zeroLocus s := by
  ext; simp

/--
@isnad1 id=le.1h4v.s9.8044e7fa65d3 from=seed src=0 shape=8d58cbe6 vocab=29b2a104
-/
lemma zeroLocus_mono {U : X.Opens} {s t : Set Γ(X, U)} (h : s ⊆ t) :
    X.zeroLocus t ⊆ X.zeroLocus s := by
  simp only [Set.subset_def, Scheme.mem_zeroLocus_iff]
  exact fun x H f hf hxf ↦ H f (h hf) hxf

/--
@isnad1 id=eq.0h5v.s12.fdbae7c510db from=seed src=0 shape=7c7c8ff7 vocab=a458d8b8
-/
lemma preimage_zeroLocus {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (s : Set Γ(Y, U)) :
    f ⁻¹' Y.zeroLocus s = X.zeroLocus ((f.app U).hom '' s) := by
  ext
  simp [← Scheme.preimage_basicOpen]

/--
@isnad1 id=eq.0h2v.s7.63953ea2a338 from=seed src=0 shape=359ff14e vocab=ace3af03
-/
@[simp]
lemma zeroLocus_univ {U : X.Opens} :
    X.zeroLocus (U := U) Set.univ = (↑U)ᶜ := by
  ext x
  simp only [Scheme.mem_zeroLocus_iff, Set.mem_univ, forall_const, Set.mem_compl_iff,
    SetLike.mem_coe, ← not_exists, not_iff_not]
  exact ⟨fun ⟨f, hf⟩ ↦ X.basicOpen_le f hf, fun _ ↦ ⟨1, by rwa [X.basicOpen_of_isUnit isUnit_one]⟩⟩

/--
@isnad1 id=eq.0h4v.s8.dfe1c8c455e3 from=seed src=0 shape=27f17ef2 vocab=58bad229
-/
lemma zeroLocus_iUnion {U : X.Opens} {ι : Type*} (f : ι → Set Γ(X, U)) :
    X.zeroLocus (⋃ i, f i) = ⋂ i, X.zeroLocus (f i) := by
  simpa [zeroLocus, AlgebraicGeometry.RingedSpace.zeroLocus] using Set.iInter_comm _

/--
@isnad1 id=eq.0h3v.s12.bd6d9aafec97 from=seed src=0 shape=3bdc7cc2 vocab=06ec14d4
-/
lemma zeroLocus_radical {U : X.Opens} (I : Ideal Γ(X, U)) :
    X.zeroLocus (U := U) I.radical = X.zeroLocus (U := U) I := by
  refine (X.zeroLocus_mono I.le_radical).antisymm ?_
  simp only [Set.subset_def, mem_zeroLocus_iff, SetLike.mem_coe]
  rintro x H f ⟨n, hn⟩ hx
  rcases n.eq_zero_or_pos with rfl | hn'
  · exact H f (by simpa using I.mul_mem_left f hn) hx
  · exact H _ hn (X.basicOpen_pow f hn' ▸ hx)

end ZeroLocus

end Scheme

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h2v.s10.59e060d5ed77 from=seed src=0 shape=6246673e vocab=f021fb21
-/
theorem basicOpen_eq_of_affine {R : CommRingCat} (f : R) :
    (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv f) = PrimeSpectrum.basicOpen f := by
  ext x
  simp only [SetLike.mem_coe, Scheme.mem_basicOpen_top]
  suffices IsUnit (algebraMap _ ((structurePresheafInCommRingCat ↑R).stalk x) f) ↔
    f ∉ PrimeSpectrum.asIdeal x by exact this
  rw [← isUnit_map_iff (StructureSheaf.stalkIso R x).symm, AlgEquiv.commutes]
  exact IsLocalization.AtPrime.isUnit_to_map_iff _ (PrimeSpectrum.asIdeal x) f

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h2v.s10.f74895678ab9 from=seed src=0 shape=f00b8517 vocab=5e5550b2
-/
@[simp]
theorem basicOpen_eq_of_affine' {R : CommRingCat} (f : Γ(Spec R, ⊤)) :
    (Spec R).basicOpen f = PrimeSpectrum.basicOpen ((Scheme.ΓSpecIso R).hom f) := by
  convert! basicOpen_eq_of_affine ((Scheme.ΓSpecIso R).hom f)
  exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso R) f).symm

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h4v.s13.f5e56433147a from=seed src=0 shape=c5f4a149 vocab=1abd68bc
-/
theorem Scheme.SpecMap_presheaf_map_eqToHom {X : Scheme} {U V : X.Opens} (h : U = V) (W) :
    (Spec.map (X.presheaf.map (eqToHom h).op)).app W = eqToHom (by cases h; simp) := by
  have : Scheme.Spec.map (X.presheaf.map (𝟙 (op U))).op = 𝟙 _ := by
    rw [X.presheaf.map_id, op_id, Scheme.Spec.map_id]
  cases h
  refine (Scheme.Hom.congr_app this _).trans ?_
  simp [eqToHom_map]

/--
@isnad1 id=eq.2h6v.s12.746474424312 from=seed src=0 shape=f85e2f5c vocab=a966a81e
-/
lemma germ_eq_zero_of_pow_mul_eq_zero {X : Scheme.{u}} {U : Opens X} (x : U) {f s : Γ(X, U)}
    (hx : x.val ∈ X.basicOpen s) {n : ℕ} (hf : s ^ n * f = 0) : X.presheaf.germ U x x.2 f = 0 := by
  rw [Scheme.mem_basicOpen X s x x.2] at hx
  have hu : IsUnit (X.presheaf.germ _ x x.2 (s ^ n)) := by
    rw [map_pow]
    exact IsUnit.pow n hx
  rw [← hu.mul_right_eq_zero, ← map_mul, hf, map_zero]

/--
@isnad1 id=eq.0h3v.s7.c86dcbb7d6b1 from=seed src=0 shape=5cc66a97 vocab=44ab00e1
-/
@[reassoc (attr := simp)]
lemma Scheme.hom_base_inv_base {X Y : Scheme.{u}} (e : X ≅ Y) :
    e.hom.base ≫ e.inv.base = 𝟙 _ :=
  LocallyRingedSpace.iso_hom_base_inv_base (Scheme.forgetToLocallyRingedSpace.mapIso e)

/--
@isnad1 id=eq.0h4v.s8.1d2d55d5648c from=seed src=0 shape=31f36a13 vocab=be8adf93
-/
@[simp]
lemma Scheme.hom_inv_apply {X Y : Scheme.{u}} (e : X ≅ Y) (x : X) :
    e.inv (e.hom x) = x := by
  change (e.hom ≫ e.inv) x = 𝟙 X.toPresheafedSpace x
  simp

/--
@isnad1 id=eq.0h3v.s7.6c72b7467192 from=seed src=0 shape=5ad0deb6 vocab=44ab00e1
-/
@[reassoc (attr := simp)]
lemma Scheme.inv_base_hom_base {X Y : Scheme.{u}} (e : X ≅ Y) :
    e.inv.base ≫ e.hom.base = 𝟙 _ :=
  LocallyRingedSpace.iso_inv_base_hom_base (Scheme.forgetToLocallyRingedSpace.mapIso e)

/--
@isnad1 id=eq.0h4v.s8.fd2081ff7f33 from=seed src=0 shape=b191e805 vocab=be8adf93
-/
@[simp]
lemma Scheme.inv_hom_apply {X Y : Scheme.{u}} (e : X ≅ Y) (y : Y) :
    e.hom (e.inv y) = y := by
  change (e.inv ≫ e.hom) y = 𝟙 Y.toPresheafedSpace y
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h2v.s10.2d554d9349d5 from=seed src=0 shape=65f9a3b9 vocab=e9c914c0
-/
theorem Spec_zeroLocus_eq_zeroLocus {R : CommRingCat} (s : Set R) :
    (Spec R).zeroLocus ((Scheme.ΓSpecIso R).inv '' s) = PrimeSpectrum.zeroLocus s := by
  ext x
  suffices (∀ a ∈ s, x ∉ PrimeSpectrum.basicOpen a) ↔ x ∈ PrimeSpectrum.zeroLocus s by simpa
  simp [Spec_carrier, PrimeSpectrum.mem_zeroLocus, Set.subset_def,
    PrimeSpectrum.mem_basicOpen _ x]

/--
@isnad1 id=eq.0h2v.s10.bc9a037f8663 from=seed src=0 shape=36c948fe vocab=1528047a
-/
theorem Spec_zeroLocus {R : CommRingCat} (s : Set Γ(Spec R, ⊤)) :
    (Spec R).zeroLocus s = PrimeSpectrum.zeroLocus ((Scheme.ΓSpecIso R).inv ⁻¹' s) := by
  convert! Spec_zeroLocus_eq_zeroLocus ((Scheme.ΓSpecIso R).inv ⁻¹' s)
  rw [Set.image_preimage_eq]
  exact (ConcreteCategory.bijective_of_isIso (C := CommRingCat) _).2
section Stalks

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance (x) : IsLocalHom (f.stalkMap x).hom :=
  f.prop x

/--
@isnad1 id=eq.0h2v.s8.cbb623feff48 from=seed src=0 shape=098a9011 vocab=e5b9a6f9
-/
@[simp]
lemma stalkMap_id (X : Scheme.{u}) (x : X) :
    (𝟙 X : X ⟶ X).stalkMap x = 𝟙 (X.presheaf.stalk x) :=
  PresheafedSpace.stalkMap.id _ x

/--
@isnad1 id=eq.0h6v.s10.5d9fb18dd022 from=seed src=0 shape=ef57efae vocab=e6f347cc
-/
lemma stalkMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap (f x) ≫ f.stalkMap x :=
  PresheafedSpace.stalkMap.comp f.toPshHom g.toPshHom x

/--
@isnad1 id=eq.1h5v.s10.70f5ca2f676b from=seed src=0 shape=3d7cc274 vocab=4108cdcd
-/
@[reassoc]
lemma stalkSpecializes_stalkMap (x x' : X)
    (h : x ⤳ x') : Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h) ≫ f.stalkMap x =
      f.stalkMap x' ≫ X.presheaf.stalkSpecializes h :=
  PresheafedSpace.stalkMap.stalkSpecializes_stalkMap f.toPshHom h

/--
@isnad1 id=eq.1h6v.s12.fdae0936c6eb from=seed src=0 shape=a4799396 vocab=25e17c44
-/
lemma stalkSpecializes_stalkMap_apply (x x' : X) (h : x ⤳ x') (y) :
    f.stalkMap x (Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h) y) =
      (X.presheaf.stalkSpecializes h (f.stalkMap x' y)) :=
  DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkSpecializes_stalkMap f x x' h)) y

/--
@isnad1 id=eq.2h6v.s10.872fa197c9d1 from=seed src=0 shape=accf2b81 vocab=97f784fe
-/
@[reassoc]
lemma stalkMap_congr (f g : X ⟶ Y) (hfg : f = g) (x x' : X)
    (hxx' : x = x') : f.stalkMap x ≫ (X.presheaf.stalkCongr (.of_eq hxx')).hom =
      (Y.presheaf.stalkCongr (.of_eq <| hfg ▸ hxx' ▸ rfl)).hom ≫ g.stalkMap x' :=
  LocallyRingedSpace.stalkMap_congr f.toLRSHom g.toLRSHom congr(($hfg).toLRSHom) x x' hxx'

/--
@isnad1 id=eq.1h5v.s10.3f63c05ff958 from=seed src=0 shape=09317d6e vocab=97f784fe
-/
@[reassoc]
lemma stalkMap_congr_hom (f g : X ⟶ Y) (hfg : f = g) (x : X) :
    f.stalkMap x = (Y.presheaf.stalkCongr (.of_eq <| hfg ▸ rfl)).hom ≫ g.stalkMap x :=
  LocallyRingedSpace.stalkMap_congr_hom f.toLRSHom g.toLRSHom congr(($hfg).toLRSHom) x

/--
@isnad1 id=eq.1h5v.s10.f7540ce0808e from=seed src=0 shape=14be488b vocab=97f784fe
-/
@[reassoc]
lemma stalkMap_congr_point (x x' : X) (hxx' : x = x') :
    f.stalkMap x ≫ (X.presheaf.stalkCongr (.of_eq hxx')).hom =
      (Y.presheaf.stalkCongr (.of_eq <| hxx' ▸ rfl)).hom ≫ f.stalkMap x' :=
  LocallyRingedSpace.stalkMap_congr_point f.toLRSHom x x' hxx'

/--
@isnad1 id=eq.0h4v.s10.7c72158e5e95 from=seed src=0 shape=b057cf4d vocab=3d0ebe39
-/
@[reassoc (attr := simp)]
lemma stalkMap_hom_inv (e : X ≅ Y) (y : Y) :
    e.hom.stalkMap (e.inv y) ≫ e.inv.stalkMap y =
      (Y.presheaf.stalkCongr (.of_eq (by simp))).hom :=
  LocallyRingedSpace.stalkMap_hom_inv (forgetToLocallyRingedSpace.mapIso e) y

/--
@isnad1 id=eq.0h5v.s12.8df3369ada82 from=seed src=0 shape=aee63a18 vocab=55c259fe
-/
@[simp]
lemma stalkMap_hom_inv_apply (e : X ≅ Y) (y : Y) (z) :
    e.inv.stalkMap y (e.hom.stalkMap (e.inv y) z) =
      (Y.presheaf.stalkCongr (.of_eq (by simp))).hom z :=
  DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkMap_hom_inv e y)) z

/--
@isnad1 id=eq.0h4v.s10.3fa3ee5069a2 from=seed src=0 shape=758b078c vocab=1ad4740e
-/
@[reassoc (attr := simp)]
lemma stalkMap_inv_hom (e : X ≅ Y) (x : X) :
    e.inv.stalkMap (e.hom x) ≫ e.hom.stalkMap x =
      (X.presheaf.stalkCongr (.of_eq (by simp))).hom :=
  LocallyRingedSpace.stalkMap_inv_hom (forgetToLocallyRingedSpace.mapIso e) x

/--
@isnad1 id=eq.0h5v.s12.1cf9ff0363bd from=seed src=0 shape=60facfc4 vocab=f45d33cb
-/
@[simp]
lemma stalkMap_inv_hom_apply (e : X ≅ Y) (x : X) (y) :
    e.hom.stalkMap x (e.inv.stalkMap (e.hom x) y) =
      (X.presheaf.stalkCongr (.of_eq (by simp))).hom y :=
  DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkMap_inv_hom e x)) y

/--
@isnad1 id=eq.1h5v.s10.968b3236e27b from=seed src=0 shape=9e3c2bd2 vocab=2c7deaed
-/
@[reassoc (attr := simp)]
lemma germ_stalkMap (U : Y.Opens) (x : X) (hx : f x ∈ U) :
    Y.presheaf.germ U (f x) hx ≫ f.stalkMap x =
      f.app U ≫ X.presheaf.germ (f ⁻¹ᵁ U) x hx :=
  PresheafedSpace.stalkMap_germ f.toPshHom U x hx

/--
@isnad1 id=eq.1h6v.s12.79d0f946c9b4 from=seed src=0 shape=0bec7375 vocab=9542c694
-/
@[simp]
lemma germ_stalkMap_apply (U : Y.Opens) (x : X) (hx : f x ∈ U) (y) :
    f.stalkMap x (Y.presheaf.germ _ (f x) hx y) =
      X.presheaf.germ (f ⁻¹ᵁ U) x hx (f.app U y) :=
  PresheafedSpace.stalkMap_germ_apply f.toPshHom U x hx y

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `x = y`, the stalk maps are isomorphic. -/
noncomputable def arrowStalkMapIsoOfEq {x y : X}
    (h : x = y) : Arrow.mk (f.stalkMap x) ≅ Arrow.mk (f.stalkMap y) :=
  Arrow.isoMk (Y.presheaf.stalkCongr <| (Inseparable.of_eq h).map f.continuous)
      (X.presheaf.stalkCongr <| Inseparable.of_eq h) <| by
    simp only [Arrow.mk_left, Arrow.mk_right, TopCat.Presheaf.stalkCongr_hom,
      Arrow.mk_hom]
    rw [stalkSpecializes_stalkMap]

end Hom

end Scheme

end Stalks

section IsLocalRing

open IsLocalRing

/--
@isnad1 id=eq.0h3v.s8.4d92627deb5d from=seed src=0 shape=e88066e8 vocab=023bf5de
-/
@[simp]
lemma Spec_closedPoint {R S : CommRingCat} [IsLocalRing R] [IsLocalRing S]
    {f : R ⟶ S} [IsLocalHom f.hom] : Spec.map f (closedPoint S) = closedPoint R :=
  IsLocalRing.comap_closedPoint f.hom

end IsLocalRing

end AlgebraicGeometry
