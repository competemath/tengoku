import Tengoku.HodgeStructuresLean4.HodgePilot.Comodule
import Tengoku.Seed.Algebra.Category.ModuleCat.Basic
import Tengoku.Seed.CategoryTheory.Preadditive.Biproducts
import Tengoku.Seed.CategoryTheory.ObjectProperty.FullSubcategory
import Tengoku.Seed.CategoryTheory.Linear.Basic
import Tengoku.Seed.CategoryTheory.Linear.LinearFunctor
import Tengoku.Seed.RingTheory.Finiteness.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The bundled category of comodules over a coalgebra

Stage 2 of the reconstruction campaign (`reconstruction_design_memo.md` §6):
the bundled category `HodgePilot.ComodCat R A` of right `A`-comodules over an
`R`-coalgebra `A`, built on the Stage-1 comodule library
(`HodgePilot/Comodule.lean`). The pinned Mathlib has no comodule API at all,
hence no such category; this file supplies it in the house style of
`Mathlib.Algebra.Category.CoalgCat.Basic` (objects bundle a `ModuleCat R`
carrier with a `Comodule` instance; morphisms are a type alias around
`ComodHom`).

## Main definitions

* `HodgePilot.ComodCat R A` — the category of right `A`-comodules; a
  `ConcreteCategory` with a faithful `forget₂` to `ModuleCat R`
  (which moreover reflects isomorphisms).
* `HodgePilot.ComodCat.regular` — the regular comodule (`A` over itself,
  coaction `comul`) as an object.
* `HodgePilot.ComodCat.base` — over a bialgebra `A`, the base ring `R` with
  coaction `r ↦ r ⊗ 1` (the "trivial representation") as an object.
* `HodgePilot.ComodCat.corestrict` — corestriction along a coalgebra morphism
  `f : A →ₗc[R] B`, as a functor `ComodCat R A ⥤ ComodCat R B` commuting with
  the forgetful functors to `ModuleCat R` on the nose.
* `HodgePilot.ComodCat.isIso_of_bijective` — a morphism of comodules whose
  underlying map is bijective is an isomorphism of comodules (the linear
  inverse of a comodule map is a comodule map, `HodgePilot.ComodHom.inverse`).
* `HodgePilot.FComodCat R A` — the full subcategory of comodules whose
  underlying module is finitely generated (over a field: finite-dimensional),
  in the `ObjectProperty` style of `FGModuleCat`.
* Additive structure (the Stage-2 stretch scoped by the design memo):
  `ComodHom` carries an `AddCommGroup`/`Module R` structure,
  `ComodCat R A` is `Preadditive` and `R`-`Linear` with additive linear
  `forget₂`, has a zero object (`PUnit` with zero coaction) and binary
  biproducts (`HodgePilot.Comodule.prod` on `M × N`) — an additive category.
  The abelian structure (kernels/cokernels) is deliberately left to a later
  stage, per the memo.

## Conventions

Right comodules, Waterhouse/Milne convention, as in Stage 1. The base ring of
the bundled category is a `CommRing` (the carrier of a `ModuleCat R` is an
`AddCommGroup`); the unbundled comodule constructions stay `CommSemiring`-
general. Everything Stage 3 uses is over the field `ℚ`.
-/

open CategoryTheory

open scoped TensorProduct

universe v w w' u

namespace HodgePilot

/-! ## The inverse of a bijective comodule morphism (unbundled) -/

section Inverse

variable {R : Type u} {A : Type v} {M N : Type*} [CommSemiring R]
  [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [ComoduleStruct R A M] [ComoduleStruct R A N]

/-- A linear two-sided inverse of a comodule morphism is itself a comodule
morphism.-/
def ComodHom.inverse (φ : ComodHom R A M N) (g : N →ₗ[R] M)
    (hgf : g ∘ₗ φ.toLinearMap = LinearMap.id)
    (hfg : φ.toLinearMap ∘ₗ g = LinearMap.id) : ComodHom R A N M where
  toLinearMap := g
  coaction_comm := by
    refine LinearMap.ext fun n => ?_
    simp only [LinearMap.comp_apply]
    have hn : φ.toLinearMap (g n) = n := by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
        LinearMap.congr_fun hfg n
    have h2 : LinearMap.rTensor A φ.toLinearMap
        (ComoduleStruct.coaction (R := R) (A := A) (g n)) =
          ComoduleStruct.coaction (R := R) (A := A) (M := N) n := by
      have h := LinearMap.congr_fun φ.coaction_comm (g n)
      simp only [LinearMap.comp_apply] at h
      rw [h, hn]
    calc LinearMap.rTensor A g
          (ComoduleStruct.coaction (R := R) (A := A) (M := N) n)
        = LinearMap.rTensor A g (LinearMap.rTensor A φ.toLinearMap
            (ComoduleStruct.coaction (R := R) (A := A) (g n))) := by rw [h2]
      _ = LinearMap.rTensor A (g ∘ₗ φ.toLinearMap)
            (ComoduleStruct.coaction (R := R) (A := A) (g n)) := by
          rw [LinearMap.rTensor_comp, LinearMap.comp_apply]
      _ = ComoduleStruct.coaction (R := R) (A := A) (g n) := by
          rw [hgf, LinearMap.rTensor_id, LinearMap.id_apply]

/--
@isnad1 id=eq.2h6v.s8.7c03a8d97047 from=translated src=- shape=2e9183f9 vocab=98be72b8
-/
@[simp]
theorem ComodHom.coe_inverse (φ : ComodHom R A M N) (g : N →ₗ[R] M)
    (hgf) (hfg) : ⇑(φ.inverse g hgf hfg) = ⇑g := rfl

end Inverse

/-! ## The bundled category -/

section Bundled

variable (R : Type u) [CommRing R] (A : Type w) [AddCommGroup A] [Module R A]
  [Coalgebra R A]

/-- The category of right `A`-comodules over an `R`-coalgebra `A`: objects
bundle a `ModuleCat R` carrier with a `Comodule R A` instance, morphisms are
`ComodHom`s. Mirrors `CoalgCat`.-/
structure ComodCat extends ModuleCat.{v} R where
  instComodule : Comodule R A carrier

attribute [instance] ComodCat.instComodule

variable {R A}

namespace ComodCat

instance instCoeSort : CoeSort (ComodCat.{v} R A) (Type v) :=
  ⟨(·.carrier)⟩

/--
@isnad1 id=eq.0h3v.s6.57e83a1a590f from=translated src=- shape=cc077655 vocab=33cea330
-/
@[simp] theorem moduleCat_of_toModuleCat (X : ComodCat.{v} R A) :
    ModuleCat.of R X.toModuleCat = X.toModuleCat :=
  rfl

variable (R A) in
/-- The object in the category of right `A`-comodules associated to a
comodule.-/
abbrev of (X : Type v) [AddCommGroup X] [Module R X] [Comodule R A X] :
    ComodCat.{v} R A :=
  { ModuleCat.of R X with
    instComodule := (inferInstance : Comodule R A X) }

/--
@isnad1 id=eq.0h3v.s8.13633da9d0eb from=translated src=- shape=92ca73cf vocab=03068e79
-/
@[simp]
lemma of_coaction {X : Type v} [AddCommGroup X] [Module R X] [Comodule R A X] :
    Comodule.coaction (R := R) (A := A) (M := of R A X) =
      Comodule.coaction (R := R) (A := A) (M := X) := rfl

/-- A type alias for `ComodHom` to avoid confusion between the categorical and
algebraic spellings of composition.-/
@[ext]
structure Hom (M N : ComodCat.{v} R A) where
  /-- The underlying `ComodHom`.-/
  toComodHom' : ComodHom R A M N

instance category : Category (ComodCat.{v} R A) where
  Hom M N := Hom M N
  id M := ⟨ComodHom.id R A M⟩
  comp f g := ⟨g.toComodHom'.comp f.toComodHom'⟩
  id_comp _ := Hom.ext (ComodHom.comp_id _)
  comp_id _ := Hom.ext (ComodHom.id_comp _)
  assoc _ _ _ := Hom.ext (ComodHom.comp_assoc _ _ _).symm

instance concreteCategory :
    ConcreteCategory (ComodCat.{v} R A) (fun M N => ComodHom R A M N) where
  hom f := f.toComodHom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `ComodCat` back into a `ComodHom`.-/
abbrev Hom.toComodHom {M N : ComodCat.{v} R A} (f : Hom M N) :
    ComodHom R A M N :=
  ConcreteCategory.hom (C := ComodCat.{v} R A) f

/-- Typecheck a `ComodHom` as a morphism in `ComodCat R A`.-/
abbrev ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] [Comodule R A X] [Comodule R A Y] (f : ComodHom R A X Y) :
    of R A X ⟶ of R A Y :=
  ConcreteCategory.ofHom f

/--
@isnad1 id=injectiv.0h4v.s8.3a2003ca2f75 from=translated src=- shape=5df23f46 vocab=ed629836
-/
lemma Hom.toComodHom_injective (M N : ComodCat.{v} R A) :
    Function.Injective (Hom.toComodHom' : Hom M N → _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

/--
@isnad1 id=eq.1h6v.s8.3948f3db4015 from=translated src=- shape=c7dcac78 vocab=6910c4d9
-/
@[ext]
lemma hom_ext {M N : ComodCat.{v} R A} (f g : M ⟶ N)
    (h : f.toComodHom = g.toComodHom) : f = g :=
  Hom.ext h

/--
@isnad1 id=eq.0h7v.s9.e6e873225553 from=translated src=- shape=269e8b8d vocab=8cf85736
-/
@[simp] theorem toComodHom_comp {M N P : ComodCat.{v} R A}
    (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).toComodHom = g.toComodHom.comp f.toComodHom :=
  rfl

/--
@isnad1 id=eq.0h3v.s8.25c5d5a02b24 from=translated src=- shape=a0483fc7 vocab=2970782a
-/
@[simp] theorem toComodHom_id {M : ComodCat.{v} R A} :
    Hom.toComodHom (𝟙 M) = ComodHom.id R A M :=
  rfl

instance hasForgetToModule :
    HasForget₂ (ComodCat.{v} R A) (ModuleCat.{v} R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.toComodHom.toLinearMap }

/--
@isnad1 id=eq.0h3v.s9.d4723f2bd05d from=translated src=- shape=1c73667d vocab=c6bc2a1f
-/
@[simp]
theorem forget₂_obj (X : ComodCat.{v} R A) :
    (forget₂ (ComodCat.{v} R A) (ModuleCat.{v} R)).obj X = ModuleCat.of R X :=
  rfl

/--
@isnad1 id=eq.0h5v.s11.e1e880150a2c from=translated src=- shape=db242981 vocab=8b4c3a8d
-/
@[simp]
theorem forget₂_map (X Y : ComodCat.{v} R A) (f : X ⟶ Y) :
    (forget₂ (ComodCat.{v} R A) (ModuleCat.{v} R)).map f =
      ModuleCat.ofHom f.toComodHom.toLinearMap :=
  rfl

/-- The forgetful functor to `R`-modules is faithful (kernel-audited witness;
the instance itself is found by instance search).
@isnad1 id=faithful.0h2v.s9.286c5c2bc090 from=translated src=- shape=cd7b77e2 vocab=6f336852
-/
theorem forget₂_faithful :
    (forget₂ (ComodCat.{v} R A) (ModuleCat.{v} R)).Faithful :=
  inferInstance

/-! ### The regular comodule as an object -/

variable (R A) in
/-- The **regular comodule** — the coalgebra `A` coacting on itself by the
comultiplication — as an object of `ComodCat R A`.-/
def regular : ComodCat.{w} R A := of R A A

/--
@isnad1 id=eq.0h2v.s5.5b202bbd2b33 from=translated src=- shape=32dd05cd vocab=7b90d133
-/
@[simp] theorem regular_carrier : (regular R A : Type w) = A := rfl

/-! ### Isomorphisms are detected on underlying modules -/

/--
@isnad1 id=isiso.1h5v.s9.339f96321647 from=translated src=- shape=089fd28d vocab=8583b651
-/
theorem isIso_of_bijective {M N : ComodCat.{v} R A} (f : M ⟶ N)
    (hf : Function.Bijective f.toComodHom) : IsIso f := by
  let e := LinearEquiv.ofBijective f.toComodHom.toLinearMap hf
  refine ⟨⟨f.toComodHom.inverse e.symm.toLinearMap
    (LinearMap.ext fun m => e.symm_apply_apply m)
    (LinearMap.ext fun n => e.apply_symm_apply n)⟩, ?_, ?_⟩
  · exact hom_ext _ _ (ComodHom.ext fun m => e.symm_apply_apply m)
  · exact hom_ext _ _ (ComodHom.ext fun n => e.apply_symm_apply n)

/-! ### Corestriction as a functor -/

section Corestrict

variable {B : Type w'} [AddCommGroup B] [Module R B] [Coalgebra R B]

/-- Corestriction along a coalgebra morphism `f : A →ₗc[R] B`, as a functor
`ComodCat R A ⥤ ComodCat R B`. On objects it is `Comodule.corestrict`
(post-composition of the coaction with `1 ⊗ f`), on morphisms it is the
identity on underlying linear maps (`ComodHom.corestrict`).-/
def corestrict (f : A →ₗc[R] B) : ComodCat.{v} R A ⥤ ComodCat.{v} R B where
  obj M :=
    { toModuleCat := M.toModuleCat
      instComodule := Comodule.corestrict M f }
  map φ := ⟨φ.toComodHom.corestrict f⟩
  map_id _ := hom_ext _ _ (ComodHom.ext fun _ => rfl)
  map_comp _ _ := hom_ext _ _ (ComodHom.ext fun _ => rfl)

/--
@isnad1 id=eq.0h5v.s7.d2fa980105cf from=translated src=- shape=828027ed vocab=1a73a1b2
-/
@[simp]
theorem corestrict_obj_carrier (f : A →ₗc[R] B) (M : ComodCat.{v} R A) :
    (((corestrict f).obj M : ComodCat.{v} R B) : Type v) = (M : Type v) := rfl

/--
@isnad1 id=eq.0h7v.s10.65c4f2ee5ff2 from=translated src=- shape=094a9b98 vocab=2ccf856d
-/
@[simp]
theorem corestrict_map_toLinearMap (f : A →ₗc[R] B) {M N : ComodCat.{v} R A}
    (φ : M ⟶ N) :
    ((corestrict f).map φ).toComodHom.toLinearMap =
      φ.toComodHom.toLinearMap := rfl

/-- Corestriction commutes with the forgetful functors to `ModuleCat R` on
the nose.
@isnad1 id=eq.0h4v.s10.d2b5730a3377 from=translated src=- shape=a23254a2 vocab=6f864597
-/
theorem corestrict_comp_forget₂ (f : A →ₗc[R] B) :
    corestrict.{v} f ⋙ forget₂ (ComodCat.{v} R B) (ModuleCat.{v} R) =
      forget₂ (ComodCat.{v} R A) (ModuleCat.{v} R) := rfl

end Corestrict

/-! ### The finite (finite-dimensional) full subcategory -/

variable (R A) in
/-- Finiteness of the underlying module, as a property of objects of
`ComodCat R A`; over a field this is finite-dimensionality. Mirrors
`ModuleCat.isFG`.-/
def isFinite : ObjectProperty (ComodCat.{v} R A) :=
  fun M => Module.Finite R M

/--
@isnad1 id=iff.0h3v.s6.73d1a990a221 from=translated src=- shape=8f658b55 vocab=9adaac81
-/
lemma isFinite_iff (M : ComodCat.{v} R A) :
    isFinite R A M ↔ Module.Finite R M := Iff.rfl

end ComodCat

variable (R A) in
/-- The category of right `A`-comodules whose underlying `R`-module is
finitely generated (for `R` a field: finite-dimensional comodules, the
objects of Tannaka reconstruction). A full subcategory of `ComodCat R A` in
the `ObjectProperty` style of `FGModuleCat`.-/
abbrev FComodCat := (ComodCat.isFinite.{v} R A).FullSubcategory

namespace FComodCat

/-- A synonym for `M.obj.carrier`, which we can mark with `@[coe]`.-/
@[reducible]
def carrier (M : FComodCat.{v} R A) : Type v := M.obj.carrier

instance instCoeSort : CoeSort (FComodCat.{v} R A) (Type v) :=
  ⟨carrier⟩

attribute [coe] FComodCat.carrier

/--
@isnad1 id=eq.0h3v.s6.eb984dee3502 from=translated src=- shape=6a136a9e vocab=326235cd
-/
@[simp] lemma obj_carrier (M : FComodCat.{v} R A) :
    M.obj.carrier = M.carrier := rfl

variable (R A) in
/-- Lift an unbundled finite comodule to `FComodCat R A`.-/
abbrev of (X : Type v) [AddCommGroup X] [Module R X] [Comodule R A X]
    [Module.Finite R X] : FComodCat.{v} R A :=
  ⟨ComodCat.of R A X, inferInstanceAs (Module.Finite R X)⟩

/--
@isnad1 id=eq.1h6v.s10.ef201f12a4d2 from=translated src=- shape=4f70f7cf vocab=db6d4b80
-/
@[ext]
lemma hom_ext {M N : FComodCat.{v} R A} {f g : M ⟶ N}
    (h : f.hom.toComodHom = g.hom.toComodHom) : f = g :=
  ObjectProperty.hom_ext _ (ComodCat.hom_ext _ _ h)

section Corestrict

variable {B : Type w'} [AddCommGroup B] [Module R B] [Coalgebra R B]

/-- Corestriction restricted to the finite full subcategories (the underlying
module is unchanged, so finiteness is preserved).-/
def corestrict (f : A →ₗc[R] B) : FComodCat.{v} R A ⥤ FComodCat.{v} R B :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ ComodCat.corestrict f) (fun M => M.property)

end Corestrict

end FComodCat

end Bundled

/-! ## Additive and `R`-linear structure on comodule morphisms (unbundled)

Comodule morphisms into a comodule with an `AddCommGroup` carrier form an
`AddCommGroup`, and an `R`-module; `LinearMap.rTensor` is additive and
`R`-linear in the map, so all the coaction-compatibility squares are
inherited summand-wise. (`CoalgHom`s have no such structure — coalgebra
morphisms are not closed under addition; comodule morphisms are.) -/

section ComodHomAdditive

namespace ComodHom

variable {R : Type u} {A : Type v} {M N : Type*} [CommSemiring R]
  [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]
  [AddCommMonoid M] [Module R M] [AddCommGroup N] [Module R N]
  [ComoduleStruct R A M] [ComoduleStruct R A N]

instance instZero : Zero (ComodHom R A M N) :=
  ⟨{ toLinearMap := 0
     coaction_comm := by
       rw [LinearMap.rTensor_zero, LinearMap.zero_comp, LinearMap.comp_zero] }⟩

/--
@isnad1 id=eq.0h4v.s7.c918269707fa from=translated src=- shape=574a70be vocab=c4efcf7b
-/
@[simp] theorem coe_zero : ⇑(0 : ComodHom R A M N) = 0 := rfl

/--
@isnad1 id=eq.0h5v.s7.a1fcfceefa63 from=translated src=- shape=1e39e405 vocab=c4efcf7b
-/
@[simp] theorem zero_apply (m : M) : (0 : ComodHom R A M N) m = 0 := rfl

/--
@isnad1 id=eq.0h4v.s7.45ac83c56885 from=translated src=- shape=600af85b vocab=9d3caf28
-/
@[simp] theorem toLinearMap_zero :
    (0 : ComodHom R A M N).toLinearMap = 0 := rfl

instance instAdd : Add (ComodHom R A M N) :=
  ⟨fun f g =>
    { toLinearMap := f.toLinearMap + g.toLinearMap
      coaction_comm := by
        rw [LinearMap.rTensor_add, LinearMap.add_comp, LinearMap.comp_add,
          f.coaction_comm, g.coaction_comm] }⟩

/--
@isnad1 id=eq.0h6v.s8.8187fb05654a from=translated src=- shape=04cb1281 vocab=7a76ea2b
-/
@[simp] theorem coe_add (f g : ComodHom R A M N) : ⇑(f + g) = ⇑f + ⇑g := rfl

/--
@isnad1 id=eq.0h7v.s8.32aee504500a from=translated src=- shape=1b5e976e vocab=7a76ea2b
-/
@[simp] theorem add_apply (f g : ComodHom R A M N) (m : M) :
    (f + g) m = f m + g m := rfl

/--
@isnad1 id=eq.0h6v.s8.7e6c9eaa6617 from=translated src=- shape=e95f5bfc vocab=7d4ea4da
-/
@[simp] theorem toLinearMap_add (f g : ComodHom R A M N) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap := rfl

instance instNeg : Neg (ComodHom R A M N) :=
  ⟨fun f =>
    { toLinearMap := -f.toLinearMap
      coaction_comm := by
        rw [LinearMap.rTensor_neg, LinearMap.neg_comp, LinearMap.comp_neg,
          f.coaction_comm] }⟩

/--
@isnad1 id=eq.0h5v.s7.f9c8ebaea14f from=translated src=- shape=05993dc7 vocab=f5ecc983
-/
@[simp] theorem coe_neg (f : ComodHom R A M N) : ⇑(-f) = -⇑f := rfl

/--
@isnad1 id=eq.0h6v.s7.960031761f5d from=translated src=- shape=04a9e1eb vocab=f5ecc983
-/
@[simp] theorem neg_apply (f : ComodHom R A M N) (m : M) : (-f) m = -f m := rfl

/--
@isnad1 id=eq.0h5v.s7.14af3d5f3845 from=translated src=- shape=06dda6a2 vocab=2d5b1f42
-/
@[simp] theorem toLinearMap_neg (f : ComodHom R A M N) :
    (-f).toLinearMap = -f.toLinearMap := rfl

instance instSub : Sub (ComodHom R A M N) :=
  ⟨fun f g =>
    { toLinearMap := f.toLinearMap - g.toLinearMap
      coaction_comm := by
        rw [LinearMap.rTensor_sub, LinearMap.sub_comp, LinearMap.comp_sub,
          f.coaction_comm, g.coaction_comm] }⟩

/--
@isnad1 id=eq.0h6v.s8.08902c7e5e55 from=translated src=- shape=04cb1281 vocab=7f292327
-/
@[simp] theorem coe_sub (f g : ComodHom R A M N) : ⇑(f - g) = ⇑f - ⇑g := rfl

/--
@isnad1 id=eq.0h7v.s8.254e96de846a from=translated src=- shape=1b5e976e vocab=7f292327
-/
@[simp] theorem sub_apply (f g : ComodHom R A M N) (m : M) :
    (f - g) m = f m - g m := rfl

/--
@isnad1 id=eq.0h6v.s8.0f631919a6dc from=translated src=- shape=e95f5bfc vocab=43613080
-/
@[simp] theorem toLinearMap_sub (f g : ComodHom R A M N) :
    (f - g).toLinearMap = f.toLinearMap - g.toLinearMap := rfl

instance instSMul : SMul R (ComodHom R A M N) :=
  ⟨fun c f =>
    { toLinearMap := c • f.toLinearMap
      coaction_comm := by
        rw [LinearMap.rTensor_smul, LinearMap.smul_comp, LinearMap.comp_smul,
          f.coaction_comm] }⟩

/--
@isnad1 id=eq.0h6v.s8.cfcbc2536e25 from=translated src=- shape=0fefa81c vocab=b66d3eca
-/
@[simp] theorem coe_smul (c : R) (f : ComodHom R A M N) : ⇑(c • f) = c • ⇑f :=
  rfl

/--
@isnad1 id=eq.0h7v.s8.d07ef84c6c7c from=translated src=- shape=d9092733 vocab=b66d3eca
-/
@[simp] theorem smul_apply (c : R) (f : ComodHom R A M N) (m : M) :
    (c • f) m = c • f m := rfl

/--
@isnad1 id=eq.0h6v.s8.8b859f1db9d3 from=translated src=- shape=a5e86f99 vocab=614b4ce9
-/
@[simp] theorem toLinearMap_smul (c : R) (f : ComodHom R A M N) :
    (c • f).toLinearMap = c • f.toLinearMap := rfl

instance addCommGroup : AddCommGroup (ComodHom R A M N) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  sub := Sub.sub
  add_assoc _ _ _ := ext fun _ => add_assoc _ _ _
  add_comm _ _ := ext fun _ => add_comm _ _
  zero_add _ := ext fun _ => zero_add _
  add_zero _ := ext fun _ => add_zero _
  neg_add_cancel _ := ext fun _ => neg_add_cancel _
  sub_eq_add_neg _ _ := ext fun _ => sub_eq_add_neg _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance module : Module R (ComodHom R A M N) where
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _
  smul_zero _ := ext fun _ => smul_zero _
  smul_add _ _ _ := ext fun _ => smul_add _ _ _
  add_smul _ _ _ := ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul _ _

end ComodHom

end ComodHomAdditive

/-! ## Preadditive and linear structure on the bundled category -/

section BundledAdditive

variable {R : Type u} [CommRing R] {A : Type w} [AddCommGroup A] [Module R A]
  [Coalgebra R A]

namespace ComodCat

variable {M N : ComodCat.{v} R A}

instance instHomZero : Zero (M ⟶ N) := ⟨⟨0⟩⟩

/--
@isnad1 id=eq.0h4v.s10.55719d795e6d from=translated src=- shape=4096a6d2 vocab=6910c4d9
-/
@[simp] lemma toComodHom_zero : (0 : M ⟶ N).toComodHom = 0 := rfl

instance instHomAdd : Add (M ⟶ N) := ⟨fun f g => ⟨f.toComodHom + g.toComodHom⟩⟩

/--
@isnad1 id=eq.0h6v.s10.171b5eb4d075 from=translated src=- shape=f32fc9be vocab=6b284f84
-/
@[simp] lemma toComodHom_add (f g : M ⟶ N) :
    (f + g).toComodHom = f.toComodHom + g.toComodHom := rfl

instance instHomNeg : Neg (M ⟶ N) := ⟨fun f => ⟨-f.toComodHom⟩⟩

/--
@isnad1 id=eq.0h5v.s9.147466e97c42 from=translated src=- shape=d32e18ca vocab=26cdd6dd
-/
@[simp] lemma toComodHom_neg (f : M ⟶ N) :
    (-f).toComodHom = -f.toComodHom := rfl

instance instHomSub : Sub (M ⟶ N) := ⟨fun f g => ⟨f.toComodHom - g.toComodHom⟩⟩

/--
@isnad1 id=eq.0h6v.s10.b03f93bdb8ae from=translated src=- shape=f32fc9be vocab=898993f6
-/
@[simp] lemma toComodHom_sub (f g : M ⟶ N) :
    (f - g).toComodHom = f.toComodHom - g.toComodHom := rfl

instance instHomNSMul : SMul ℕ (M ⟶ N) := ⟨fun n f => ⟨n • f.toComodHom⟩⟩

/--
@isnad1 id=eq.0h6v.s11.0b6e5414f53c from=translated src=- shape=3399a1b5 vocab=d1927f64
-/
@[simp] lemma toComodHom_nsmul (n : ℕ) (f : M ⟶ N) :
    (n • f).toComodHom = n • f.toComodHom := rfl

instance instHomZSMul : SMul ℤ (M ⟶ N) := ⟨fun n f => ⟨n • f.toComodHom⟩⟩

/--
@isnad1 id=eq.0h6v.s11.357c133f33a1 from=translated src=- shape=3399a1b5 vocab=ed8c1164
-/
@[simp] lemma toComodHom_zsmul (n : ℤ) (f : M ⟶ N) :
    (n • f).toComodHom = n • f.toComodHom := rfl

instance instHomSMul : SMul R (M ⟶ N) := ⟨fun c f => ⟨c • f.toComodHom⟩⟩

/--
@isnad1 id=eq.0h6v.s10.d4417793086b from=translated src=- shape=20a14536 vocab=b4887951
-/
@[simp] lemma toComodHom_rsmul (c : R) (f : M ⟶ N) :
    (c • f).toComodHom = c • f.toComodHom := rfl

instance homAddCommGroup : AddCommGroup (M ⟶ N) :=
  Function.Injective.addCommGroup (Hom.toComodHom)
    (fun _ _ h => hom_ext _ _ h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl)

instance homModule : Module R (M ⟶ N) :=
  Function.Injective.module R
    { toFun := Hom.toComodHom, map_zero' := rfl, map_add' := fun _ _ => rfl }
    (fun _ _ h => hom_ext _ _ h)
    (fun _ _ => rfl)

instance preadditive : Preadditive (ComodCat.{v} R A) where
  add_comp _ _ _ f f' g :=
    hom_ext _ _ (ComodHom.ext fun m => _root_.map_add g.toComodHom _ _)
  comp_add _ _ _ _ _ _ :=
    hom_ext _ _ (ComodHom.ext fun _ => rfl)

instance linear : CategoryTheory.Linear R (ComodCat.{v} R A) where
  smul_comp _ _ _ c f g :=
    hom_ext _ _ (ComodHom.ext fun m => _root_.map_smul g.toComodHom c _)
  comp_smul _ _ _ _ _ _ :=
    hom_ext _ _ (ComodHom.ext fun _ => rfl)

end ComodCat

end BundledAdditive

/-! ## Products of comodules (binary direct sums, unbundled)

The product `M × N` of two right `A`-comodules is a comodule: the coaction is
the sum of the two component coactions pushed in along `inl` and `inr`. The
four structural maps `inl`, `inr`, `fst`, `snd` are comodule morphisms, and
they exhibit `M × N` as a binary biproduct in the bundled category below. -/

section ProdComodule

variable {R : Type u} {A : Type v} {M N : Type*} [CommSemiring R]
  [AddCommMonoid A] [Module R A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

section Struct

variable [CoalgebraStruct R A] [ComoduleStruct R A M] [ComoduleStruct R A N]

/-- The product comodule structure on `M × N`: the coaction is the sum of the
two component coactions pushed in along `inl` and `inr`.-/
instance ComoduleStruct.prod : ComoduleStruct R A (M × N) where
  coaction :=
    LinearMap.rTensor A (LinearMap.inl R M N) ∘ₗ
        ComoduleStruct.coaction (R := R) (A := A) (M := M) ∘ₗ
          LinearMap.fst R M N +
      LinearMap.rTensor A (LinearMap.inr R M N) ∘ₗ
        ComoduleStruct.coaction (R := R) (A := A) (M := N) ∘ₗ
          LinearMap.snd R M N

/--
@isnad1 id=eq.0h4v.s10.97902f2cc728 from=translated src=- shape=4d3efcd3 vocab=dedd31ee
-/
@[simp] theorem ComoduleStruct.prod_coaction :
    ComoduleStruct.coaction (R := R) (A := A) (M := M × N) =
      LinearMap.rTensor A (LinearMap.inl R M N) ∘ₗ
          ComoduleStruct.coaction (R := R) (A := A) (M := M) ∘ₗ
            LinearMap.fst R M N +
        LinearMap.rTensor A (LinearMap.inr R M N) ∘ₗ
          ComoduleStruct.coaction (R := R) (A := A) (M := N) ∘ₗ
            LinearMap.snd R M N := rfl

variable (R A M N) in
/-- The inclusion `M → M × N` as a comodule morphism.-/
def ComodHom.inl : ComodHom R A M (M × N) where
  toLinearMap := LinearMap.inl R M N
  coaction_comm := by
    ext m
    simp [ComoduleStruct.prod_coaction]

variable (R A M N) in
/-- The inclusion `N → M × N` as a comodule morphism.-/
def ComodHom.inr : ComodHom R A N (M × N) where
  toLinearMap := LinearMap.inr R M N
  coaction_comm := by
    ext n
    simp [ComoduleStruct.prod_coaction]

variable (R A M N) in
/-- The projection `M × N → M` as a comodule morphism.-/
def ComodHom.fst : ComodHom R A (M × N) M where
  toLinearMap := LinearMap.fst R M N
  coaction_comm := by
    ext p <;>
      simp [ComoduleStruct.prod_coaction, ← LinearMap.rTensor_comp_apply,
        LinearMap.rTensor_zero]

variable (R A M N) in
/-- The projection `M × N → N` as a comodule morphism.-/
def ComodHom.snd : ComodHom R A (M × N) N where
  toLinearMap := LinearMap.snd R M N
  coaction_comm := by
    ext p <;>
      simp [ComoduleStruct.prod_coaction, ← LinearMap.rTensor_comp_apply,
        LinearMap.rTensor_zero]

/--
@isnad1 id=eq.0h5v.s7.b851707bc595 from=translated src=- shape=ed4eb6fd vocab=2b443c67
-/
@[simp] theorem ComodHom.inl_apply (m : M) :
    ComodHom.inl R A M N m = ((m, 0) : M × N) := rfl

/--
@isnad1 id=eq.0h5v.s7.c3db14dc427e from=translated src=- shape=b128d55b vocab=3d57e7a3
-/
@[simp] theorem ComodHom.inr_apply (n : N) :
    ComodHom.inr R A M N n = ((0, n) : M × N) := rfl

/--
@isnad1 id=eq.0h5v.s7.096d4e0bbee6 from=translated src=- shape=d54fa1e5 vocab=451ef274
-/
@[simp] theorem ComodHom.fst_apply (p : M × N) :
    ComodHom.fst R A M N p = p.1 := rfl

/--
@isnad1 id=eq.0h5v.s7.b2f141797d71 from=translated src=- shape=3b4a5ca0 vocab=ca752275
-/
@[simp] theorem ComodHom.snd_apply (p : M × N) :
    ComodHom.snd R A M N p = p.2 := rfl

/--
@isnad1 id=eq.0h4v.s7.8a589f240b27 from=translated src=- shape=47b2e9fe vocab=893854b1
-/
@[simp] theorem ComodHom.inl_toLinearMap :
    (ComodHom.inl R A M N).toLinearMap = LinearMap.inl R M N := rfl

/--
@isnad1 id=eq.0h4v.s7.4efc839d868c from=translated src=- shape=51a59a21 vocab=b4104923
-/
@[simp] theorem ComodHom.inr_toLinearMap :
    (ComodHom.inr R A M N).toLinearMap = LinearMap.inr R M N := rfl

/--
@isnad1 id=eq.0h4v.s7.8457f156df8c from=translated src=- shape=6ce5438a vocab=c71406c9
-/
@[simp] theorem ComodHom.fst_toLinearMap :
    (ComodHom.fst R A M N).toLinearMap = LinearMap.fst R M N := rfl

/--
@isnad1 id=eq.0h4v.s7.4c7b7bb00127 from=translated src=- shape=7afd97a8 vocab=98180a0f
-/
@[simp] theorem ComodHom.snd_toLinearMap :
    (ComodHom.snd R A M N).toLinearMap = LinearMap.snd R M N := rfl

end Struct

section Laws

variable [Coalgebra R A] [Comodule R A M] [Comodule R A N]

/-- Naturality of the right unitor against `rTensor` (pure-tensor check).-/
private theorem rid_naturality {P Q : Type*} [AddCommMonoid P] [Module R P]
    [AddCommMonoid Q] [Module R Q] (f : P →ₗ[R] Q) :
    (TensorProduct.rid R Q).toLinearMap ∘ₗ LinearMap.rTensor R f =
      f ∘ₗ (TensorProduct.rid R P).toLinearMap :=
  TensorProduct.ext' fun p r => by simp

omit [Coalgebra R A] in
/-- Naturality of the inverse associator in the first slot, in
`rTensor`/`rTensor` form (the `hnat2` pattern of `Comodule.lean`).-/
private theorem rTensor_rTensor_assoc_symm {P Q : Type*} [AddCommMonoid P]
    [Module R P] [AddCommMonoid Q] [Module R Q] (j : P →ₗ[R] Q) :
    LinearMap.rTensor A (LinearMap.rTensor A j) ∘ₗ
        (TensorProduct.assoc R P A A).symm.toLinearMap =
      (TensorProduct.assoc R Q A A).symm.toLinearMap ∘ₗ
        LinearMap.rTensor (A ⊗[R] A) j := by
  simpa only [← LinearMap.rTensor_def, TensorProduct.map_id,
    LinearMap.rTensor_id] using
    TensorProduct.map_map_comp_assoc_symm_eq j (LinearMap.id (M := A))
      (LinearMap.id (M := A))

/-- The composite `rTensor j ∘ ρ` of a coaction with a pushed-in linear map
is "coassociative relative to `M`" — the engine of the product coassociativity
proof, applied at `j = inl` and `j = inr`.-/
private theorem coassoc_component {P : Type*} [AddCommMonoid P] [Module R P]
    (j : M →ₗ[R] P) :
    LinearMap.rTensor A
        (LinearMap.rTensor A j ∘ₗ Comodule.coaction (R := R) (A := A) (M := M)) ∘ₗ
        Comodule.coaction (R := R) (A := A) (M := M) =
      (TensorProduct.assoc R P A A).symm.toLinearMap ∘ₗ
        LinearMap.lTensor P (Coalgebra.comul (R := R) (A := A)) ∘ₗ
          LinearMap.rTensor A j ∘ₗ Comodule.coaction (R := R) (A := A) (M := M) := by
  rw [LinearMap.rTensor_comp, LinearMap.comp_assoc, Comodule.coaction_coassoc,
    ← LinearMap.comp_assoc
      (LinearMap.lTensor M (Coalgebra.comul (R := R) (A := A)) ∘ₗ
        Comodule.coaction (R := R) (A := A) (M := M))
      (TensorProduct.assoc R M A A).symm.toLinearMap
      (LinearMap.rTensor A (LinearMap.rTensor A j)),
    rTensor_rTensor_assoc_symm, LinearMap.comp_assoc,
    ← LinearMap.comp_assoc (Comodule.coaction (R := R) (A := A) (M := M))
      (LinearMap.lTensor M (Coalgebra.comul (R := R) (A := A)))
      (LinearMap.rTensor (A ⊗[R] A) j),
    LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
    LinearMap.comp_assoc]

private theorem inl_fst_add_inr_snd :
    LinearMap.inl R M N ∘ₗ LinearMap.fst R M N +
      LinearMap.inr R M N ∘ₗ LinearMap.snd R M N = LinearMap.id :=
  LinearMap.ext fun _ => Prod.ext (by simp) (by simp)

/-- The product of two comodules is a comodule. This is the object part of
binary biproducts in `ComodCat R A`.-/
instance Comodule.prod : Comodule R A (M × N) where
  toComoduleStruct := ComoduleStruct.prod
  coaction_counit := by
    have hS1 : (TensorProduct.rid R (M × N)).toLinearMap ∘ₗ
        (LinearMap.lTensor (M × N) (Coalgebra.counit (R := R) (A := A)) ∘ₗ
          (LinearMap.rTensor A (LinearMap.inl R M N) ∘ₗ
            ComoduleStruct.coaction (R := R) (A := A) (M := M) ∘ₗ
              LinearMap.fst R M N)) =
        LinearMap.inl R M N ∘ₗ LinearMap.fst R M N := by
      rw [← LinearMap.comp_assoc
          (ComoduleStruct.coaction (R := R) (A := A) (M := M) ∘ₗ
            LinearMap.fst R M N)
          (LinearMap.rTensor A (LinearMap.inl R M N))
          (LinearMap.lTensor (M × N) (Coalgebra.counit (R := R) (A := A))),
        LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
        LinearMap.comp_assoc,
        ← LinearMap.comp_assoc
          (LinearMap.lTensor M (Coalgebra.counit (R := R) (A := A)) ∘ₗ
            (ComoduleStruct.coaction (R := R) (A := A) (M := M) ∘ₗ
              LinearMap.fst R M N))
          (LinearMap.rTensor R (LinearMap.inl R M N))
          (TensorProduct.rid R (M × N)).toLinearMap,
        rid_naturality, LinearMap.comp_assoc,
        ← LinearMap.comp_assoc (LinearMap.fst R M N)
          (ComoduleStruct.coaction (R := R) (A := A) (M := M))
          (LinearMap.lTensor M (Coalgebra.counit (R := R) (A := A))),
        ← LinearMap.comp_assoc (LinearMap.fst R M N)
          (LinearMap.lTensor M (Coalgebra.counit (R := R) (A := A)) ∘ₗ
            ComoduleStruct.coaction (R := R) (A := A) (M := M))
          (TensorProduct.rid R M).toLinearMap,
        Comodule.coaction_counit, LinearMap.id_comp]
    have hS2 : (TensorProduct.rid R (M × N)).toLinearMap ∘ₗ
        (LinearMap.lTensor (M × N) (Coalgebra.counit (R := R) (A := A)) ∘ₗ
          (LinearMap.rTensor A (LinearMap.inr R M N) ∘ₗ
            ComoduleStruct.coaction (R := R) (A := A) (M := N) ∘ₗ
              LinearMap.snd R M N)) =
        LinearMap.inr R M N ∘ₗ LinearMap.snd R M N := by
      rw [← LinearMap.comp_assoc
          (ComoduleStruct.coaction (R := R) (A := A) (M := N) ∘ₗ
            LinearMap.snd R M N)
          (LinearMap.rTensor A (LinearMap.inr R M N))
          (LinearMap.lTensor (M × N) (Coalgebra.counit (R := R) (A := A))),
        LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
        LinearMap.comp_assoc,
        ← LinearMap.comp_assoc
          (LinearMap.lTensor N (Coalgebra.counit (R := R) (A := A)) ∘ₗ
            (ComoduleStruct.coaction (R := R) (A := A) (M := N) ∘ₗ
              LinearMap.snd R M N))
          (LinearMap.rTensor R (LinearMap.inr R M N))
          (TensorProduct.rid R (M × N)).toLinearMap,
        rid_naturality, LinearMap.comp_assoc,
        ← LinearMap.comp_assoc (LinearMap.snd R M N)
          (ComoduleStruct.coaction (R := R) (A := A) (M := N))
          (LinearMap.lTensor N (Coalgebra.counit (R := R) (A := A))),
        ← LinearMap.comp_assoc (LinearMap.snd R M N)
          (LinearMap.lTensor N (Coalgebra.counit (R := R) (A := A)) ∘ₗ
            ComoduleStruct.coaction (R := R) (A := A) (M := N))
          (TensorProduct.rid R N).toLinearMap,
        Comodule.coaction_counit, LinearMap.id_comp]
    rw [ComoduleStruct.prod_coaction, LinearMap.comp_add, LinearMap.comp_add,
      hS1, hS2, inl_fst_add_inr_snd]
  coaction_coassoc := by
    have hT1inl : (LinearMap.rTensor A (LinearMap.inl R M N) ∘ₗ
        ComoduleStruct.coaction (R := R) (A := A) (M := M) ∘ₗ
          LinearMap.fst R M N) ∘ₗ LinearMap.inl R M N =
        LinearMap.rTensor A (LinearMap.inl R M N) ∘ₗ
          ComoduleStruct.coaction (R := R) (A := A) (M := M) := by
      rw [LinearMap.comp_assoc, LinearMap.comp_assoc, LinearMap.fst_comp_inl,
        LinearMap.comp_id]
    have hT2inl : (LinearMap.rTensor A (LinearMap.inr R M N) ∘ₗ
        ComoduleStruct.coaction (R := R) (A := A) (M := N) ∘ₗ
          LinearMap.snd R M N) ∘ₗ LinearMap.inl R M N = 0 := by
      rw [LinearMap.comp_assoc, LinearMap.comp_assoc, LinearMap.snd_comp_inl,
        LinearMap.comp_zero, LinearMap.comp_zero]
    have hT1inr : (LinearMap.rTensor A (LinearMap.inl R M N) ∘ₗ
        ComoduleStruct.coaction (R := R) (A := A) (M := M) ∘ₗ
          LinearMap.fst R M N) ∘ₗ LinearMap.inr R M N = 0 := by
      rw [LinearMap.comp_assoc, LinearMap.comp_assoc, LinearMap.fst_comp_inr,
        LinearMap.comp_zero, LinearMap.comp_zero]
    have hT2inr : (LinearMap.rTensor A (LinearMap.inr R M N) ∘ₗ
        ComoduleStruct.coaction (R := R) (A := A) (M := N) ∘ₗ
          LinearMap.snd R M N) ∘ₗ LinearMap.inr R M N =
        LinearMap.rTensor A (LinearMap.inr R M N) ∘ₗ
          ComoduleStruct.coaction (R := R) (A := A) (M := N) := by
      rw [LinearMap.comp_assoc, LinearMap.comp_assoc, LinearMap.snd_comp_inr,
        LinearMap.comp_id]
    have hD1 : LinearMap.rTensor A
        (LinearMap.rTensor A (LinearMap.inl R M N) ∘ₗ
          ComoduleStruct.coaction (R := R) (A := A) (M := M) ∘ₗ
            LinearMap.fst R M N) ∘ₗ
        (LinearMap.rTensor A (LinearMap.inl R M N) ∘ₗ
          ComoduleStruct.coaction (R := R) (A := A) (M := M) ∘ₗ
            LinearMap.fst R M N) =
        (TensorProduct.assoc R (M × N) A A).symm.toLinearMap ∘ₗ
          (LinearMap.lTensor (M × N) (Coalgebra.comul (R := R) (A := A)) ∘ₗ
            (LinearMap.rTensor A (LinearMap.inl R M N) ∘ₗ
              ComoduleStruct.coaction (R := R) (A := A) (M := M) ∘ₗ
                LinearMap.fst R M N)) := by
      rw [← LinearMap.comp_assoc
          (ComoduleStruct.coaction (R := R) (A := A) (M := M) ∘ₗ
            LinearMap.fst R M N)
          (LinearMap.rTensor A (LinearMap.inl R M N))
          (LinearMap.rTensor A
            (LinearMap.rTensor A (LinearMap.inl R M N) ∘ₗ
              ComoduleStruct.coaction (R := R) (A := A) (M := M) ∘ₗ
                LinearMap.fst R M N)),
        ← LinearMap.rTensor_comp, hT1inl,
        ← LinearMap.comp_assoc (LinearMap.fst R M N)
          (ComoduleStruct.coaction (R := R) (A := A) (M := M))
          (LinearMap.rTensor A
            (LinearMap.rTensor A (LinearMap.inl R M N) ∘ₗ
              ComoduleStruct.coaction (R := R) (A := A) (M := M))),
        coassoc_component, LinearMap.comp_assoc, LinearMap.comp_assoc,
        LinearMap.comp_assoc]
    have hD2 : LinearMap.rTensor A
        (LinearMap.rTensor A (LinearMap.inr R M N) ∘ₗ
          ComoduleStruct.coaction (R := R) (A := A) (M := N) ∘ₗ
            LinearMap.snd R M N) ∘ₗ
        (LinearMap.rTensor A (LinearMap.inr R M N) ∘ₗ
          ComoduleStruct.coaction (R := R) (A := A) (M := N) ∘ₗ
            LinearMap.snd R M N) =
        (TensorProduct.assoc R (M × N) A A).symm.toLinearMap ∘ₗ
          (LinearMap.lTensor (M × N) (Coalgebra.comul (R := R) (A := A)) ∘ₗ
            (LinearMap.rTensor A (LinearMap.inr R M N) ∘ₗ
              ComoduleStruct.coaction (R := R) (A := A) (M := N) ∘ₗ
                LinearMap.snd R M N)) := by
      rw [← LinearMap.comp_assoc
          (ComoduleStruct.coaction (R := R) (A := A) (M := N) ∘ₗ
            LinearMap.snd R M N)
          (LinearMap.rTensor A (LinearMap.inr R M N))
          (LinearMap.rTensor A
            (LinearMap.rTensor A (LinearMap.inr R M N) ∘ₗ
              ComoduleStruct.coaction (R := R) (A := A) (M := N) ∘ₗ
                LinearMap.snd R M N)),
        ← LinearMap.rTensor_comp, hT2inr,
        ← LinearMap.comp_assoc (LinearMap.snd R M N)
          (ComoduleStruct.coaction (R := R) (A := A) (M := N))
          (LinearMap.rTensor A
            (LinearMap.rTensor A (LinearMap.inr R M N) ∘ₗ
              ComoduleStruct.coaction (R := R) (A := A) (M := N))),
        coassoc_component, LinearMap.comp_assoc, LinearMap.comp_assoc,
        LinearMap.comp_assoc]
    have hX12 : LinearMap.rTensor A
        (LinearMap.rTensor A (LinearMap.inl R M N) ∘ₗ
          ComoduleStruct.coaction (R := R) (A := A) (M := M) ∘ₗ
            LinearMap.fst R M N) ∘ₗ
        (LinearMap.rTensor A (LinearMap.inr R M N) ∘ₗ
          ComoduleStruct.coaction (R := R) (A := A) (M := N) ∘ₗ
            LinearMap.snd R M N) = 0 := by
      rw [← LinearMap.comp_assoc
          (ComoduleStruct.coaction (R := R) (A := A) (M := N) ∘ₗ
            LinearMap.snd R M N)
          (LinearMap.rTensor A (LinearMap.inr R M N))
          (LinearMap.rTensor A
            (LinearMap.rTensor A (LinearMap.inl R M N) ∘ₗ
              ComoduleStruct.coaction (R := R) (A := A) (M := M) ∘ₗ
                LinearMap.fst R M N)),
        ← LinearMap.rTensor_comp, hT1inr, LinearMap.rTensor_zero,
        LinearMap.zero_comp]
    have hX21 : LinearMap.rTensor A
        (LinearMap.rTensor A (LinearMap.inr R M N) ∘ₗ
          ComoduleStruct.coaction (R := R) (A := A) (M := N) ∘ₗ
            LinearMap.snd R M N) ∘ₗ
        (LinearMap.rTensor A (LinearMap.inl R M N) ∘ₗ
          ComoduleStruct.coaction (R := R) (A := A) (M := M) ∘ₗ
            LinearMap.fst R M N) = 0 := by
      rw [← LinearMap.comp_assoc
          (ComoduleStruct.coaction (R := R) (A := A) (M := M) ∘ₗ
            LinearMap.fst R M N)
          (LinearMap.rTensor A (LinearMap.inl R M N))
          (LinearMap.rTensor A
            (LinearMap.rTensor A (LinearMap.inr R M N) ∘ₗ
              ComoduleStruct.coaction (R := R) (A := A) (M := N) ∘ₗ
                LinearMap.snd R M N)),
        ← LinearMap.rTensor_comp, hT2inl, LinearMap.rTensor_zero,
        LinearMap.zero_comp]
    rw [ComoduleStruct.prod_coaction, LinearMap.rTensor_add,
      LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add,
      LinearMap.comp_add, LinearMap.comp_add, hD1, hD2, hX12, hX21,
      add_zero, zero_add]

end Laws

end ProdComodule

/-! ## The zero comodule -/

section PUnitComodule

variable {R : Type u} {A : Type v} [CommSemiring R]
  [AddCommMonoid A] [Module R A] [Coalgebra R A]

/-- The zero module `PUnit` is a comodule with the zero coaction.-/
instance Comodule.instPUnit : Comodule R A PUnit where
  coaction := 0
  coaction_counit := LinearMap.ext fun _ => Subsingleton.elim _ _
  coaction_coassoc := by ext x; simp

end PUnitComodule

/-! ## Biproducts and the zero object in the bundled category -/

section BundledBiproducts

variable {R : Type u} [CommRing R] {A : Type w} [AddCommGroup A] [Module R A]
  [Coalgebra R A]

namespace ComodCat

/-- The binary bicone on `M N : ComodCat R A` built from the product comodule
and the four structural comodule morphisms.-/
def binaryBicone (M N : ComodCat.{v} R A) : Limits.BinaryBicone M N where
  pt := of R A (M × N)
  fst := ⟨ComodHom.fst R A M N⟩
  snd := ⟨ComodHom.snd R A M N⟩
  inl := ⟨ComodHom.inl R A M N⟩
  inr := ⟨ComodHom.inr R A M N⟩
  inl_fst := hom_ext _ _ (ComodHom.ext fun _ => rfl)
  inl_snd := hom_ext _ _ (ComodHom.ext fun _ => rfl)
  inr_fst := hom_ext _ _ (ComodHom.ext fun _ => rfl)
  inr_snd := hom_ext _ _ (ComodHom.ext fun _ => rfl)

/--
@isnad1 id=eq.0h4v.s10.075747b85d7e from=translated src=- shape=dc3632b2 vocab=9d2f1571
-/
theorem binaryBicone_total (M N : ComodCat.{v} R A) :
    (binaryBicone M N).fst ≫ (binaryBicone M N).inl +
        (binaryBicone M N).snd ≫ (binaryBicone M N).inr =
      𝟙 (binaryBicone M N).pt :=
  hom_ext _ _ (ComodHom.ext fun _ => Prod.ext (add_zero _) (zero_add _))

/--
@isnad1 id=iszero.0h3v.s6.ec861cd838d8 from=translated src=- shape=6733355b vocab=fcca5b8b
-/
theorem isZero_of_subsingleton (M : ComodCat.{v} R A) [Subsingleton M] :
    Limits.IsZero M where
  unique_to Y := ⟨⟨⟨(0 : M ⟶ Y)⟩, fun f => hom_ext f _ (ComodHom.ext fun m => by
    rw [Subsingleton.elim m 0]
    simp)⟩⟩
  unique_from Y := ⟨⟨⟨(0 : Y ⟶ M)⟩, fun f => hom_ext f _ (ComodHom.ext fun _ =>
    Subsingleton.elim _ _)⟩⟩

end ComodCat

end BundledBiproducts

/-! ## The base comodule as an object (bialgebra coefficients) -/

namespace ComodCat

section Base

variable (R : Type u) [CommRing R] (A : Type w) [Ring A] [Bialgebra R A]

/-- The **base comodule** — the base ring `R` with the coaction `r ↦ r ⊗ 1`
over a bialgebra `A` (the "trivial representation") — as an object of
`ComodCat R A`.-/
def base : ComodCat.{u} R A :=
  letI := Comodule.base R A
  of R A R

/--
@isnad1 id=eq.0h2v.s6.13712dc03a78 from=translated src=- shape=bf44951a vocab=87d8d784
-/
@[simp] theorem base_carrier : (base R A : Type u) = R := rfl

end Base

end ComodCat

end HodgePilot
