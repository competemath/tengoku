/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/
module

public import Tengoku

/-!
# LeanPool.WhiteheadTheorem.Exponential

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.Exponential`.
-/

@[expose] public section

open CategoryTheory
open scoped Topology

variable {X Y Y' Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Z]

/-- `uncurry_curry`
@isnad1 id=eq.0h4v.s5.f858a9d3d598 from=translated src=- shape=d8c5299c vocab=6911cd1d
-/
lemma ContinuousMap.uncurry_curry [LocallyCompactSpace Y]
  (f : C(X × Y, Z)) : f = f.curry.uncurry := rfl

/-- `curry_uncurry`
@isnad1 id=eq.0h4v.s6.1ce5ffb7816c from=translated src=- shape=ca97e9b9 vocab=665cae10
-/
lemma ContinuousMap.curry_uncurry [LocallyCompactSpace Y]
  (f : C(X, C(Y, Z))) : f = f.uncurry.curry := rfl

/-- An auxiliary lemma only used for showing the naturality of `topBinProdRightAdjExp`
@isnad1 id=eq.0h6v.s6.412f21224cf3 from=translated src=- shape=299362ce vocab=1e04cede
-/
lemma TopCat.exp_homEquiv_naturality_right [LocallyCompactSpace X]
    (f : C(Y', Y)) (g : C(Y, C(X, Z))) :
  (g.comp f).uncurry = g.uncurry.comp (f.prodMap (ContinuousMap.id X)) := rfl

namespace TopCat

/-- The functor `TopCat.of (· × X)` (taking the topological binary product, with `X` on the right)
from `TopCat` to `TopCat` -/
abbrev topBinProdRight (X : TopCat.{u}) : TopCat ⥤ TopCat where
  obj Y := TopCat.of (Y × X)
  map {Y Z} f := TopCat.ofHom (f.hom.prodMap (ContinuousMap.id X))

/-- The exponentiation functor `C(X, ·)` from `TopCat` to `TopCat` -/
abbrev exp (X : TopCat.{u}) : TopCat ⥤ TopCat where
  obj Y := TopCat.of C(X, Y)
  map {Y Z} f := TopCat.ofHom ⟨fun g ↦ f.hom.comp g, f.hom.continuous_postcomp⟩

/-- `topBinProdRightAdjExp` -/
noncomputable def topBinProdRightAdjExp (X : TopCat.{u}) [LocallyCompactSpace X] :
    topBinProdRight X ⊣ exp X :=
  Adjunction.mkOfHomEquiv
  { homEquiv Y Z :=
    { toFun f := TopCat.ofHom f.hom.curry
      invFun f := TopCat.ofHom f.hom.uncurry
      left_inv _ := by simp only [hom_ofHom, ← ContinuousMap.uncurry_curry _, ofHom_hom]
      right_inv _ := by simp only [hom_ofHom, ← ContinuousMap.curry_uncurry _, ofHom_hom] }
    homEquiv_naturality_left_symm {Y' Y Z} f g := by
      simp only [Equiv.coe_fn_symm_mk, hom_comp, TopCat.exp_homEquiv_naturality_right, ofHom_comp]
    homEquiv_naturality_right {Y Z Z'} f g := by
      simp only [Equiv.coe_fn_mk, hom_comp]; rfl }

/-- Same as `topBinProdRight`, except that `X` is not an object in `TopCat`,
but simply a topological space -/
abbrev topBinProdRight' (X : Type u) [TopologicalSpace X] : TopCat ⥤ TopCat where
  obj Y := TopCat.of (Y × X)
  map {Y Z} f := ofHom (f.hom.prodMap (ContinuousMap.id X))

/-- `topBinProdLeft'` -/
abbrev topBinProdLeft' (X : Type u) [TopologicalSpace X] : TopCat ⥤ TopCat where
  obj Y := TopCat.of (X × Y)
  map {Y Z} f := ofHom ((ContinuousMap.id X).prodMap f.hom)

/-- Same as `exp`, except that `X` is not an object in `TopCat`, but simply a topological space -/
abbrev exp' (X : Type u) [TopologicalSpace X] : TopCat ⥤ TopCat where
  obj Y := TopCat.of C(X, Y)
  map {Y Z} f := TopCat.ofHom ⟨fun g ↦ f.hom.comp g, f.hom.continuous_postcomp⟩

/-- Same as `topBinProdRightAdjExp`,
except that `X` is not an object in `TopCat`, but simply a topological space -/
noncomputable def topBinProdRightAdjExp'
    (X : Type u) [TopologicalSpace X] [LocallyCompactSpace X] :
    topBinProdRight' X ⊣ exp' X :=
  Adjunction.mkOfHomEquiv
  { homEquiv Y Z :=
    { toFun f := TopCat.ofHom f.hom.curry
      invFun f := TopCat.ofHom f.hom.uncurry
      left_inv _ := by simp only [hom_ofHom, ← ContinuousMap.uncurry_curry _, ofHom_hom]
      right_inv _ := by simp only [hom_ofHom, ← ContinuousMap.curry_uncurry _, ofHom_hom] }
    homEquiv_naturality_left_symm {Y' Y Z} f g := by
      simp only [Equiv.coe_fn_symm_mk, hom_comp, TopCat.exp_homEquiv_naturality_right, ofHom_comp]
    homEquiv_naturality_right {Y Z Z'} f g := by
      simp only [Equiv.coe_fn_mk, hom_comp]; rfl }

/-- `topBinProdLeftAdjExp'` -/
noncomputable def topBinProdLeftAdjExp'
    (X : Type u) [TopologicalSpace X] [LocallyCompactSpace X] :
    topBinProdLeft' X ⊣ exp' X :=
  Adjunction.mkOfHomEquiv
  { homEquiv Y Z :=
      let i : TopCat.of (X × Y) ≅ TopCat.of (Y × X) := isoOfHomeo (Homeomorph.prodComm X Y)
      { toFun f := TopCat.ofHom (i.inv ≫ f).hom.curry
        invFun f := i.hom ≫ TopCat.ofHom f.hom.uncurry
        left_inv _ := by
          simp only [hom_comp, hom_ofHom, ← ContinuousMap.uncurry_curry _, ofHom_comp, ofHom_hom,
            Iso.hom_inv_id_assoc]
        right_inv _ := by
          simp only [Iso.inv_hom_id_assoc, hom_ofHom, ← ContinuousMap.curry_uncurry _, ofHom_hom] }
    homEquiv_naturality_left_symm {Y' Y Z} f g := by
      simp only [isoOfHomeo_inv, Homeomorph.prodComm_symm, hom_comp, hom_ofHom, isoOfHomeo_hom,
        Equiv.coe_fn_symm_mk, exp_homEquiv_naturality_right, ofHom_comp]
      rfl
    homEquiv_naturality_right {Y Z Z'} f g := by
      simp only [isoOfHomeo_inv, Homeomorph.prodComm_symm, hom_comp, hom_ofHom, isoOfHomeo_hom,
        Equiv.coe_fn_mk, ContinuousMap.comp_assoc]
      rfl }

end TopCat

namespace ContinuousMap

variable {A B Y : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Y]

/-- `argSwap` -/
@[simp]
def argSwap : C(C(A × B, Y), C(B × A, Y)) where
  toFun f := f.comp ContinuousMap.prodSwap
  continuous_toFun := by fun_prop

/-- `curriedArgSwap` -/
def curriedArgSwap [LocallyCompactSpace A] [LocallyCompactSpace B] :
    C(C(A, C(B, Y)), C(B, C(A, Y))) where
  toFun f := ContinuousMap.curry <| argSwap <| ContinuousMap.uncurry f
  continuous_toFun := by
    refine Continuous.comp continuous_curry ?_
    exact Continuous.comp argSwap.continuous continuous_uncurry

/--
@isnad1 id=eq.0h3v.s8.37436be543d2 from=translated src=- shape=f439ac29 vocab=2b4a4a09
-/
lemma curriedArgSwap_curriedArgSwap [LocallyCompactSpace A] [LocallyCompactSpace B] :
  curriedArgSwap ∘ (curriedArgSwap (A := A) (B := B) (Y := Y)) = id := rfl

/-- `curryLeft` -/
def curryLeft (f : C(A × B, Y)) (b : B) : C(A, Y) where
  toFun a := f ⟨a, b⟩
  continuous_toFun := f.continuous.curry_left

/-- `curryRight` -/
def curryRight (f : C(A × B, Y)) (a : A) : C(B, Y) where
  toFun b := f ⟨a, b⟩
  continuous_toFun := f.continuous.curry_right

lemma eq_of_curry_eq {f g : C(A × B, Y)}
    (e : f.curry = g.curry) : f = g := by
  ext ⟨a, b⟩
  replace e := congrFun (congrArg ContinuousMap.toFun e) a
  replace e := congrFun (congrArg ContinuousMap.toFun e) b
  exact e

lemma eq_of_argSwap_curry_eq {f g : C(A × B, Y)}
    (e : f.argSwap.curry = g.argSwap.curry) : f = g := by
  ext ⟨a, b⟩
  replace e := congrFun (congrArg ContinuousMap.toFun e) b
  replace e := congrFun (congrArg ContinuousMap.toFun e) a
  exact e

end ContinuousMap

---------------------------------------------------------------

open scoped unitInterval

namespace TopCat

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]

/--
@isnad1 id=eq.1h5v.s7.736b1d9573f7 from=translated src=- shape=b8d8c0f9 vocab=44dbb3a4
-/
lemma hom_eq_of_curry_eq {Y : TopCat} {f g : TopCat.of (A × B) ⟶ Y}
    (e : f.hom.curry = g.hom.curry) : f = g :=
  TopCat.hom_ext_iff.mpr <| ContinuousMap.eq_of_curry_eq e

/--
@isnad1 id=eq.1h5v.s8.0332780075c6 from=translated src=- shape=bff0640a vocab=e02ff9a1
-/
lemma hom_eq_of_argSwap_curry_eq {Y : TopCat} {f g : TopCat.of (A × B) ⟶ Y}
    (e : f.hom.argSwap.curry = g.hom.argSwap.curry) : f = g :=
  TopCat.hom_ext_iff.mpr <| ContinuousMap.eq_of_argSwap_curry_eq e

end TopCat
