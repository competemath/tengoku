import Tengoku.Seed.CategoryTheory.Linear.LinearFunctor
import Tengoku.Seed.CategoryTheory.Conj
import Tengoku.Seed.Algebra.Algebra.Equiv
import Tengoku.Seed.Algebra.Category.ModuleCat.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Endomorphism algebras under linear functors

For an `R`-linear functor `F : C ⥤ D` between `R`-linear categories, `F.map` is an `R`-algebra
homomorphism `End X →ₐ[R] End (F.obj X)` (`CategoryTheory.Functor.mapEndAlgHom`), and
conjugation by an isomorphism `e : X ≅ Y` is an `R`-algebra isomorphism
`End X ≃ₐ[R] End Y` (`CategoryTheory.Iso.conjAlgEquiv`).

For a module category, `ModuleCat.Hom.hom` is an `R`-algebra isomorphism
`End M ≃ₐ[R] Module.End R M` (`ModuleCat.endAlgEquiv`). Hence an `R`-linear functor
`F : C ⥤ ModuleCat R` gives representations of the endomorphism algebras of `C`
(`CategoryTheory.Functor.mapModuleEnd`) and linear maps of hom modules
(`CategoryTheory.Functor.mapModuleHom`), computed by `(F.map f).hom`.

Recall that in `End X` the product is `f * g = g ≫ f`.
-/

universe w v v₁ v₂ u₁ u₂

namespace CategoryTheory

variable (R : Type w) [CommSemiring R]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [CategoryTheory.Linear R C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [CategoryTheory.Linear R D]

/-- `F.map` as an `R`-algebra homomorphism of endomorphism algebras.-/
def Functor.mapEndAlgHom (F : C ⥤ D) [F.Additive] [F.Linear R] (X : C) :
    End X →ₐ[R] End (F.obj X) :=
  AlgHom.ofLinearMap (F.mapLinearMap R) (F.map_id X) fun f g => F.map_comp g f

/--
@isnad1 id=eq.0h6v.s8.4ee2b3da9137 from=translated src=- shape=304bf5a2 vocab=4b53973e
-/
@[simp] theorem Functor.mapEndAlgHom_apply (F : C ⥤ D) [F.Additive] [F.Linear R] {X : C}
    (f : End X) : F.mapEndAlgHom R X f = F.map f := rfl

/-- Conjugation `f ↦ e.inv ≫ f ≫ e.hom` by an isomorphism, as an `R`-algebra isomorphism of
endomorphism algebras.-/
def Iso.conjAlgEquiv {X Y : C} (e : X ≅ Y) : End X ≃ₐ[R] End Y :=
  AlgEquiv.ofLinearEquiv
    { e.conj with
      map_add' := fun f g => by
        change e.inv ≫ ((f : X ⟶ X) + g) ≫ e.hom =
          ((e.inv ≫ f ≫ e.hom : Y ⟶ Y) + e.inv ≫ g ≫ e.hom)
        rw [Preadditive.add_comp, Preadditive.comp_add]
      map_smul' := fun r f => by
        change e.inv ≫ (r • (f : X ⟶ X)) ≫ e.hom = (r • (e.inv ≫ f ≫ e.hom : Y ⟶ Y))
        rw [Linear.smul_comp, Linear.comp_smul] }
    (e.conj.map_one) (fun f g => e.conj.map_mul f g)

/--
@isnad1 id=eq.0h6v.s7.51622891f4e2 from=translated src=- shape=84500c6a vocab=22b6c693
-/
@[simp] theorem Iso.conjAlgEquiv_apply {X Y : C} (e : X ≅ Y) (f : End X) :
    Iso.conjAlgEquiv R e f = e.inv ≫ f ≫ e.hom := rfl

/--
@isnad1 id=eq.0h6v.s7.154b1816cdfb from=translated src=- shape=d42ae5a2 vocab=e8ca3cde
-/
@[simp] theorem Iso.conjAlgEquiv_symm_apply {X Y : C} (e : X ≅ Y) (f : End Y) :
    (Iso.conjAlgEquiv R e).symm f = e.hom ≫ f ≫ e.inv := rfl

end CategoryTheory

namespace ModuleCat

variable {R : Type w} [CommRing R]

/-- `ModuleCat.Hom.hom` as an `R`-algebra isomorphism `End M ≃ₐ[R] Module.End R M`.-/
def endAlgEquiv (M : ModuleCat.{v} R) : CategoryTheory.End M ≃ₐ[R] Module.End R M :=
  AlgEquiv.ofRingEquiv (f := endRingEquiv M) fun _ => rfl

/--
@isnad1 id=eq.0h3v.s9.db8e44aaf9d4 from=translated src=- shape=0ace88bd vocab=9ec12a76
-/
@[simp] theorem endAlgEquiv_apply (M : ModuleCat.{v} R) (f : CategoryTheory.End M) :
    endAlgEquiv M f = f.hom := rfl

/--
@isnad1 id=eq.0h3v.s9.ad145a4922d6 from=translated src=- shape=507aee79 vocab=5376c6a4
-/
@[simp] theorem endAlgEquiv_symm_apply (M : ModuleCat.{v} R) (f : Module.End R M) :
    (endAlgEquiv M).symm f = ofHom f := rfl

end ModuleCat

namespace CategoryTheory

variable (R : Type w) [CommRing R]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [CategoryTheory.Linear R C]

/-- An `R`-linear functor to modules, on morphisms: an `R`-linear map
`(X ⟶ Y) →ₗ[R] (F.obj X →ₗ[R] F.obj Y)`, `f ↦ (F.map f).hom`.-/
def Functor.mapModuleHom (F : C ⥤ ModuleCat.{v} R) [F.Additive] [F.Linear R] (X Y : C) :
    (X ⟶ Y) →ₗ[R] (F.obj X →ₗ[R] F.obj Y) :=
  ModuleCat.homLinearEquiv.toLinearMap ∘ₗ F.mapLinearMap R

/--
@isnad1 id=eq.0h6v.s10.4c88052c050f from=translated src=- shape=732913c8 vocab=51887dbc
-/
@[simp] theorem Functor.mapModuleHom_apply (F : C ⥤ ModuleCat.{v} R) [F.Additive] [F.Linear R]
    {X Y : C} (f : X ⟶ Y) : F.mapModuleHom R X Y f = (F.map f).hom := rfl

/-- An `R`-linear functor to modules, on endomorphisms: the representation
`End X →ₐ[R] Module.End R (F.obj X)`, `f ↦ (F.map f).hom`.-/
def Functor.mapModuleEnd (F : C ⥤ ModuleCat.{v} R) [F.Additive] [F.Linear R] (X : C) :
    End X →ₐ[R] Module.End R (F.obj X) :=
  (ModuleCat.endAlgEquiv (F.obj X)).toAlgHom.comp (F.mapEndAlgHom R X)

/--
@isnad1 id=eq.0h5v.s9.f2af9a356b80 from=translated src=- shape=be7977a6 vocab=add47b31
-/
@[simp] theorem Functor.mapModuleEnd_apply (F : C ⥤ ModuleCat.{v} R) [F.Additive] [F.Linear R]
    {X : C} (f : End X) : F.mapModuleEnd R X f = (F.map f).hom := rfl

/--
@isnad1 id=eq.0h6v.s10.d914bd68fef2 from=translated src=- shape=75a3c33b vocab=98395618
-/
theorem Functor.mapModuleEnd_apply_apply (F : C ⥤ ModuleCat.{v} R) [F.Additive] [F.Linear R]
    {X : C} (f : End X) (x : F.obj X) : F.mapModuleEnd R X f x = (F.map f).hom x := rfl

/-- The representation `End X →ₐ[R] Module.End R M` of an `R`-linear functor to modules,
transported along an isomorphism `e : F.obj X ≅ M`: `f ↦ e.inv ≫ F.map f ≫ e.hom`. Typical
use: `e = eqToIso h` when the image of `X` is only propositionally equal to a fixed module.-/
def Functor.mapModuleEndOfIso (F : C ⥤ ModuleCat.{v} R) [F.Additive] [F.Linear R] {X : C}
    {M : ModuleCat.{v} R} (e : F.obj X ≅ M) : End X →ₐ[R] Module.End R M :=
  ((ModuleCat.endAlgEquiv M).toAlgHom.comp (Iso.conjAlgEquiv R e).toAlgHom).comp
    (F.mapEndAlgHom R X)

/--
@isnad1 id=eq.0h7v.s9.1a5e1db45094 from=translated src=- shape=27b03b5a vocab=23e73e33
-/
@[simp] theorem Functor.mapModuleEndOfIso_apply (F : C ⥤ ModuleCat.{v} R) [F.Additive]
    [F.Linear R] {X : C} {M : ModuleCat.{v} R} (e : F.obj X ≅ M) (f : End X) :
    F.mapModuleEndOfIso R e f = (e.inv ≫ F.map f ≫ e.hom).hom := rfl

end CategoryTheory
