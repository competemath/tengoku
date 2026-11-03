/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyLinear
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexCohomologyHomotopyNaturality
import Tengoku.Seed.Algebra.Homology.DerivedCategory.ExactFunctor
import Tengoku.Seed.RingTheory.LocalProperties.ProjectiveDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Conditional localization of derived-category Hom-sets

Degreewise module localization induces a map on derived-category morphisms.
The canonical class-to-homotopy comparison followed by `Qh` identifies this
map with degree-zero Hom-complex class localization when both the source and
its localization are K-projective. Under the separate class-localization
hypothesis, this map is a localization of `R`-modules.
Both module categories use their standard derived-category structures.

No preservation of arbitrary K-projectivity, internal derived-Hom object, or
geometric pullback comparison is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra CochainComplex.HomComplex

namespace CochainComplex.HomComplex

universe u

noncomputable section

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- The standard derived category on source modules, used locally.-/
private abbrev sourceDerivedCategory : HasDerivedCategory (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _
/-- The standard derived category on localized modules, used locally.-/
private abbrev targetDerivedCategory : HasDerivedCategory (ModuleCat.{u} (Localization S)) :=
  HasDerivedCategory.standard _
attribute [local instance] sourceDerivedCategory targetDerivedCategory

private abbrev F := ModuleCat.localizedModuleFunctor.{u} S
private abbrev loc (X : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((F S).mapHomologicalComplex (.up ℤ)).obj X

/-- The canonical comparison between localizing a derived image and taking
the derived image of the degreewise localized complex. It is the component of
the existing `mapDerivedCategoryFactorsh` isomorphism.-/
def derivedLocalizationComparison (X : CochainComplex (ModuleCat.{u} R) ℤ) :
    (ModuleCat.localizedModuleFunctor.{u} S).mapDerivedCategory.obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≅
    DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj X)) :=
  ((F S).mapDerivedCategoryFactorsh).app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj X)

/-- `R`-linearity of localization, used only to build the linear Hom map;
it is deliberately not registered as an instance for importers.-/
private abbrev localizedFunctorLinear : Functor.Linear R (F S) where
  map_smul {M N} f r := by
    apply ModuleCat.hom_ext
    ext y
    dsimp [F, ModuleCat.localizedModuleFunctor, ModuleCat.localizedModuleMap]
    simp only [map_smul, LinearMap.smul_apply]
    change r •
      ((IsLocalizedModule.mapExtendScalars S
        (M.localizedModuleMkLinearMap S) (N.localizedModuleMkLinearMap S)
        (Localization S)) f.hom) y =
      (algebraMap R (Localization S) r) •
        ((IsLocalizedModule.mapExtendScalars S
        (M.localizedModuleMkLinearMap S) (N.localizedModuleMkLinearMap S)
        (Localization S)) f.hom) y
    exact (IsScalarTower.algebraMap_smul (Localization S) r _).symm

/-- Degreewise localization on derived-category morphisms, conjugated by the
canonical comparison isomorphisms. This linear map is defined without any
K-projectivity hypothesis; the class comparison below needs both sources
K-projective.-/
def derivedHomLocalizedMap (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) →ₗ[R]
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj P)) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj Q))) where
  toFun f := (derivedLocalizationComparison S P).inv ≫
    (F S).mapDerivedCategory.map f ≫ (derivedLocalizationComparison S Q).hom
  map_add' f g := by simp
  map_smul' r f := by
    letI : Functor.Linear R (F S) := localizedFunctorLinear S
    simp

variable (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
  [P.IsKProjective]
  [CochainComplex.IsKProjective
    (((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj P)]

end

noncomputable section BoundedProjective

variable {R : Type u} [CommRing R] (S : Submonoid R)
  (P Q : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The standard source derived category for the bounded corollary.-/
private abbrev boundedSourceDerivedCategory : HasDerivedCategory (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _
/-- The standard localized derived category for the bounded corollary.-/
private abbrev boundedTargetDerivedCategory : HasDerivedCategory (ModuleCat.{u} (Localization S)) :=
  HasDerivedCategory.standard _
attribute [local instance] boundedSourceDerivedCategory boundedTargetDerivedCategory

end BoundedProjective

end CochainComplex.HomComplex
