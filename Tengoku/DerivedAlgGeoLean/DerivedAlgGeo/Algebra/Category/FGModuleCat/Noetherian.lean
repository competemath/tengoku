/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Algebra.Category.ModuleCat.Noetherian
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Subobject.NoetherianObject
import Tengoku.Seed.Algebra.Category.FGModuleCat.Limits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Noetherian objects in `FGModuleCat`

Over a Noetherian ring, every finitely generated module is algebraically Noetherian. The
forgetful functor to `ModuleCat` preserves monomorphisms, reflects isomorphisms, and therefore
detects the categorical ascending-chain condition.
-/

universe u

open CategoryTheory

namespace FGModuleCat

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Every finitely generated module over a Noetherian ring is a Noetherian object.
@isnad1 id=isnoethe.0h2v.s5.e5478234af02 from=translated src=- shape=88a545a0 vocab=5997bf9d
-/
instance isNoetherianObject (M : FGModuleCat.{u} R) : IsNoetherianObject M := by
  letI : Module.Finite R M := M.property
  have hM : IsNoetherianObject (ModuleCat.of R M) := inferInstance
  letI : IsNoetherianObject
      ((forget₂ (FGModuleCat R) (ModuleCat R)).obj M) := hM
  exact CategoryTheory.isNoetherianObject_of_reflectsIsomorphisms
    (forget₂ (FGModuleCat R) (ModuleCat R))

end FGModuleCat
