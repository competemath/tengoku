/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.Algebra.Category.ModuleCat.Subobject
import Tengoku.Seed.CategoryTheory.Subobject.NoetherianObject
import Tengoku.Seed.RingTheory.Noetherian.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Noetherian objects in `ModuleCat`

The categorical subobjects of an `R`-module are order-isomorphic to its submodules. Consequently
an algebraically Noetherian module is a Noetherian object of `ModuleCat R`.
-/

universe v u

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [Ring R]

/-- An algebraically Noetherian module is a Noetherian object of `ModuleCat R`.-/
instance isNoetherianObject_of_isNoetherian (M : ModuleCat.{v} R) [IsNoetherian R M] :
    IsNoetherianObject M := by
  apply ObjectProperty.is_of_prop isNoetherianObject
  exact RelHomClass.isWellFounded (subobjectModule M).toOrderEmbedding.dual.ltEmbedding

end ModuleCat
