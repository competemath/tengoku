/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sheaves of modules on over categories

Elementary API for restricting a sheaf of modules on an arbitrary ringed site to an over
category. No geometric realization of the site is required.
-/

universe u

open CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) (U : C)

@[simp]
lemma overFunctor_obj (M : SheafOfModules.{u} R) :
    (overFunctor R U).obj M = M.over U := rfl

end SheafOfModules
