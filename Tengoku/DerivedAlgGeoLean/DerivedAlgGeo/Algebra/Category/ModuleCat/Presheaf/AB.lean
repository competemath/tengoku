/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.Algebra.Category.ModuleCat.Presheaf.Abelian
import Tengoku.Seed.Algebra.Category.ModuleCat.Presheaf.Colimits
import Tengoku.Seed.Algebra.Category.ModuleCat.Presheaf.Limits
import Tengoku.Seed.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Tengoku.Seed.CategoryTheory.Functor.ReflectsIso.Balanced

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact colimits of presheaves of modules

Colimits of presheaves of modules of a shape `K` are exact when colimits of that shape are exact
in abelian groups.  The forgetful functor to presheaves of abelian groups preserves colimits and
finite limits, and it reflects finite limits: being faithful it reflects monomorphisms and
epimorphisms, so out of the balanced category of presheaves of modules it reflects isomorphisms,
and a finite-limit-preserving functor that reflects isomorphisms reflects finite limits.
Exactness therefore pulls back along it from the functor category, where colimits are exact
objectwise (`HasExactColimitsOfShape.domain_of_functor`).  In particular presheaves of modules
satisfy AB4 and AB5 in the universes where abelian groups do.

## Main results

* `PresheafOfModules.hasExactColimitsOfShape`: the per-shape instance.
* `PresheafOfModules.ab4OfSize`, `PresheafOfModules.ab5OfSize`: the Grothendieck axioms.
-/

open CategoryTheory Limits

universe w' w v' u' u v

namespace PresheafOfModules

variable {C : Type u'} [Category.{v'} C] (R : Cᵒᵖ ⥤ RingCat.{u})

/-- Colimits of shape `K` of presheaves of modules are exact when they are in abelian groups,
pulled back along the forgetful functor to presheaves of abelian groups.-/
instance hasExactColimitsOfShape (K : Type w) [Category.{w'} K]
    [HasColimitsOfShape K AddCommGrpCat.{v}] [HasExactColimitsOfShape K AddCommGrpCat.{v}] :
    HasExactColimitsOfShape K (PresheafOfModules.{v} R) :=
  HasExactColimitsOfShape.domain_of_functor K (toPresheaf R)

end PresheafOfModules
