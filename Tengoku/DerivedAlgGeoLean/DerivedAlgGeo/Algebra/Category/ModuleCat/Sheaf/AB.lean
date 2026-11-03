/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Tengoku.Seed.Algebra.Category.ModuleCat.Sheaf.Abelian
import Tengoku.Seed.Algebra.Category.ModuleCat.Sheaf.Colimits
import Tengoku.Seed.Algebra.Category.ModuleCat.Sheaf.Limits
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Algebra.Category.ModuleCat.Presheaf.AB

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact colimits of sheaves of modules

Colimits of sheaves of modules of a shape `K` are exact when colimits of that shape are exact
in abelian groups: the sheafification adjunction has a fully faithful right adjoint and a left
adjoint preserving finite limits, so exactness descends from presheaves of modules by
Mathlib's `Adjunction.hasExactColimitsOfShape`.  In particular sheaves of modules on a ringed
site satisfy AB4 and AB5 in the universes where abelian groups do, the input to coproducts in
their derived category.

## Main results

* `SheafOfModules.hasExactColimitsOfShape`: the per-shape instance.
* `SheafOfModules.ab4OfSize`, `SheafOfModules.ab5OfSize`: the Grothendieck axioms.
-/

open CategoryTheory Limits

universe w' w v' u' u v

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- Colimits of shape `K` of sheaves of modules are exact when they are in abelian groups,
through the sheafification adjunction: its right adjoint is fully faithful and its left adjoint
preserves finite limits, which is what `Adjunction.hasExactColimitsOfShape` needs.
`HasSheafify` (not merely `HasWeakSheafify`) is required because Mathlib proves
`PreservesFiniteLimits (sheafification α)` and `Abelian (SheafOfModules R)` only under it.
@isnad1 id=hasexact.0h4v.s7.8ab08185429e from=translated src=- shape=51261696 vocab=27ae5656
-/
instance hasExactColimitsOfShape (K : Type w) [Category.{w'} K]
    [HasColimitsOfShape K AddCommGrpCat.{v}] [HasExactColimitsOfShape K AddCommGrpCat.{v}] :
    HasExactColimitsOfShape K (SheafOfModules.{v} R) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).hasExactColimitsOfShape K

end SheafOfModules
