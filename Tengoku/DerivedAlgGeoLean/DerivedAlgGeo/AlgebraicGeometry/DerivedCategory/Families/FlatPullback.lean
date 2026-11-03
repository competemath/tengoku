/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.Algebra.Category.ModuleCat.Descent
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Flat
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.ExactPullback
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Stalk

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact pullback along flat morphisms

The canonical module pullback-to-stalk comparison lives in
`AlgebraicGeometry.Modules.Pullback.Stalk`.  A flat scheme morphism has flat
maps on local rings, so extension of scalars preserves finite limits at every
stalk.  Joint reflection by module stalks then proves that module-sheaf
pullback preserves finite limits, and hence is exact.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}}

/-- At every point of a flat scheme morphism, extension of scalars along the
induced local-ring map preserves finite limits.
@isnad1 id=preserve.0h5v.s11.421916f9be70 from=translated src=- shape=fb296508 vocab=6aa135ff
-/
theorem flatStalkMap_preservesFiniteLimits
    {T U : SchemeBaseChange S} (f : T ⟶ U) [Flat f.left] (x : T.left) :
    PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (f.left.stalkMap x).hom) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (Flat.stalkMap f.left x)

/-- The stalkwise model for pullback along a flat scheme morphism preserves
finite limits.
@isnad1 id=preserve.0h5v.s11.1d1c5d0117b8 from=translated src=- shape=6430d243 vocab=c3b3ac59
-/
theorem flatPullbackStalkModel_preservesFiniteLimits
    {T U : SchemeBaseChange S} (f : T ⟶ U) [Flat f.left] (x : T.left) :
    PreservesFiniteLimits
      (Scheme.Modules.moduleStalkFunctor U.left (f.left x) ⋙
        ModuleCat.extendScalars.{u, u, u} (f.left.stalkMap x).hom) := by
  have hStalk : PreservesFiniteLimits
      (Scheme.Modules.moduleStalkFunctor U.left (f.left x)) :=
    Scheme.Modules.moduleStalkFunctor_preservesFiniteLimits U.left (f.left x)
  have hScalars : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (f.left.stalkMap x).hom) :=
    flatStalkMap_preservesFiniteLimits f x
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ hStalk hScalars

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families
