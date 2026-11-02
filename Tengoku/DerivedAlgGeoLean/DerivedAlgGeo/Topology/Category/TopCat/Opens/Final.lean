/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.CategoryTheory.Filtered.Connected
import Tengoku.Seed.Topology.Sheaves.SheafCondition.Sites

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Inverse image on opens is a final functor

For a continuous map `f : X ⟶ Y`, the inverse-image functor `Opens.map f : Opens Y ⥤ Opens X` is
final.  Mathlib makes it representably flat, so every structured-arrow category under it is
cofiltered, hence connected, which is finality.

## Main results

* `TopologicalSpace.Opens.map_final`: the instance.

## Implementation notes

This is what makes `SheafOfModules.pullbackObjUnitToUnit` an isomorphism along every morphism
of ringed spaces over `f`, in particular along every morphism of schemes: Mathlib states that
isomorphism under a `Final` hypothesis on the underlying functor of opens.  The instance lives
here, with the carrier, rather than in the module-sheaf consumer that first needed it.
-/

open CategoryTheory

namespace TopologicalSpace.Opens

end TopologicalSpace.Opens
