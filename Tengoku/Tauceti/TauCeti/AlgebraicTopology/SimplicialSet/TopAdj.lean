/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.Geometry.Convex.ConvexSpace.Topology

/-!
# Naturality of singular simplices

The identification of singular simplices with continuous maps from standard simplices commutes
with continuous maps, which act by postcomposition; in particular, so does the identification of
points with singular zero-simplices. Faces of singular simplices obtained by precomposition with
affine simplices are also expressed in terms of their vertex maps.
This transfers naturality of simplicial vertex classes to singular homology, giving naturality
of the basepoint section of the augmentation in `TauCeti.singularHomology₀Section_naturality`.
Along an inducing map, a singular simplex of the target is induced from the source exactly when
its image lies in the range (`Topology.IsInducing.mem_range_toSSet_map_app_iff`).
-/

public section

open CategoryTheory Simplicial Convexity

universe u

namespace TauCeti.TopCat

/-- Mapping the singular vertex of a point gives the singular vertex of its image. -/
@[simp]
lemma toSSet_map_app_toSSetObj₀Equiv_symm {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    (TopCat.toSSet.map f).app (Opposite.op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSetObj₀Equiv.symm (f x) := rfl

/-- The map of singular simplicial sets induced by a continuous map acts on singular simplices
by postcomposition. -/
@[simp]
lemma toSSetObjEquiv_toSSet_map_app {X Y : TopCat.{u}} (f : X ⟶ Y) {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj X).obj n) :
    Y.toSSetObjEquiv n ((TopCat.toSSet.map f).app n σ) =
      (ConcreteCategory.hom f).comp (X.toSSetObjEquiv n σ) := rfl

end TauCeti.TopCat

namespace Topology.IsInducing

end Topology.IsInducing
