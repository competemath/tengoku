/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku

/-!
# Continuity of affine maps between standard simplices

An affine map `Convexity.StdSimplex.affineMapMk v` out of a standard simplex is determined by the
images `v m` of the vertices. When the target is a standard simplex on a finite type, its
weights are the bilinear expressions `∑ m, w.weights m * (v m).weights n`, so the map is
continuous; `Convexity.StdSimplex.continuousAffineMapMk` bundles it as a continuous map. This
makes affine simplices, such as the simplices of a barycentric subdivision,
available as continuous maps between topological standard simplices.
-/

public section

namespace Convexity.StdSimplex

variable {R : Type*} [PartialOrder R] {M N : Type*}

section Semiring

variable [Semiring R] [IsStrictOrderedRing R]

end Semiring

variable [Ring R] [IsStrictOrderedRing R] [TopologicalSpace R] [IsTopologicalRing R]

end Convexity.StdSimplex
