/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Components
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Operations

/-!
# Tree separators and path decompositions

A vertex minimizing the sum of distances is a centroid: every component
left after deleting it contains at most half the vertices. This supplies
the balanced recursion used for logarithmic-width tree decompositions.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition.Internal

open scoped Classical

variable {W : Type} {H : SimpleGraph W}

end Algebraic.Cutwidth.PathDecomposition.Internal
