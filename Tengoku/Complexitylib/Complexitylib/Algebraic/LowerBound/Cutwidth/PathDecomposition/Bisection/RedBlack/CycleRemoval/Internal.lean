/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.CycleRemoval.Internal.Rank
public import Tengoku

/-!
# Removing designated edges from cycles

Choose a largest set of designated edges whose deletion preserves
reachability. Every remaining designated edge is then a bridge. The
number removed is bounded by the original cycle rank, since the surviving
graph still has the same connected components.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.CycleRemoval.Internal

open scoped Classical

variable {V : Type} [Fintype V] (B : SimpleGraph V)

end Algebraic.Cutwidth.Bisection.RedBlack.CycleRemoval.Internal
