/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Core.Internal.Structure
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.WeightedTree
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Core.Internal

/-!
# Positive witnesses from light weighted core pairs

Natural weights that dominate core-piece sizes transfer the weighted-forest
bound to a small positive witness after simultaneous restoration. The forest
version requires heavy leaves and isolated vertices and a strict average
bound. For a nontrivial tree, a total bound by `M` times one fewer than its
number of vertices also suffices.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily.Internal

open scoped Classical

variable {V E ι : Type} [Fintype V] [Fintype E] [Fintype ι]
  {B : SimpleGraph V} {R : Multigraph V E} (F : RestorationFamily B R ι)

end Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily.Internal
