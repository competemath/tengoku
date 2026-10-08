/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
public import Tengoku
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Tree.Internal

/-!
# Logarithmic-width decompositions of trees

Repeatedly deleting a centroid gives bags of size at most `⌈log₂ n⌉ + 1`.
This elementary bound suffices for the tree component in Fomin and Høie's
endpoint induction; their sharper logarithmic term is not needed for the
asymptotic coefficient `1/6` in the cubic-graph pathwidth bound.
-/

@[expose] public section

namespace Algebraic.Cutwidth

open scoped Classical

end Algebraic.Cutwidth
