/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Glue
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Operations
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Tree
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.TreeComponent

/-!
# The subcubic endpoint induction

This proves the prescribed-endpoint decomposition in Fomin and Høie's
Lemma 4, using the elementary base-two tree bound. The resulting bags have
size at most `max |X| (n / 3 + 1) + ceil(log₂ n) + 1`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition.Internal

open scoped Classical

end Algebraic.Cutwidth.PathDecomposition.Internal
