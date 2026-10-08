/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Operations.Defs
public import Tengoku
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Endpoint.Internal

/-!
# Prescribed endpoints in subcubic graphs

The endpoint induction of Fomin and Høie's *Pathwidth of cubic graphs and
exact algorithms* (2006), Lemma 4, using the elementary base-two tree bound.
This finite result has no bisection hypothesis. `Bisection` uses it to prove
the cubic pathwidth theorem from the Monien–Preis bisection hypothesis.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition

open scoped Classical

end Algebraic.Cutwidth.PathDecomposition
