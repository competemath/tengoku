/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition

/-!
# Spanning paths in connected graphs of degree at most two

A longest simple path cannot have an external neighbor at an endpoint.
At an internal vertex its two path neighbors exhaust the ambient degree.
Connectivity therefore forces the path to span the graph, including when
the graph is a cycle. This supplies an ordering for the degree-two regions
in Monien and Preis's thin-path argument.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal

open scoped Classical

variable {V : Type} [Fintype V] (B : SimpleGraph V)

end Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal
