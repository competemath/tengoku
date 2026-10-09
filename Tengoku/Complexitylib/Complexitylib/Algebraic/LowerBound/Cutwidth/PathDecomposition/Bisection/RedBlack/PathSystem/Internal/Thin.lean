/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Internal.SpanningPath
public import Tengoku

/-!
# Ordering red attachments along a degree-two region

A finite set of red attachments to a connected degree-two region can be
ordered along a spanning path. Thus Monien and Preis's thin-walk witness
applies directly to a vertex set and its attachments, without supplying a
walk or ordered positions. Repeated attachment positions are allowed.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal

open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] (B : SimpleGraph V) (R : Multigraph V E)

end Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal
