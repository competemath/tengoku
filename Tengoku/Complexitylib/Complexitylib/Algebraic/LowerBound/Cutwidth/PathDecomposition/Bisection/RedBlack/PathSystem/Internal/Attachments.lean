/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Internal
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Internal.Thin
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Internal

/-!
# Constructing the thin-path restoration family

Select the induced degree-two regions that are thin relative to their
actual red attachments to small black components. Unless a positive set
of at most `8 M + 1` vertices already exists, each selected region has one
or two attachments, at most `2 M` vertices, and a nonempty black boundary.
Choose one attached small component per region. When eligible vertices
belong to large black components, this constructs a restoration family
whose region plus attachment has at most `3 M` vertices.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal

open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] (B : SimpleGraph V) (R : Multigraph V E)

theorem mem_attachmentEdges {P : Finset V} {M : Nat} {e : E} :
    e ∈ attachmentEdges B R P M ↔
      (R.fst e ∈ P ∧ Fintype.card (B.connectedComponentMk (R.snd e)) ≤ M) ∨
        (R.snd e ∈ P ∧ Fintype.card (B.connectedComponentMk (R.fst e)) ≤ M) := by
  simp [attachmentEdges]

end Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal
