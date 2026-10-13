/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Operations.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Padding.Internal

/-!
# Padding path decompositions by a boundary

Insert a fixed boundary in every bag and at both ends. The added boundary
may overlap the induced copy of the original graph.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition

open scoped Classical

/-- Extend an induced copy's decomposition by adding `X` to all bags and as
both endpoints. Every vertex outside the copy must lie in `X`.
@isnad1 id=ex.2h8v.s7.4aaaa61efe02 from=translated src=- shape=2f2fc192 vocab=1c90c41c
-/
theorem exists_pad {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (D : PathDecomposition G) (f : G ↪g H) (X : Finset W)
    (cover : ∀ w, w ∈ Set.range f ∨ w ∈ X) {b : Nat}
    (bound : ∀ i, (D.bag i).card ≤ b) :
    ∃ E : PathDecomposition H, E.StartsAt X ∧ E.EndsAt X ∧
      ∀ i, (E.bag i).card ≤ X.card + b :=
  Internal.exists_pad D f X cover bound

end Algebraic.Cutwidth.PathDecomposition
