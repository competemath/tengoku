/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.CutBoundary.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.CutBoundary.Internal

/-!
# Boundary counts for the bisection assembly

Both vertex boundaries are bounded by the number of crossing edges. Cutting
an induced subgraph on the same side cannot increase that edge count.
-/

@[expose] public section

namespace Algebraic.Cutwidth

open scoped Classical

variable {W : Type} [Fintype W] (H : SimpleGraph W)

/-- The two orientations of a cut have the same crossing edges.
@isnad1 id=eq.0h3v.s5.80778f4c8e62 from=translated src=- shape=4d3f6c15 vocab=c1d58351
-/
theorem cutFinset_compl (S : Finset W) : H.cutFinset Sᶜ = H.cutFinset S :=
  PathDecomposition.Internal.cutFinset_compl H S

/-- Each boundary vertex can be charged to a distinct crossing edge.
@isnad1 id=le.0h3v.s4.21745a42d51d from=translated src=- shape=2c991243 vocab=a62b63a1
-/
theorem card_cutBoundary_le (S : Finset W) :
    (cutBoundary H S).card ≤ (H.cutFinset S).card :=
  PathDecomposition.Internal.card_cutBoundary_le H S

/-- Inducing a graph cannot increase the number of edges crossing a fixed side.
@isnad1 id=le.0h4v.s6.350f7e523dab from=translated src=- shape=724d7c3b vocab=ace10c27
-/
theorem card_cutFinset_induce_le (S : Finset W) (T : Set W)
    [DecidablePred (· ∈ T)] [Fintype T] :
    ((H.induce T).cutFinset (S.subtype (· ∈ T))).card ≤ (H.cutFinset S).card :=
  PathDecomposition.Internal.card_cutFinset_induce_le H S T

end Algebraic.Cutwidth
