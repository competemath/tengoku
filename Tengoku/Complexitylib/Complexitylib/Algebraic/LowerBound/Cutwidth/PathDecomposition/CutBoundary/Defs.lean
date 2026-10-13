/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition

/-!
# The vertex boundary of one side of a cut

The boundary consists of vertices on the given side that have a neighbor
on the other side. Its cardinality is at most the number of crossing edges.
-/

@[expose] public section

namespace Algebraic.Cutwidth

open scoped Classical

/-- Vertices of `S` incident to an edge crossing from `S` to its complement. -/
noncomputable def cutBoundary {W : Type} (H : SimpleGraph W) (S : Finset W) : Finset W :=
  S.filter fun u => ∃ v, v ∉ S ∧ H.Adj u v

/-- A boundary vertex is inside the side and has a neighbor outside.
@isnad1 id=iff.0h4v.s5.ba4822b4674e from=translated src=- shape=48cb9347 vocab=b09fef46
-/
theorem mem_cutBoundary {W : Type} (H : SimpleGraph W) {S : Finset W} {u : W} :
    u ∈ cutBoundary H S ↔ u ∈ S ∧ ∃ v, v ∉ S ∧ H.Adj u v :=
  Finset.mem_filter

/-- The boundary is contained in its side.
@isnad1 id=le.0h3v.s4.48cfe5f1604a from=translated src=- shape=544e900b vocab=f71bb5d9
-/
theorem cutBoundary_subset {W : Type} (H : SimpleGraph W) (S : Finset W) :
    cutBoundary H S ⊆ S :=
  Finset.filter_subset _ _

end Algebraic.Cutwidth
