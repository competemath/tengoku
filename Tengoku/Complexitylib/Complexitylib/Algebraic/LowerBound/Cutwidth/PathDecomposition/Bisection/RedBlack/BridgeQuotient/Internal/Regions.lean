/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.BridgeQuotient.Internal
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.CycleRemoval.Internal.Core

/-!
# Identifying region vertices in the boundary quotient

Disjoint connected regions remain internally connected when any of their
boundary edges are deleted. Once all region boundaries are deleted, each
region is exactly one connected component and hence one quotient vertex.
The degree of a quotient vertex is bounded by the original cut of its
component, with equality when designated edges are bridges. These statements
identify the path vertices to be suppressed and their exact degrees.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.BridgeQuotient.Internal

open scoped Classical

variable {V ι : Type} [Fintype V] (B : SimpleGraph V) (P : ι → Finset V)

theorem induce_delete_region_cuts (disjoint : Pairwise (fun i j => Disjoint (P i) (P j)))
    (removed : Set (Sym2 V)) (subset : removed ⊆ ⋃ i, (B.cutFinset (P i) : Set (Sym2 V)))
    (i : ι) : (B.deleteEdges removed).induce {v | v ∈ P i} = B.induce {v | v ∈ P i} := by
  ext a b
  change (B.deleteEdges removed).Adj a.val b.val ↔ B.Adj a.val b.val
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨fun h => h.1, fun ab => ⟨ab, ?_⟩⟩
  intro deleted
  obtain ⟨j, crossing⟩ := Set.mem_iUnion.mp (subset deleted)
  have crossing := (B.mem_cutFinset_mk.mp crossing).2
  by_cases same : i = j
  · rw [← same] at crossing
    rcases crossing with ⟨_, outside⟩ | ⟨_, outside⟩
    · exact outside b.property
    · exact outside a.property
  · rcases crossing with ⟨ha, _⟩ | ⟨hb, _⟩
    · exact Finset.disjoint_left.mp (disjoint same) a.property ha
    · exact Finset.disjoint_left.mp (disjoint same) b.property hb

end Algebraic.Cutwidth.Bisection.RedBlack.BridgeQuotient.Internal
