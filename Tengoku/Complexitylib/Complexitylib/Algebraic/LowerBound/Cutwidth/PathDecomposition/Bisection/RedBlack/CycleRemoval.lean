/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.CycleRemoval.Internal
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.CycleRemoval.Internal.Core

/-!
# Breaking all cycles through designated edges

A finite graph admits deletion of designated edges so that every retained
designated edge is a bridge, while reachability and connected components
are preserved. The number deleted is at most the original cycle rank:
`|E| - |V| + number of components`, expressed without natural subtraction.
Untouched cyclic components reserve one unit of this rank each, in addition
to the units used by deleted edges.

A cycle meeting a connected region of black degree at most two contains
every boundary edge of that region. Designating one boundary edge per
region therefore suffices to break all cycles through the regions. If
the designated edges are distinct, at most the original cycle rank many
regions need be isolated, and the result has no cycle through any region.
Deleting full cuts also preserves reachability between vertices outside
the selected regions: after the first edge deletion, a simple path cannot
enter and leave a region through its sole remaining boundary edge.

This supplies cycle selection for a given thin-path system in Monien and
Preis's proof. `PathSystem` constructs and instantiates that system.
`BridgeQuotient` contracts the pieces between surviving boundaries to a
forest. `PathSystem.Marks` counts the initial attachment marks and reserves
rank for small cyclic components. Monien and Preis's weighted-tree
reorganization is not formalized; `RedBlack.Clusters` proves the red/black
lemma by another route.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack

open scoped Classical

variable {V : Type} [Fintype V] (B : SimpleGraph V)

/-- Every cyclic component uses at least one unit of cycle rank. -/
theorem card_vertices_add_cyclic_le (cyclic : Finset B.ConnectedComponent)
    (cycles : ∀ C ∈ cyclic, ¬ C.toSimpleGraph.IsAcyclic) :
    Fintype.card V + cyclic.card ≤ B.edgeFinset.card + Nat.card B.ConnectedComponent :=
  CycleRemoval.Internal.card_vertices_add_cyclic_le B cyclic cycles

/-- Reachability-preserving deletions and untouched cyclic components together
use at most the original cycle rank. -/
theorem card_removed_add_untouched_cyclic_le (removed : Finset (Sym2 V))
    (edges : removed ⊆ B.edgeFinset)
    (reachable : (B.deleteEdges (removed : Set (Sym2 V))).Reachable = B.Reachable)
    (cyclic : Finset B.ConnectedComponent)
    (cycles : ∀ C ∈ cyclic, ¬ C.toSimpleGraph.IsAcyclic)
    (kept : ∀ C ∈ cyclic, ∀ {u v}, u ∈ C.supp → v ∈ C.supp →
      B.Adj u v → s(u, v) ∉ removed) :
    removed.card + cyclic.card + Fintype.card V ≤
      B.edgeFinset.card + Nat.card B.ConnectedComponent :=
  CycleRemoval.Internal.card_removed_add_untouched_cyclic_le B removed edges reachable
    cyclic cycles kept

end Algebraic.Cutwidth.Bisection.RedBlack
