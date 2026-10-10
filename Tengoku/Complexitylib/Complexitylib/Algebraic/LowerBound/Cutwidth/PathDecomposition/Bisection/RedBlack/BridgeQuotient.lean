/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.BridgeQuotient.Defs
public import Tengoku
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.BridgeQuotient.Internal
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.BridgeQuotient.Internal.Regions

/-!
# Contracting the pieces between bridges

The component quotient preserves reachability. If every designated edge
is a bridge, it is a forest, and every one of its connected components is
a tree. The quotient also preserves the designated actual edges exactly:
none becomes a loop and distinct edges do not merge into parallel copies.

In Monien and Preis's red/black argument, cycles avoid all thin regions
after cycle removal. Every surviving region-boundary edge is therefore a
bridge, so contracting the pieces between those boundaries gives a forest.
This supplies the contraction step. `PathSuppression` removes the thin-path
vertices from the quotient. The weighted-tree reorganization is not formalized;
`RedBlack.Clusters` proves the red/black lemma by another route.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.BridgeQuotient

variable {V : Type} (B : SimpleGraph V) (F : Set (Sym2 V))

/-- Original walks project to reachability between the corresponding quotient vertices. -/
theorem reachable_project {u v : V} (reachable : B.Reachable u v) :
    (graph B F).Reachable ((B.deleteEdges F).connectedComponentMk u)
      ((B.deleteEdges F).connectedComponentMk v) :=
  Internal.reachable_project B F reachable

/-- Quotient reachability is exactly original reachability between any chosen representatives. -/
theorem reachable_iff {C D : (B.deleteEdges F).ConnectedComponent} {u v : V}
    (hu : u ∈ C.supp) (hv : v ∈ D.supp) :
    (graph B F).Reachable C D ↔ B.Reachable u v :=
  Internal.reachable_iff B F hu hv

/-- Contracting connected pieces preserves connectedness. -/
theorem connected (original : B.Connected) : (graph B F).Connected :=
  Internal.connected B F original

/-- The designated actual edges map onto all quotient edges, without loops. -/
theorem edge_image (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e) :
    Sym2.map (B.deleteEdges F).connectedComponentMk '' (F ∩ B.edgeSet) =
      (graph B F).edgeSet :=
  Internal.edge_image B F bridges

/-- Distinct designated bridges remain distinct edges after contraction. -/
theorem edge_map_injOn (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e) :
    Set.InjOn (Sym2.map (B.deleteEdges F).connectedComponentMk) (F ∩ B.edgeSet) :=
  Internal.edge_map_injOn B F bridges

/-- The quotient has exactly as many edges as there are designated actual bridges. -/
theorem edge_ncard (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e) :
    (graph B F).edgeSet.ncard = (F ∩ B.edgeSet).ncard :=
  Internal.edge_ncard B F bridges

/-- Contracting the connected pieces between bridges produces a forest. -/
theorem isAcyclic (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e) : (graph B F).IsAcyclic :=
  Internal.isAcyclic B F bridges

/-- A connected graph gives a tree when the contracted pieces are separated by bridges. -/
theorem isTree (original : B.Connected) (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e) :
    (graph B F).IsTree :=
  Internal.isTree B F original bridges

/-- Each component of a bridge quotient is a tree, including isolated vertices. -/
theorem component_isTree (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e)
    (C : (graph B F).ConnectedComponent) : C.toSimpleGraph.IsTree :=
  Internal.component_isTree B F bridges C

variable [Fintype V]

open scoped Classical

/-- Deleting region boundaries preserves the induced graph inside each disjoint region. -/
theorem induce_delete_region_cuts {ι : Type} (P : ι → Finset V)
    (disjoint : Pairwise (fun i j => Disjoint (P i) (P j)))
    (removed : Set (Sym2 V)) (subset : removed ⊆ ⋃ i, (B.cutFinset (P i) : Set (Sym2 V)))
    (i : ι) : (B.deleteEdges removed).induce {v | v ∈ P i} = B.induce {v | v ∈ P i} :=
  Internal.induce_delete_region_cuts B P disjoint removed subset i

/-- A region-boundary edge is a bridge whenever all cycles avoid the regions. -/
theorem isBridge_of_mem_region_cut {ι : Type} (P : ι → Finset V)
    (avoids : ∀ u (p : B.Walk u u), p.IsCycle → ∀ i v, v ∈ P i → v ∉ p.support)
    {i : ι} {e : Sym2 V} (member : e ∈ B.cutFinset (P i)) : B.IsBridge e :=
  Internal.isBridge_of_mem_region_cut B P avoids member

/-- If every cycle avoids the regions, contracting the pieces between their
boundaries produces a forest. -/
theorem ofRegions_isAcyclic {ι : Type} (P : ι → Finset V)
    (avoids : ∀ u (p : B.Walk u u), p.IsCycle → ∀ i v, v ∈ P i → v ∉ p.support) :
    (ofRegions B P).IsAcyclic :=
  Internal.ofRegions_isAcyclic B P avoids

/-- After cycles through the regions have been eliminated, every component
of the region-boundary quotient is a tree. -/
theorem ofRegions_component_isTree {ι : Type} (P : ι → Finset V)
    (avoids : ∀ u (p : B.Walk u u), p.IsCycle → ∀ i v, v ∈ P i → v ∉ p.support)
    (C : (ofRegions B P).ConnectedComponent) : C.toSimpleGraph.IsTree :=
  Internal.ofRegions_component_isTree B P avoids C

end Algebraic.Cutwidth.Bisection.RedBlack.BridgeQuotient
