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

/-- Original walks project to reachability between the corresponding quotient vertices.
@isnad1 id=reachabl.1h5v.s5.8525d3293bce from=translated src=- shape=8a73ffb2 vocab=08656a34
-/
theorem reachable_project {u v : V} (reachable : B.Reachable u v) :
    (graph B F).Reachable ((B.deleteEdges F).connectedComponentMk u)
      ((B.deleteEdges F).connectedComponentMk v) :=
  Internal.reachable_project B F reachable

/-- Quotient reachability is exactly original reachability between any chosen representatives.
@isnad1 id=iff.2h7v.s6.675dafacf4a6 from=translated src=- shape=adf3ce13 vocab=c11e2734
-/
theorem reachable_iff {C D : (B.deleteEdges F).ConnectedComponent} {u v : V}
    (hu : u ∈ C.supp) (hv : v ∈ D.supp) :
    (graph B F).Reachable C D ↔ B.Reachable u v :=
  Internal.reachable_iff B F hu hv

/-- Contracting connected pieces preserves connectedness.
@isnad1 id=connecte.1h3v.s4.8736f1907ecd from=translated src=- shape=039da043 vocab=cdc0a5f5
-/
theorem connected (original : B.Connected) : (graph B F).Connected :=
  Internal.connected B F original

/-- The designated actual edges map onto all quotient edges, without loops.
@isnad1 id=eq.1h3v.s6.3d979c6e40ec from=translated src=- shape=0492954a vocab=a65194e0
-/
theorem edge_image (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e) :
    Sym2.map (B.deleteEdges F).connectedComponentMk '' (F ∩ B.edgeSet) =
      (graph B F).edgeSet :=
  Internal.edge_image B F bridges

/-- Distinct designated bridges remain distinct edges after contraction.
@isnad1 id=injon.1h3v.s6.452da6a9a42a from=translated src=- shape=0c2e7ee1 vocab=82136f04
-/
theorem edge_map_injOn (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e) :
    Set.InjOn (Sym2.map (B.deleteEdges F).connectedComponentMk) (F ∩ B.edgeSet) :=
  Internal.edge_map_injOn B F bridges

/-- The quotient has exactly as many edges as there are designated actual bridges.
@isnad1 id=eq.1h3v.s6.b6f45195037c from=translated src=- shape=b2c5c1bc vocab=042008b9
-/
theorem edge_ncard (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e) :
    (graph B F).edgeSet.ncard = (F ∩ B.edgeSet).ncard :=
  Internal.edge_ncard B F bridges

/-- Contracting the connected pieces between bridges produces a forest.
@isnad1 id=isacycli.1h3v.s5.41f07cd13e25 from=translated src=- shape=06f4b783 vocab=96dd98aa
-/
theorem isAcyclic (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e) : (graph B F).IsAcyclic :=
  Internal.isAcyclic B F bridges

/-- A connected graph gives a tree when the contracted pieces are separated by bridges.
@isnad1 id=istree.2h3v.s5.4737e921de39 from=translated src=- shape=61229f23 vocab=f1ef9ff2
-/
theorem isTree (original : B.Connected) (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e) :
    (graph B F).IsTree :=
  Internal.isTree B F original bridges

/-- Each component of a bridge quotient is a tree, including isolated vertices.
@isnad1 id=istree.1h4v.s6.291a9946401d from=translated src=- shape=2a351d7c vocab=039e1b0a
-/
theorem component_isTree (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e)
    (C : (graph B F).ConnectedComponent) : C.toSimpleGraph.IsTree :=
  Internal.component_isTree B F bridges C

variable [Fintype V]

open scoped Classical

/-- Deleting region boundaries preserves the induced graph inside each disjoint region.
@isnad1 id=eq.2h6v.s7.06efc4f94809 from=translated src=- shape=e2cfdea8 vocab=3c730df5
-/
theorem induce_delete_region_cuts {ι : Type} (P : ι → Finset V)
    (disjoint : Pairwise (fun i j => Disjoint (P i) (P j)))
    (removed : Set (Sym2 V)) (subset : removed ⊆ ⋃ i, (B.cutFinset (P i) : Set (Sym2 V)))
    (i : ι) : (B.deleteEdges removed).induce {v | v ∈ P i} = B.induce {v | v ∈ P i} :=
  Internal.induce_delete_region_cuts B P disjoint removed subset i

/-- A region-boundary edge is a bridge whenever all cycles avoid the regions.
@isnad1 id=isbridge.2h6v.s6.031c1a24ea48 from=translated src=- shape=82c26501 vocab=b3c131a2
-/
theorem isBridge_of_mem_region_cut {ι : Type} (P : ι → Finset V)
    (avoids : ∀ u (p : B.Walk u u), p.IsCycle → ∀ i v, v ∈ P i → v ∉ p.support)
    {i : ι} {e : Sym2 V} (member : e ∈ B.cutFinset (P i)) : B.IsBridge e :=
  Internal.isBridge_of_mem_region_cut B P avoids member

/-- If every cycle avoids the regions, contracting the pieces between their
boundaries produces a forest.
@isnad1 id=isacycli.1h4v.s6.c32d2502c28d from=translated src=- shape=855fa7e4 vocab=14b7f972
-/
theorem ofRegions_isAcyclic {ι : Type} (P : ι → Finset V)
    (avoids : ∀ u (p : B.Walk u u), p.IsCycle → ∀ i v, v ∈ P i → v ∉ p.support) :
    (ofRegions B P).IsAcyclic :=
  Internal.ofRegions_isAcyclic B P avoids

/-- After cycles through the regions have been eliminated, every component
of the region-boundary quotient is a tree.
@isnad1 id=istree.1h5v.s8.589934b78044 from=translated src=- shape=afd64f70 vocab=fe83e406
-/
theorem ofRegions_component_isTree {ι : Type} (P : ι → Finset V)
    (avoids : ∀ u (p : B.Walk u u), p.IsCycle → ∀ i v, v ∈ P i → v ∉ p.support)
    (C : (ofRegions B P).ConnectedComponent) : C.toSimpleGraph.IsTree :=
  Internal.ofRegions_component_isTree B P avoids C

end Algebraic.Cutwidth.Bisection.RedBlack.BridgeQuotient
