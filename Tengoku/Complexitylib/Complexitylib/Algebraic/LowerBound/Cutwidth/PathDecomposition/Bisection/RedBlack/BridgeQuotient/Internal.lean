/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.BridgeQuotient.Defs
public import Tengoku

/-!
# Connectivity and acyclicity of bridge quotients

Walks project to the component quotient and quotient walks lift through
the connected contracted pieces. An original bridge remains a bridge in
the quotient: a quotient path avoiding its image would lift to an original
path avoiding the bridge. Thus contracting along the complement of a set
of bridges produces a forest, and a tree when the original graph is connected.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.BridgeQuotient.Internal

variable {V : Type} (B : SimpleGraph V) (F : Set (Sym2 V))

private theorem lift_reachable (K : SimpleGraph V)
    (Q : SimpleGraph (B.deleteEdges F).ConnectedComponent) (kept : B.deleteEdges F ≤ K)
    (adjacent : ∀ C D, Q.Adj C D → ∃ u ∈ C.supp, ∃ v ∈ D.supp, K.Adj u v)
    {C D : (B.deleteEdges F).ConnectedComponent} (reachable : Q.Reachable C D)
    {u v : V} (hu : u ∈ C.supp) (hv : v ∈ D.supp) : K.Reachable u v := by
  obtain ⟨p⟩ := reachable
  induction p generalizing u v with
  | @nil C => exact (C.reachable_of_mem_supp hu hv).mono kept
  | @cons C D E edge p ih =>
    obtain ⟨a, ha, b, hb, ab⟩ := adjacent C D edge
    exact ((C.reachable_of_mem_supp hu ha).mono kept).trans (ab.reachable.trans (ih hb hv))

/--
@isnad1 id=reachabl.3h7v.s6.5569c776d935 from=translated src=- shape=6f79deac vocab=c11e2734
-/
theorem reachable_lift {C D : (B.deleteEdges F).ConnectedComponent}
    (reachable : (graph B F).Reachable C D) {u v : V} (hu : u ∈ C.supp) (hv : v ∈ D.supp) :
    B.Reachable u v :=
  lift_reachable B F B (graph B F) (SimpleGraph.deleteEdges_le _) (fun _ _ h => h.2)
    reachable hu hv

/--
@isnad1 id=reachabl.1h5v.s5.8525d3293bce from=translated src=- shape=8a73ffb2 vocab=08656a34
-/
theorem reachable_project {u v : V} (reachable : B.Reachable u v) :
    (graph B F).Reachable ((B.deleteEdges F).connectedComponentMk u)
      ((B.deleteEdges F).connectedComponentMk v) := by
  obtain ⟨p⟩ := reachable
  induction p with
  | nil => exact SimpleGraph.Reachable.rfl
  | @cons a b c ab p ih =>
    by_cases same : (B.deleteEdges F).connectedComponentMk a =
        (B.deleteEdges F).connectedComponentMk b
    · exact same ▸ ih
    · have edge : (graph B F).Adj ((B.deleteEdges F).connectedComponentMk a)
          ((B.deleteEdges F).connectedComponentMk b) := by
        refine ⟨same, a, ?_, b, ?_, ab⟩ <;> exact
          (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
      exact edge.reachable.trans ih

/--
@isnad1 id=iff.2h7v.s6.675dafacf4a6 from=translated src=- shape=adf3ce13 vocab=c11e2734
-/
theorem reachable_iff {C D : (B.deleteEdges F).ConnectedComponent} {u v : V}
    (hu : u ∈ C.supp) (hv : v ∈ D.supp) :
    (graph B F).Reachable C D ↔ B.Reachable u v := by
  refine ⟨fun h => reachable_lift B F h hu hv, fun h => ?_⟩
  have projected := reachable_project B F h
  rwa [(C.mem_supp_iff u).mp hu, (D.mem_supp_iff v).mp hv] at projected

/--
@isnad1 id=connecte.1h3v.s4.8736f1907ecd from=translated src=- shape=039da043 vocab=cdc0a5f5
-/
theorem connected (original : B.Connected) : (graph B F).Connected where
  preconnected C D := (reachable_iff B F C.out_eq D.out_eq).mpr
    (original.preconnected C.out D.out)
  nonempty := original.nonempty.map (B.deleteEdges F).connectedComponentMk

private theorem edge_mem_deleted {C D : (B.deleteEdges F).ConnectedComponent}
    (different : C ≠ D) {u v : V} (hu : u ∈ C.supp) (hv : v ∈ D.supp)
    (adjacent : B.Adj u v) : s(u, v) ∈ F := by
  by_contra fresh
  have kept : (B.deleteEdges F).Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨adjacent, fresh⟩
  exact different (SimpleGraph.ConnectedComponent.eq_of_common_vertex
    (C.mem_supp_of_adj_mem_supp hu kept) hv)

private theorem endpoints_ne_of_bridge {u v : V} (bridge : B.IsBridge s(u, v))
    (removed : s(u, v) ∈ F) :
    (B.deleteEdges F).connectedComponentMk u ≠ (B.deleteEdges F).connectedComponentMk v := by
  intro equal
  exact (SimpleGraph.isBridge_iff.mp bridge)
    ((SimpleGraph.ConnectedComponent.exact equal).mono
      (SimpleGraph.deleteEdges_anti (Set.singleton_subset_iff.mpr removed)))

/--
@isnad1 id=eq.1h3v.s6.3d979c6e40ec from=translated src=- shape=0492954a vocab=a65194e0
-/
theorem edge_image (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e) :
    Sym2.map (B.deleteEdges F).connectedComponentMk '' (F ∩ B.edgeSet) =
      (graph B F).edgeSet := by
  ext e
  constructor
  · rintro ⟨e, member, rfl⟩
    obtain ⟨u, v⟩ := e
    apply (graph B F).mem_edgeSet.mpr
    refine ⟨endpoints_ne_of_bridge B F (bridges _ member) member.1, u, ?_, v, ?_,
      B.mem_edgeSet.mp member.2⟩ <;> exact
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  · intro member
    obtain ⟨C, D⟩ := e
    obtain ⟨different, u, hu, v, hv, uv⟩ := (graph B F).mem_edgeSet.mp member
    refine ⟨s(u, v), ⟨edge_mem_deleted B F different hu hv uv, B.mem_edgeSet.mpr uv⟩, ?_⟩
    change s((B.deleteEdges F).connectedComponentMk u, (B.deleteEdges F).connectedComponentMk v) = _
    rw [(C.mem_supp_iff u).mp hu, (D.mem_supp_iff v).mp hv]

/--
@isnad1 id=injon.1h3v.s6.452da6a9a42a from=translated src=- shape=0c2e7ee1 vocab=82136f04
-/
theorem edge_map_injOn (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e) :
    Set.InjOn (Sym2.map (B.deleteEdges F).connectedComponentMk) (F ∩ B.edgeSet) := by
  intro e he f hf equal
  obtain ⟨u, v⟩ := e
  obtain ⟨a, b⟩ := f
  by_contra different
  have kept : B.deleteEdges F ≤ B.deleteEdges {s(u, v)} :=
    SimpleGraph.deleteEdges_anti (Set.singleton_subset_iff.mpr he.1)
  have adjacent : (B.deleteEdges {s(u, v)}).Adj a b := by
    refine SimpleGraph.deleteEdges_adj.mpr ⟨B.mem_edgeSet.mp hf.2, ?_⟩
    exact fun h => different (Set.mem_singleton_iff.mp h).symm
  apply SimpleGraph.isBridge_iff.mp (bridges _ he)
  change s((B.deleteEdges F).connectedComponentMk u, (B.deleteEdges F).connectedComponentMk v) =
    s((B.deleteEdges F).connectedComponentMk a, (B.deleteEdges F).connectedComponentMk b) at equal
  rcases Sym2.eq_iff.mp equal with ⟨left, right⟩ | ⟨left, right⟩
  · exact ((SimpleGraph.ConnectedComponent.exact left).mono kept).trans
      (adjacent.reachable.trans ((SimpleGraph.ConnectedComponent.exact right.symm).mono kept))
  · exact ((SimpleGraph.ConnectedComponent.exact left).mono kept).trans
      (adjacent.symm.reachable.trans ((SimpleGraph.ConnectedComponent.exact right.symm).mono kept))

/--
@isnad1 id=eq.1h3v.s6.b6f45195037c from=translated src=- shape=b2c5c1bc vocab=042008b9
-/
theorem edge_ncard (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e) :
    (graph B F).edgeSet.ncard = (F ∩ B.edgeSet).ncard := by
  rw [← edge_image B F bridges]
  exact (edge_map_injOn B F bridges).ncard_image

/--
@isnad1 id=isbridge.2h5v.s6.b560e89272e2 from=translated src=- shape=d0c2da91 vocab=73e4e5b4
-/
theorem isBridge_of_adj (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e)
    {C D : (B.deleteEdges F).ConnectedComponent} (edge : (graph B F).Adj C D) :
    (graph B F).IsBridge s(C, D) := by
  obtain ⟨different, u, hu, v, hv, uv⟩ := edge
  have removed := edge_mem_deleted B F different hu hv uv
  have bridge := bridges _ ⟨removed, B.mem_edgeSet.mpr uv⟩
  apply SimpleGraph.isBridge_iff.mpr
  intro reachable
  have kept : B.deleteEdges F ≤ B.deleteEdges {s(u, v)} :=
    SimpleGraph.deleteEdges_anti (Set.singleton_subset_iff.mpr removed)
  have allowed (A D' : (B.deleteEdges F).ConnectedComponent)
      (adjacent : ((graph B F).deleteEdges {s(C, D)}).Adj A D') :
      ∃ a ∈ A.supp, ∃ b ∈ D'.supp, (B.deleteEdges {s(u, v)}).Adj a b := by
    obtain ⟨⟨_, a, ha, b, hb, ab⟩, fresh⟩ := SimpleGraph.deleteEdges_adj.mp adjacent
    refine ⟨a, ha, b, hb, SimpleGraph.deleteEdges_adj.mpr ⟨ab, ?_⟩⟩
    intro equal
    have pair : s(a, b) = s(u, v) := Set.mem_singleton_iff.mp equal
    rcases Sym2.eq_iff.mp pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have left := SimpleGraph.ConnectedComponent.eq_of_common_vertex ha hu
      have right := SimpleGraph.ConnectedComponent.eq_of_common_vertex hb hv
      exact fresh (by simp [left, right])
    · have left := SimpleGraph.ConnectedComponent.eq_of_common_vertex ha hv
      have right := SimpleGraph.ConnectedComponent.eq_of_common_vertex hb hu
      exact fresh (by simp [left, right, Sym2.eq_swap])
  exact (SimpleGraph.isBridge_iff.mp bridge)
    (lift_reachable B F _ _ kept allowed reachable hu hv)

/--
@isnad1 id=isacycli.1h3v.s5.41f07cd13e25 from=translated src=- shape=06f4b783 vocab=96dd98aa
-/
theorem isAcyclic (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e) : (graph B F).IsAcyclic :=
  SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr
    (fun _ _ edge => isBridge_of_adj B F bridges edge)

/--
@isnad1 id=istree.2h3v.s5.4737e921de39 from=translated src=- shape=61229f23 vocab=f1ef9ff2
-/
theorem isTree (original : B.Connected) (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e) :
    (graph B F).IsTree :=
  ⟨connected B F original, isAcyclic B F bridges⟩

/--
@isnad1 id=istree.1h4v.s6.291a9946401d from=translated src=- shape=2a351d7c vocab=039e1b0a
-/
theorem component_isTree (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e)
    (C : (graph B F).ConnectedComponent) : C.toSimpleGraph.IsTree :=
  ⟨C.connected_toSimpleGraph, (isAcyclic B F bridges).induce C.supp⟩

variable [Fintype V]

/--
@isnad1 id=isbridge.2h6v.s6.031c1a24ea48 from=translated src=- shape=82c26501 vocab=b3c131a2
-/
theorem isBridge_of_mem_region_cut {ι : Type} (P : ι → Finset V)
    (avoids : ∀ u (p : B.Walk u u), p.IsCycle → ∀ i v, v ∈ P i → v ∉ p.support)
    {i : ι} {e : Sym2 V} (member : e ∈ B.cutFinset (P i)) : B.IsBridge e := by
  obtain ⟨edge, a, b, rfl, ha, _⟩ := B.mem_cutFinset.mp member
  apply (SimpleGraph.isBridge_iff_forall_cycle_notMem edge).mpr
  intro u p cycle member
  exact avoids u p cycle i a ha (p.fst_mem_support_of_mem_edges member)

/--
@isnad1 id=isacycli.1h4v.s6.c32d2502c28d from=translated src=- shape=855fa7e4 vocab=14b7f972
-/
theorem ofRegions_isAcyclic {ι : Type} (P : ι → Finset V)
    (avoids : ∀ u (p : B.Walk u u), p.IsCycle → ∀ i v, v ∈ P i → v ∉ p.support) :
    (ofRegions B P).IsAcyclic := by
  apply isAcyclic
  intro e he
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he.1
  exact isBridge_of_mem_region_cut B P avoids hi

/--
@isnad1 id=istree.1h5v.s8.589934b78044 from=translated src=- shape=afd64f70 vocab=fe83e406
-/
theorem ofRegions_component_isTree {ι : Type} (P : ι → Finset V)
    (avoids : ∀ u (p : B.Walk u u), p.IsCycle → ∀ i v, v ∈ P i → v ∉ p.support)
    (C : (ofRegions B P).ConnectedComponent) : C.toSimpleGraph.IsTree :=
  ⟨C.connected_toSimpleGraph, (ofRegions_isAcyclic B P avoids).induce C.supp⟩

end Algebraic.Cutwidth.Bisection.RedBlack.BridgeQuotient.Internal
