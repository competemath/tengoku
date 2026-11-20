import Tengoku.Erdos64.Erdos64.Basic
import Tengoku.Seed.Combinatorics.SimpleGraph.Matching

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

open scoped Classical

/-- A nontrivial simple path uses one edge at either endpoint and two at
each other vertex in its support.-/
theorem path_spanningCoe_degree_of_mem_support
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (hxy : x ≠ y) (v : V) (hv : v ∈ p.support) :
    p.toSubgraph.spanningCoe.degree v = if v = x ∨ v = y then 1 else 2 := by
  classical
  have hn : ¬p.Nil := fun h => hxy h.eq
  rw [SimpleGraph.Subgraph.degree_spanningCoe, SimpleGraph.Subgraph.degree,
    ← Set.toFinset_card, ← Set.ncard_eq_toFinset_card']
  by_cases hx : v = x
  · subst v
    simp [hp.neighborSet_toSubgraph_startpoint hn]
  by_cases hy : v = y
  · subst v
    simp [hp.neighborSet_toSubgraph_endpoint hn]
  rw [ite_eq_right (not_or.mpr ⟨hx, hy⟩)]
  obtain ⟨i, hi, hile⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv
  have hi0 : i ≠ 0 := by
    intro h
    exact hx (by simpa [h] using hi.symm)
  have hin : i < p.length := by
    have hne : i ≠ p.length := by
      intro h
      exact hy (by simpa [h] using hi.symm)
    omega
  rw [← hi]
  exact hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hin

/-- Removing a simple path subtracts exactly its used incidences.-/
theorem path_complement_degree_of_mem_support
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) (hxy : x ≠ y)
    (v : V) (hv : v ∈ p.support) :
    (G \ p.toSubgraph.spanningCoe).degree v =
      G.degree v - (if v = x ∨ v = y then 1 else 2) := by
  classical
  have hsub : p.toSubgraph.spanningCoe.neighborFinset v ⊆ G.neighborFinset v := by
    intro w hw
    exact (G.mem_neighborFinset v w).mpr
      (p.toSubgraph.adj_sub ((p.toSubgraph.spanningCoe.mem_neighborFinset v w).mp hw))
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_sdiff, Finset.card_sdiff_of_subset hsub,
    SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree,
    path_spanningCoe_degree_of_mem_support p hp hxy v hv]

/-- For a spanning simple path with degree-two endpoints and degree-three
internal vertices, the unused edges form a perfect matching on all vertices.
No minimal-counterexample or cycle-length premise is needed.-/
theorem spanning_two_port_path_complement_isPerfectMatching
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) (hxy : x ≠ y)
    (hspan : ∀ v, v ∈ p.support)
    (hdeg : ∀ v, G.degree v = if v = x ∨ v = y then 2 else 3) :
    (G.toSubgraph (G \ p.toSubgraph.spanningCoe) sdiff_le).IsPerfectMatching := by
  classical
  apply SimpleGraph.Subgraph.isPerfectMatching_iff_forall_degree.mpr
  intro v
  rw [SimpleGraph.degree_toSubgraph,
    path_complement_degree_of_mem_support p hp hxy v (hspan v), hdeg v]
  split_ifs <;> rfl

/-- Every vertex of a spanning cubic two-port path has a unique neighbor
joined by an unused edge. This is the matching in adjacency form.-/
theorem spanning_two_port_path_unique_unused_neighbor
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) (hxy : x ≠ y)
    (hspan : ∀ v, v ∈ p.support)
    (hdeg : ∀ v, G.degree v = if v = x ∨ v = y then 2 else 3)
    (v : V) :
    ∃! w, G.Adj v w ∧ s(v, w) ∉ p.edges := by
  have h := SimpleGraph.Subgraph.isPerfectMatching_iff.mp
    (spanning_two_port_path_complement_isPerfectMatching p hp hxy hspan hdeg) v
  simpa only [SimpleGraph.toSubgraph_adj, SimpleGraph.sdiff_adj,
    SimpleGraph.Subgraph.spanningCoe_adj, SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges] using h

/-- The unique unused neighbors pair the vertices by a fixed-point-free
involution. Thus the matching supplies actual partner data, with each pair
an ambient edge outside the path.-/
theorem spanning_two_port_path_matching_involution
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) (hxy : x ≠ y)
    (hspan : ∀ v, v ∈ p.support)
    (hdeg : ∀ v, G.degree v = if v = x ∨ v = y then 2 else 3) :
    ∃ mate : V → V, Function.Involutive mate ∧
      (∀ v, mate v ≠ v) ∧
      (∀ v w, G.Adj v w ∧ s(v, w) ∉ p.edges ↔ w = mate v) := by
  classical
  have hu := spanning_two_port_path_unique_unused_neighbor p hp hxy hspan hdeg
  let mate : V → V := fun v => (hu v).choose
  have hm (v : V) : (G.Adj v (mate v) ∧ s(v, mate v) ∉ p.edges) ∧
      ∀ w, G.Adj v w ∧ s(v, w) ∉ p.edges → w = mate v := (hu v).choose_spec
  refine ⟨mate, ?_, ?_, ?_⟩
  · intro v
    apply Eq.symm
    apply (hm (mate v)).2
    refine ⟨(hm v).1.1.symm, ?_⟩
    simpa only [Sym2.eq_swap] using (hm v).1.2
  · intro v h
    exact (hm v).1.1.ne h.symm
  · intro v w
    exact ⟨(hm v).2 w, fun h => h.symm ▸ (hm v).1⟩

/-- The spanning path in this degree pattern necessarily has odd length.-/
theorem spanning_two_port_path_length_odd
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) (hxy : x ≠ y)
    (hspan : ∀ v, v ∈ p.support)
    (hdeg : ∀ v, G.degree v = if v = x ∨ v = y then 2 else 3) :
    Odd p.length := by
  have heven :=
    (spanning_two_port_path_complement_isPerfectMatching p hp hxy hspan hdeg).even_card
  have hcard : Fintype.card V = p.length + 1 := by
    have hfin : p.support.toFinset = Finset.univ := by
      ext v
      simp [hspan v]
    rw [← Finset.card_univ, ← hfin, List.toFinset_card_of_nodup hp.support_nodup,
      p.length_support]
  obtain ⟨k, hk⟩ := heven
  exact ⟨k - 1, by omega⟩

end Erdos64
