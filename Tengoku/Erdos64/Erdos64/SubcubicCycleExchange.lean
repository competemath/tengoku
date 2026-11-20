import Tengoku.Erdos64.Erdos64.Basic
import Tengoku.Seed.Combinatorics.SimpleGraph.Matching

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

open scoped Classical symmDiff

private theorem isCycles_neighborFinset_card_zero_or_two
    {V : Type u} [Fintype V] {H : SimpleGraph V}
    (hH : H.IsCycles) (v : V) :
    (H.neighborFinset v).card = 0 ∨ (H.neighborFinset v).card = 2 := by
  classical
  by_cases hnonempty : (H.neighborSet v).Nonempty
  · right
    simpa only [Set.ncard_eq_toFinset_card', ← SimpleGraph.neighborFinset_def] using
      hH hnonempty
  · left
    apply Finset.card_eq_zero.mpr
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
    exact fun hw => hnonempty ⟨w, hw⟩

/-- In a subcubic graph, the symmetric difference of two unions of cycles
is again a union of cycles, still contained in the ambient graph. The cycle
unions need not cover the same vertices. Connectedness of the result is not
asserted: an exchange may produce several disjoint cycles.-/
theorem subcubic_isCycles_symmDiff
    {V : Type u} [Fintype V] {G H K : SimpleGraph V} [DecidableRel G.Adj]
    (hHG : H ≤ G) (hKG : K ≤ G) (hH : H.IsCycles) (hK : K.IsCycles)
    (hdegree : ∀ v, G.degree v ≤ 3) :
    (H ∆ K).IsCycles ∧ H ∆ K ≤ G := by
  classical
  refine ⟨?_, symmDiff_le_sup.trans (sup_le hHG hKG)⟩
  intro v hnonempty
  let S := H.neighborFinset v
  let T := K.neighborFinset v
  have hS : S.card = 0 ∨ S.card = 2 :=
    isCycles_neighborFinset_card_zero_or_two hH v
  have hT : T.card = 0 ∨ T.card = 2 :=
    isCycles_neighborFinset_card_zero_or_two hK v
  have hunion : (S ∪ T).card ≤ 3 := by
    apply (Finset.card_le_card (show S ∪ T ⊆ G.neighborFinset v from ?_)).trans
      (hdegree v)
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · exact G.mem_neighborFinset v w |>.mpr (hHG (H.mem_neighborFinset v w |>.mp h))
    · exact G.mem_neighborFinset v w |>.mpr (hKG (K.mem_neighborFinset v w |>.mp h))
  have hsymm : (H ∆ K).neighborFinset v = S ∆ T := by
    ext w
    rw [SimpleGraph.mem_neighborFinset]
    simp [S, T, symmDiff_def]
  have hpos : 0 < (S ∆ T).card := by
    rw [← hsymm]
    exact Finset.card_pos.mpr ⟨hnonempty.choose,
      (H ∆ K).mem_neighborFinset v hnonempty.choose |>.mpr hnonempty.choose_spec⟩
  have hcounts := Finset.card_union_add_card_inter S T
  have hsubtract : (S ∆ T).card + (S ∩ T).card = (S ∪ T).card := by
    rw [symmDiff_eq_sup_sdiff_inf]
    exact Finset.card_sdiff_add_card_eq_card
      (Finset.inter_subset_left.trans Finset.subset_union_left)
  rw [Set.ncard_eq_toFinset_card', ← SimpleGraph.neighborFinset_def, hsymm]
  omega

/-- Only the union of the two cycle graphs needs to be subcubic. The ambient
graph may have larger degrees at vertices unused by their union.-/
theorem isCycles_symmDiff_of_sup_degree_le_three
    {V : Type u} [Fintype V] {H K : SimpleGraph V}
    (hH : H.IsCycles) (hK : K.IsCycles)
    (hdegree : ∀ v, (H ⊔ K).degree v ≤ 3) :
    (H ∆ K).IsCycles := by
  exact (subcubic_isCycles_symmDiff (G := H ⊔ K) (H := H) (K := K)
    le_sup_left le_sup_right hH hK hdegree).1

/-- Every nontrivial connected component of a subcubic cycle exchange is
the vertex set of an actual simple cycle. This permits inspecting exchange
components without assuming the entire exchange remains connected.-/
theorem subcubic_cycle_exchange_component
    {V : Type u} [Fintype V] {G H K : SimpleGraph V}
    (hHG : H ≤ G) (hKG : K ≤ G) (hH : H.IsCycles) (hK : K.IsCycles)
    (hdegree : ∀ v, G.degree v ≤ 3)
    {c : (H ∆ K).ConnectedComponent} {v : V}
    (hv : v ∈ c.supp) (hnonempty : ((H ∆ K).neighborSet v).Nonempty) :
    ∃ p : (H ∆ K).Walk v v, p.IsCycle ∧ p.toSubgraph.verts = c.supp := by
  exact SimpleGraph.IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (subcubic_isCycles_symmDiff hHG hKG hH hK hdegree).1 hv hnonempty

/-- Removing all edges of one simple cycle from a union of cycles leaves a
union of cycles. Every vertex on the removed cycle becomes isolated.-/
theorem isCycles_sdiff_cycle
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsCycles) {v : V} (p : G.Walk v v) (hp : p.IsCycle) :
    (G \ p.toSubgraph.spanningCoe).IsCycles := by
  classical
  intro x ⟨y, hxy⟩
  change G.Adj x y ∧ ¬p.toSubgraph.Adj x y at hxy
  have hx : x ∉ p.toSubgraph.verts := by
    intro hx
    exact hxy.2 ((hp.adj_toSubgraph_iff_of_isCycles hG hx y).mpr hxy.1)
  have heq : (G \ p.toSubgraph.spanningCoe).neighborSet x = G.neighborSet x := by
    ext z
    change (G.Adj x z ∧ ¬p.toSubgraph.Adj x z) ↔ G.Adj x z
    exact ⟨And.left, fun hxz => ⟨hxz, fun hc => hx (p.toSubgraph.edge_vert hc)⟩⟩
  rw [heq]
  exact hG ⟨y, hxy.1⟩

private theorem exists_cycle_of_isCycles_ne_bot
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsCycles) (hne : G ≠ ⊥) :
    ∃ v, ∃ p : G.Walk v v, p.IsCycle := by
  obtain ⟨v, w, hvw⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  obtain ⟨p, hp, _⟩ :=
    hG.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := G.connectedComponentMk v)
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem ⟨w, hvw⟩
  exact ⟨v, p, hp⟩

/-- An eight-edge union of cycles containing no triangle has a cycle of
length four or eight, hence a power-of-two cycle. This counts all exchange
components, rather than assuming that an eight-edge exchange is connected.-/
theorem hasPowerOfTwoCycle_of_isCycles_eight_edges_no_triangles
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsCycles) (hedges : G.edgeFinset.card = 8)
    (hno3 : ∀ {v : V} (p : G.Walk v v), p.IsCycle → p.length ≠ 3) :
    HasPowerOfTwoCycle G := by
  classical
  have hne : G ≠ ⊥ := by
    intro heq
    have hzero : G.edgeFinset.card = 0 := by
      exact Finset.card_eq_zero.mpr (SimpleGraph.edgeFinset_eq_empty.mpr heq)
    omega
  obtain ⟨v, p, hp⟩ := exists_cycle_of_isCycles_ne_bot hG hne
  by_cases hp4 : p.length = 4
  · exact ⟨2, v, p, by decide, hp, by simpa using hp4⟩
  have hp5 : 5 ≤ p.length := by
    have := hp.isCircuit.three_le_length
    have := hno3 p hp
    omega
  have hcycle_edges : p.toSubgraph.spanningCoe.edgeFinset = p.edges.toFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.Subgraph.edgeSet_spanningCoe,
      p.mem_edges_toSubgraph, List.mem_toFinset]
  have hcycle_card : p.toSubgraph.spanningCoe.edgeFinset.card = p.length := by
    rw [hcycle_edges, List.toFinset_card_of_nodup hp.isTrail.edges_nodup,
      SimpleGraph.Walk.length_edges]
  have hcounts : (G \ p.toSubgraph.spanningCoe).edgeFinset.card + p.length = 8 := by
    rw [SimpleGraph.edgeFinset_sdiff, ← hcycle_card, ← hedges]
    exact Finset.card_sdiff_add_card_eq_card
      (SimpleGraph.edgeFinset_mono p.toSubgraph.spanningCoe_le)
  have hrest : G \ p.toSubgraph.spanningCoe = ⊥ := by
    by_contra hrest
    obtain ⟨w, q, hq⟩ := exists_cycle_of_isCycles_ne_bot
      (isCycles_sdiff_cycle hG p hp) hrest
    have hq3 := hq.isCircuit.three_le_length
    have hqnot3 := hno3 (q.mapLe sdiff_le) (hq.mapLe sdiff_le)
    simp only [SimpleGraph.Walk.length_mapLe] at hqnot3
    have hqle := hq.isTrail.length_le_card_edgeFinset
    omega
  have hp8 : p.length = 8 := by
    have hzero : (G \ p.toSubgraph.spanningCoe).edgeFinset.card = 0 :=
      Finset.card_eq_zero.mpr (SimpleGraph.edgeFinset_eq_empty.mpr hrest)
    omega
  exact ⟨3, v, p, by decide, hp, by simpa using hp8⟩

/-- An eight-edge exchange between cycle unions forces a dyadic cycle when
the union is subcubic and the exchanged edges contain no triangle. The
ambient graph need not itself be subcubic or triangle-free.-/
theorem hasPowerOfTwoCycle_of_eight_edge_cycle_exchange
    {V : Type u} [Fintype V] {G H K : SimpleGraph V}
    (hHG : H ≤ G) (hKG : K ≤ G) (hH : H.IsCycles) (hK : K.IsCycles)
    (hdegree : ∀ v, (H ⊔ K).degree v ≤ 3)
    (hedges : (H ∆ K).edgeFinset.card = 8)
    (hno3 : ∀ {v : V} (p : (H ∆ K).Walk v v), p.IsCycle → p.length ≠ 3) :
    HasPowerOfTwoCycle G := by
  have hcycles := isCycles_symmDiff_of_sup_degree_le_three hH hK hdegree
  obtain ⟨k, v, p, hk, hp, hlen⟩ :=
    hasPowerOfTwoCycle_of_isCycles_eight_edges_no_triangles hcycles hedges hno3
  have hle : H ∆ K ≤ G := symmDiff_le_sup.trans (sup_le hHG hKG)
  exact ⟨k, v, p.mapLe hle, hk, hp.mapLe hle,
    by simpa only [SimpleGraph.Walk.length_mapLe] using hlen⟩

end Erdos64
