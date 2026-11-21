import Tengoku.Erdos64.Erdos64.HighDegreeAuxiliaryReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Cubic neighbors for which `r` is the unique high-degree neighbor.-/
def highDegreePrivateNeighbors (r : V) : Finset V :=
  (G.neighborFinset r).filter
    (fun v => G.degree v = 3 ∧ highDegreeNeighbors G v = {r})

variable {G}

/-- At a high-degree vertex, all neighbors split into private cubic neighbors
and the cubic connectors counted by its auxiliary degree.
@isnad1 id=eq.1h3v.s8.f4d14e5e13cf from=translated src=- shape=e79ff320 vocab=3d49f62c
-/
theorem EdgeMinimalCounterexample.highDegree_private_add_aux_degree
    (M : EdgeMinimalCounterexample G) (x : HighDegreeVertex G) :
    (highDegreePrivateNeighbors G x.1).card +
      (highDegreeAuxGraph G).degree x = G.degree x.1 := by
  classical
  let N := G.neighborFinset x.1
  have hconnect : N.filter (fun v => (highDegreeNeighbors G v).card = 2) =
      (degreeThreeTwoHighNeighbors G).filter (G.Adj x.1) := by
    ext v
    simp only [N, degreeThreeTwoHighNeighbors, Finset.mem_filter,
      Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hv, hc⟩
      exact ⟨⟨M.neighbor_degree_eq_three_of_degree_ge_four x.2 hv, hc⟩, hv⟩
    · rintro ⟨⟨_, hc⟩, hv⟩
      exact ⟨hv, hc⟩
  have hprivate : N.filter (fun v => ¬ (highDegreeNeighbors G v).card = 2) =
      highDegreePrivateNeighbors G x.1 := by
    ext v
    simp only [highDegreePrivateNeighbors, N, Finset.mem_filter,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hv, hc⟩
      have hv3 := M.neighbor_degree_eq_three_of_degree_ge_four x.2 hv
      refine ⟨hv, hv3, ?_⟩
      have hbound : (highDegreeNeighbors G v).card ≤ 2 :=
        M.high_degree_neighborFinset_card_le_two_of_degree_eq_three hv3
      have hxmem : x.1 ∈ highDegreeNeighbors G v := by
        simp [highDegreeNeighbors, x.2, hv.symm]
      exact (Finset.eq_of_subset_of_card_le
        (Finset.singleton_subset_iff.mpr hxmem) (by simp; omega)).symm
    · rintro ⟨hv, _, hc⟩
      exact ⟨hv, by simp [hc]⟩
  have hsum := Finset.card_filter_add_card_filter_not
    (s := N) (p := fun v => (highDegreeNeighbors G v).card = 2)
  rw [hconnect, hprivate, ← M.highDegreeAuxGraph_degree_eq_connector_count,
    show N.card = G.degree x.1 from G.card_neighborFinset_eq_degree x.1] at hsum
  omega

/-- If high-degree vertices exist, one has at least two cubic neighbors for
which it is the unique high-degree neighbor. In fact all but at most two of
its neighbors are private.
@isnad1 id=ex.2h2v.s7.1e680a67f0fa from=translated src=- shape=2be69a58 vocab=7c3fb11b
-/
theorem EdgeMinimalCounterexample.exists_highDegree_vertex_two_private_neighbors
    (M : EdgeMinimalCounterexample G)
    (hH : (Finset.univ.filter (fun v => 4 ≤ G.degree v)).Nonempty) :
    ∃ r : V, 4 ≤ G.degree r ∧
      G.degree r ≤ (highDegreePrivateNeighbors G r).card + 2 ∧
      2 ≤ (highDegreePrivateNeighbors G r).card := by
  classical
  obtain ⟨r, hr⟩ := hH
  let x : HighDegreeVertex G := ⟨r, (Finset.mem_filter.mp hr).2⟩
  have hS : (Finset.univ : Finset (HighDegreeVertex G)).Nonempty :=
    ⟨x, Finset.mem_univ x⟩
  obtain ⟨y, _, hy⟩ := M.highDegreeAuxGraph_low_internal_degree Finset.univ hS
  have hdegree : (highDegreeAuxGraph G).degree y ≤ 2 := by
    simpa [internalDegree, ← SimpleGraph.neighborFinset_eq_filter] using hy
  have hsum := M.highDegree_private_add_aux_degree y
  refine ⟨y.1, y.2, ?_, ?_⟩ <;> have := y.2 <;> omega

end Erdos64
