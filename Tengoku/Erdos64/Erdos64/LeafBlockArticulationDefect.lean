import Tengoku.Erdos64.Erdos64.LeafBlocks

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A proper finite leaf block with a single articulation boundary cannot have
    minimum internal degree three at its articulation vertex in a
    subgraph-critical graph.  The closure premise is deliberately stated for
    every non-root carrier vertex, so the conclusion records the actual
    defect at `root` rather than an abstract carrier existence claim.
@isnad1 id=le.7h4v.s7.d5895a6aa8eb from=translated src=- shape=310b39f2 vocab=aaa21096
-/
theorem leafBlock_articulation_internalDegree_le_two
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (K : Finset V) (root : V)
    (hKconn : (G.induce (↑K : Set V)).Connected)
    (hKnonempty : K.Nonempty)
    (hKproper : K ≠ (Finset.univ : Finset V))
    (hroot : root ∈ K)
    (hboundary :
      ∀ x, x ∈ K → ∀ y, y ∉ K → G.Adj x y → x = root)
    (hclosed : ∀ v, v ∈ K → v ≠ root → 3 ≤ G.degree v)
    (hcritical : IsSubgraphCritical G) :
    internalDegree G K root ≤ 2 := by
  obtain ⟨v, hv, hvlow⟩ := hcritical K hKnonempty hKproper
  by_cases hvr : v = root
  · simpa only [hvr] using hvlow
  · have hvdeg : 3 ≤ G.degree v := hclosed v hv hvr
    have hneighbors : ∀ w, G.Adj v w → w ∈ K := by
      intro w hvw
      by_contra hwK
      exact hvr (hboundary v hv w hwK hvw)
    have hfilter : K.filter (G.Adj v) = G.neighborFinset v := by
      ext w
      rw [Finset.mem_filter]
      constructor
      · intro hw
        exact (G.mem_neighborFinset v w).2 hw.2
      · intro hw
        have hvw : G.Adj v w := (G.mem_neighborFinset v w).1 hw
        exact ⟨hneighbors w hvw, hvw⟩
    have hvinternal : internalDegree G K v = G.degree v := by
      change (K.filter (G.Adj v)).card = G.degree v
      rw [hfilter]
      exact SimpleGraph.card_neighborFinset_eq_degree G v
    rw [hvinternal] at hvlow
    omega

end Erdos64
