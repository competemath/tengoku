import Tengoku.Erdos64.Erdos64.RootedBranches

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

open SimpleGraph

/-- A boundary carrier retains minimum degree three when every port to its
    external root has ambient degree at least four.
@isnad1 id=le.4h4v.s8.47afae48dc66 from=translated src=- shape=6660622f vocab=251b8fc6
-/
theorem induced_minDegree_ge_three_of_high_degree_ports
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (K : Finset V) (r : V) (hK : K.Nonempty)
    (hboundary : ∀ v, v ∈ K → ∀ w, w ∉ K → G.Adj v w → w = r)
    (hmin : G.minDegree ≥ 3)
    (hports : ∀ v, v ∈ K → G.Adj v r → 4 ≤ G.degree v) :
    (G.induce (↑K : Set V)).minDegree ≥ 3 := by
  classical
  letI : Nonempty (↑K : Set V) := by
    obtain ⟨v, hv⟩ := hK
    exact ⟨⟨v, hv⟩⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
    (G := G.induce (↑K : Set V)) 3
  intro v
  rw [degree_induce_coeFinset_eq_internalDegree G v]
  have hvK : v.1 ∈ K := v.2
  have hvdeg : 3 ≤ G.degree v.1 :=
    degree_ge_three_of_minDegree_ge_three G hmin v.1
  by_cases hvr : G.Adj v.1 r
  · by_cases hrK : r ∈ K
    · have hfilter : K.filter (G.Adj v.1) = G.neighborFinset v.1 := by
        ext w
        constructor
        · intro hw
          exact (G.mem_neighborFinset v.1 w).2
            (Finset.mem_filter.mp hw).2
        · intro hw
          have hAdj : G.Adj v.1 w := (G.mem_neighborFinset v.1 w).1 hw
          refine Finset.mem_filter.mpr ⟨?_, hAdj⟩
          by_contra hwK
          have hwr : w = r := hboundary v.1 hvK w hwK hAdj
          exact hwK (hwr ▸ hrK)
      rw [internalDegree, hfilter]
      exact hvdeg
    · have hunion :
          K.filter (G.Adj v.1) ∪ ({r} : Finset V) = G.neighborFinset v.1 := by
        ext w
        constructor
        · intro hw
          rcases Finset.mem_union.mp hw with hw | hw
          · exact (G.mem_neighborFinset v.1 w).2
              (Finset.mem_filter.mp hw).2
          · have hwr : w = r := Finset.mem_singleton.mp hw
            exact (G.mem_neighborFinset v.1 w).2 (hwr ▸ hvr)
        · intro hw
          have hAdj : G.Adj v.1 w := (G.mem_neighborFinset v.1 w).1 hw
          by_cases hwK : w ∈ K
          · exact Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨hwK, hAdj⟩)
          · exact Finset.mem_union.mpr <| Or.inr <|
              Finset.mem_singleton.mpr (hboundary v.1 hvK w hwK hAdj)
      have hdisjoint :
          Disjoint (K.filter (G.Adj v.1)) ({r} : Finset V) := by
        apply Finset.disjoint_left.2
        intro w hwK hwr
        have hwmem : w ∈ K := (Finset.mem_filter.mp hwK).1
        exact hrK (Finset.mem_singleton.mp hwr ▸ hwmem)
      have hcard := congrArg Finset.card hunion
      rw [Finset.card_union_of_disjoint hdisjoint,
        Finset.card_singleton, SimpleGraph.card_neighborFinset_eq_degree]
        at hcard
      have hcard' : internalDegree G K v.1 + 1 = G.degree v.1 := by
        simpa only [internalDegree] using hcard
      have hvdeg4 : 4 ≤ G.degree v.1 := hports v.1 hvK hvr
      rw [internalDegree]
      omega
  · have hfilter : K.filter (G.Adj v.1) = G.neighborFinset v.1 := by
      ext w
      constructor
      · intro hw
        exact (G.mem_neighborFinset v.1 w).2
          (Finset.mem_filter.mp hw).2
      · intro hw
        have hAdj : G.Adj v.1 w := (G.mem_neighborFinset v.1 w).1 hw
        refine Finset.mem_filter.mpr ⟨?_, hAdj⟩
        by_contra hwK
        have hwr : w = r := hboundary v.1 hvK w hwK hAdj
        exact hvr (hwr ▸ hAdj)
    rw [internalDegree, hfilter]
    exact hvdeg

end Erdos64
