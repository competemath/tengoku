import Tengoku.Erdos64.Erdos64.RootedBranches

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A finite carrier whose only possible boundary vertex is `r` has the same
    ambient and induced degrees at vertices with no edge to `r`.
@isnad1 id=eq.3h5v.s7.e83c5eed2c8f from=translated src=- shape=bc5ecc3f vocab=dc2dd195
-/
theorem internalDegree_eq_degree_of_boundary_root_of_no_root_neighbor
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (K : Finset V) (r : V)
    (hboundary : ∀ v, v ∈ K → ∀ w, w ∉ K → G.Adj v w → w = r)
    (hnoroot : ∀ v, v ∈ K → ¬ G.Adj v r)
    {v : V} (hv : v ∈ K) :
    internalDegree G K v = G.degree v := by
  classical
  have hfilter : K.filter (G.Adj v) = G.neighborFinset v := by
    ext w
    constructor
    · intro hw
      exact (G.mem_neighborFinset v w).2 (Finset.mem_filter.mp hw).2
    · intro hw
      have hvw : G.Adj v w := (G.mem_neighborFinset v w).1 hw
      refine Finset.mem_filter.mpr ⟨?_, hvw⟩
      by_contra hwK
      have hwr : w = r := hboundary v hv w hwK hvw
      subst w
      exact (hnoroot v hv) hvw
  change (K.filter (G.Adj v)).card = G.degree v
  rw [hfilter]
  exact SimpleGraph.card_neighborFinset_eq_degree G v

/-- A nonempty component with no edge to its external root retains ambient
    minimum degree at least three after induction. This is only a degree
    transport lemma; it makes no criticality or dyadic-cycle assertion.
@isnad1 id=le.4h4v.s8.c0f0f05fb2fb from=translated src=- shape=bccd7c87 vocab=25bba2a8
-/
theorem induced_minDegree_ge_three_of_boundary_root_of_no_root_neighbor
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (K : Finset V) (r : V) (hK : K.Nonempty)
    (hboundary : ∀ v, v ∈ K → ∀ w, w ∉ K → G.Adj v w → w = r)
    (hnoroot : ∀ v, v ∈ K → ¬ G.Adj v r)
    (hmin : G.minDegree ≥ 3) :
    (G.induce (↑K : Set V)).minDegree ≥ 3 := by
  classical
  letI : Nonempty (↑K : Set V) := by
    obtain ⟨v, hv⟩ := hK
    exact ⟨⟨v, hv⟩⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
    (G := G.induce (↑K : Set V)) 3
  intro v
  rw [degree_induce_coeFinset_eq_internalDegree G v]
  rw [internalDegree_eq_degree_of_boundary_root_of_no_root_neighbor
    K r hboundary hnoroot v.2]
  exact degree_ge_three_of_minDegree_ge_three G hmin v.1

end Erdos64
