import Tengoku.Erdos64.Erdos64.TwoPortEdgeCompletion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Suppress `x` by replacing its two incidences with an edge between the
retained vertices `a` and `b`. The degree hypotheses belong to the lemmas.-/
def degreeTwoSuppressionGraph {V : Type u} (G : SimpleGraph V)
    (x a b : V) (hax : a ≠ x) (hbx : b ≠ x) :
    SimpleGraph {v : V // v ≠ x} :=
  (G.induce {v : V | v ≠ x}) ⊔ SimpleGraph.edge ⟨a, hax⟩ ⟨b, hbx⟩

instance degreeTwoSuppressionGraph_decidableRel
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    [DecidableRel G.Adj] {x a b : V} {hax : a ≠ x} {hbx : b ≠ x} :
    DecidableRel (degreeTwoSuppressionGraph G x a b hax hbx).Adj :=
  inferInstanceAs (DecidableRel
    ((G.induce {v : V | v ≠ x}) ⊔ SimpleGraph.edge ⟨a, hax⟩ ⟨b, hbx⟩).Adj)

/-- Deleting one vertex removes exactly its possible incidence from the
degree of each surviving vertex.-/
theorem degree_induce_ne_vertex_add_indicator
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) (v : {v : V // v ≠ x}) :
    (G.induce {w : V | w ≠ x}).degree v +
      (if G.Adj v.1 x then 1 else 0) = G.degree v.1 := by
  classical
  have hfin :
      ((G.induce {w : V | w ≠ x}).neighborFinset v).map
        (.subtype (fun w : V => w ≠ x)) = (G.neighborFinset v.1).erase x := by
    ext w
    simp [SimpleGraph.neighborFinset_eq_filter, and_comm]
  have hdeg : (G.induce {w : V | w ≠ x}).degree v =
      ((G.neighborFinset v.1).erase x).card := by
    rw [← hfin, Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree]
  rw [hdeg, ← SimpleGraph.card_neighborFinset_eq_degree]
  by_cases hadj : G.Adj v.1 x
  · simpa [hadj] using
      Finset.card_erase_add_one ((G.mem_neighborFinset v.1 x).2 hadj)
  · simp [hadj]

/-- Suppression of a vertex with exactly two distinct, nonadjacent neighbors
preserves the degree of every surviving vertex.-/
theorem degreeTwoSuppressionGraph_degree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x a b : V) (hax : a ≠ x) (hbx : b ≠ x)
    (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    (hneighbors : ∀ w, G.Adj x w ↔ w = a ∨ w = b)
    (v : {v : V // v ≠ x}) :
    (degreeTwoSuppressionGraph G x a b hax hbx).degree v = G.degree v.1 := by
  classical
  have hab' : (⟨a, hax⟩ : {v : V // v ≠ x}) ≠ ⟨b, hbx⟩ := by
    intro h
    exact hab (congrArg Subtype.val h)
  change ((G.induce {w : V | w ≠ x}) ⊔
    SimpleGraph.edge ⟨a, hax⟩ ⟨b, hbx⟩).degree v = G.degree v.1
  rw [degree_sup_edge_of_not_adj _ hab' hnadj]
  have hiff : (v = ⟨a, hax⟩ ∨ v = ⟨b, hbx⟩) ↔ G.Adj v.1 x := by
    rw [G.adj_comm, hneighbors]
    simp only [Subtype.ext_iff]
  simpa only [hiff] using degree_induce_ne_vertex_add_indicator G x v

/-- The surviving vertex set has exactly one fewer vertex.-/
theorem card_ne_vertex_add_one
    {V : Type u} [Fintype V] [DecidableEq V] (x : V) :
    Fintype.card {v : V // v ≠ x} + 1 = Fintype.card V := by
  have hpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
  simp only [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  omega

end Erdos64
