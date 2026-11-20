import Tengoku.Erdos64.Erdos64.TwoPortDefectBookkeeping
import Tengoku.Erdos64.Erdos64.RootDeletedNoDyadicTransfer
import Tengoku.Seed.Combinatorics.SimpleGraph.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Adding a missing terminal edge increases each terminal degree by one and
preserves every other degree.
@isnad1 id=eq.2h5v.s7.459db4de671d from=translated src=- shape=d1c03446 vocab=8c71402e
-/
theorem degree_sup_edge_of_not_adj
    {V : Type u} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    {a b : V} (hab : a ≠ b) (hnadj : ¬ K.Adj a b) (v : V) :
    (K ⊔ SimpleGraph.edge a b).degree v =
      K.degree v + if v = a ∨ v = b then 1 else 0 := by
  classical
  have hna : b ∉ K.neighborFinset a := by simpa using hnadj
  have hnb : a ∉ K.neighborFinset b := by
    simpa only [SimpleGraph.mem_neighborFinset] using (fun h => hnadj h.symm)
  by_cases hva : v = a
  · subst v
    have hfin : (K ⊔ SimpleGraph.edge a b).neighborFinset a =
        insert b (K.neighborFinset a) := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj,
        SimpleGraph.edge_adj, Finset.mem_insert]
      by_cases hw : w = b <;> simp [hw, hab, or_comm]
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hfin,
      Finset.card_insert_of_notMem hna, SimpleGraph.card_neighborFinset_eq_degree]
    simp
  · by_cases hvb : v = b
    · subst v
      have hfin : (K ⊔ SimpleGraph.edge a b).neighborFinset b =
          insert a (K.neighborFinset b) := by
        ext w
        simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj,
          SimpleGraph.edge_adj, Finset.mem_insert]
        by_cases hw : w = a <;> simp [hw, hab.symm, or_comm]
      rw [← SimpleGraph.card_neighborFinset_eq_degree, hfin,
        Finset.card_insert_of_notMem hnb, SimpleGraph.card_neighborFinset_eq_degree]
      simp
    · have hfin : (K ⊔ SimpleGraph.edge a b).neighborFinset v =
          K.neighborFinset v := by
        ext w
        simp [SimpleGraph.mem_neighborFinset,
          SimpleGraph.edge_adj, hva, hvb]
      rw [← SimpleGraph.card_neighborFinset_eq_degree, hfin,
        SimpleGraph.card_neighborFinset_eq_degree]
      simp [hva, hvb]

/-- Completing an exact nonadjacent two-port side by its missing terminal edge
repairs all lost root incidences. Each vertex recovers its ambient degree.
@isnad1 id=eq.7h7v.s9.db56f078725d from=translated src=- shape=6abe81cd vocab=74c01ce3
-/
theorem two_port_edge_completion_degree
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (D : Finset V) (r x y : V)
    (hr : r ∉ D) (hx : x ∈ D) (hy : y ∈ D)
    (hxy : x ≠ y) (hnadj : ¬ G.Adj x y)
    (hboundary : ∀ v, v ∈ D → ∀ w, w ∉ D → G.Adj v w → w = r)
    (hexact : ∀ v, v ∈ D → (G.Adj v r ↔ v = x ∨ v = y))
    (v : (↑D : Set V)) :
    ((G.induce (↑D : Set V)) ⊔ SimpleGraph.edge ⟨x, hx⟩ ⟨y, hy⟩).degree v =
      G.degree v.1 := by
  have hneq : (⟨x, hx⟩ : (↑D : Set V)) ≠ ⟨y, hy⟩ := by
    intro h
    exact hxy (congrArg Subtype.val h)
  have hn : ¬ (G.induce (↑D : Set V)).Adj ⟨x, hx⟩ ⟨y, hy⟩ := hnadj
  rw [degree_sup_edge_of_not_adj _ hneq hn,
    degree_induce_coeFinset_eq_internalDegree]
  have haccount := internalDegree_add_root_indicator_eq_degree D r hr hboundary v.2
  have hiff : (v = ⟨x, hx⟩ ∨ v = ⟨y, hy⟩) ↔ G.Adj v.1 r := by
    rw [hexact v.1 v.2]
    simp only [Subtype.ext_iff]
  simpa only [hiff] using haccount

/-- Vertex minimality forces a dyadic cycle in the smaller terminal-edge
completion. The synthetic edge is not yet removed in this degree lemma.
@isnad1 id=haspower.8h6v.s7.4c4330d402a8 from=translated src=- shape=2a0b2296 vocab=46d85f40
-/
theorem MinimalCounterexample.two_port_edge_completion_has_dyadic_cycle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (D : Finset V) (r x y : V)
    (hr : r ∉ D) (hx : x ∈ D) (hy : y ∈ D)
    (hxy : x ≠ y) (hnadj : ¬ G.Adj x y)
    (hboundary : ∀ v, v ∈ D → ∀ w, w ∉ D → G.Adj v w → w = r)
    (hexact : ∀ v, v ∈ D → (G.Adj v r ↔ v = x ∨ v = y)) :
    HasPowerOfTwoCycle
      ((G.induce (↑D : Set V)) ⊔ SimpleGraph.edge ⟨x, hx⟩ ⟨y, hy⟩) := by
  classical
  let H := (G.induce (↑D : Set V)) ⊔ SimpleGraph.edge ⟨x, hx⟩ ⟨y, hy⟩
  let : Nonempty (↑D : Set V) := ⟨⟨x, hx⟩⟩
  have hmin : H.minDegree ≥ 3 := by
    apply H.le_minDegree_of_forall_le_degree
    intro v
    rw [show H.degree v = G.degree v.1 from
      two_port_edge_completion_degree D r x y hr hx hy hxy hnadj
        hboundary hexact v]
    exact degree_ge_three_of_minDegree_ge_three G M.isCounterexample.1 v.1
  have hcard : Fintype.card (↑D : Set V) < Fintype.card V :=
    Fintype.card_subtype_lt hr
  by_contra hno
  exact M.not_exists_strictly_smaller (H := H) ⟨⟨hmin, hno⟩, hcard⟩

end Erdos64
