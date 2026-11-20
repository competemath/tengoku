import Tengoku.Erdos64.Erdos64.SharedRootQuotientResidual
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

open scoped BigOperators

/-- Counting incidences from high-degree vertices more sharply: only cubic
vertices with two high-degree neighbors contribute more than one incidence.
@isnad1 id=other.1h2v.s7.db4818b26ce7 from=translated src=- shape=a56de04e vocab=b91c6d58
-/
theorem EdgeMinimalCounterexample.high_degree_incidence_le_cubic_plus_connectors
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : EdgeMinimalCounterexample G) :
    let H := Finset.univ.filter (fun v => 4 ≤ G.degree v)
    let L := Finset.univ.filter (fun v => G.degree v = 3)
    4 * H.card ≤ L.card +
      (L.filter (fun v => (H.filter (G.Adj v)).card = 2)).card := by
  classical
  dsimp only
  let H := Finset.univ.filter (fun v => 4 ≤ G.degree v)
  let L := Finset.univ.filter (fun v => G.degree v = 3)
  change 4 * H.card ≤ L.card +
    (L.filter (fun v => (H.filter (G.Adj v)).card = 2)).card
  have hleft : 4 * H.card ≤ ∑ u ∈ H, (L.filter (G.Adj u)).card := by
    calc
      4 * H.card = ∑ _u ∈ H, 4 := by simp [Nat.mul_comm]
      _ ≤ ∑ u ∈ H, (L.filter (G.Adj u)).card := by
        apply Finset.sum_le_sum
        intro u hu
        have hu4 : 4 ≤ G.degree u := (Finset.mem_filter.mp hu).2
        have hfin : L.filter (G.Adj u) = G.neighborFinset u := by
          ext v
          simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
          constructor
          · exact fun h => h.2
          · intro huv
            refine ⟨?_, huv⟩
            simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
            exact M.neighbor_degree_eq_three_of_degree_ge_four hu4 huv
        simpa only [hfin, SimpleGraph.card_neighborFinset_eq_degree] using hu4
  have hdouble : (∑ u ∈ H, (L.filter (G.Adj u)).card) =
      ∑ v ∈ L, (H.filter (G.Adj v)).card := by
    simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow, G.adj_comm] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj
        (s := H) (t := L))
  have hright : (∑ v ∈ L, (H.filter (G.Adj v)).card) ≤
      L.card + (L.filter (fun v => (H.filter (G.Adj v)).card = 2)).card := by
    calc
      (∑ v ∈ L, (H.filter (G.Adj v)).card) ≤
          ∑ v ∈ L, (1 + if (H.filter (G.Adj v)).card = 2 then 1 else 0) := by
        apply Finset.sum_le_sum
        intro v hv
        have hv3 : G.degree v = 3 := (Finset.mem_filter.mp hv).2
        have hb : (H.filter (G.Adj v)).card ≤ 2 :=
          M.high_degree_neighborFinset_card_le_two_of_degree_eq_three hv3
        split <;> omega
      _ = _ := by simp [Finset.sum_add_distrib]
  exact hleft.trans (hdouble ▸ hright)

/-- The cubic and high-degree carriers partition a graph of minimum degree
at least three.
@isnad1 id=eq.1h2v.s7.c107e1bed368 from=translated src=- shape=3c1b41ab vocab=0f6782a5
-/
theorem EdgeMinimalCounterexample.card_eq_cubic_add_high
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : EdgeMinimalCounterexample G) :
    Fintype.card V =
      (Finset.univ.filter (fun v => G.degree v = 3)).card +
      (Finset.univ.filter (fun v => 4 ≤ G.degree v)).card := by
  classical
  let L := Finset.univ.filter (fun v => G.degree v = 3)
  let H := Finset.univ.filter (fun v => 4 ≤ G.degree v)
  have hpartition : L ∪ H = Finset.univ := by
    ext v
    have hv := degree_ge_three_of_minDegree_ge_three G M.vertexMinimal.isCounterexample.1 v
    simp only [L, H, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro _
      trivial
    · intro _
      by_cases hv3 : G.degree v = 3
      · exact Or.inl hv3
      · exact Or.inr (by omega)
  have hdisjoint : Disjoint L H := by
    refine Finset.disjoint_left.2 ?_
    intro v hvL hvH
    have hv3 := (Finset.mem_filter.mp hvL).2
    have hv4 := (Finset.mem_filter.mp hvH).2
    omega
  simpa only [hpartition, Finset.card_univ] using
    (Finset.card_union_of_disjoint hdisjoint)

/-- The connector edge bound strengthens the cubic-density estimate by an
additive three in its integer form.
@isnad1 id=and.1h3v.s9.4423f133d1fa from=translated src=- shape=78c6ace9 vocab=243ef307
-/
theorem EdgeMinimalCounterexample.cubic_density_of_connector_bound
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : EdgeMinimalCounterexample G)
    (hconnectors :
      let H := Finset.univ.filter (fun v => 4 ≤ G.degree v)
      let L := Finset.univ.filter (fun v => G.degree v = 3)
      (L.filter (fun v => (H.filter (G.Adj v)).card = 2)).card + 3 ≤
        2 * H.card) :
    2 * (Finset.univ.filter (fun v => 4 ≤ G.degree v)).card + 3 ≤
      (Finset.univ.filter (fun v => G.degree v = 3)).card ∧
    2 * Fintype.card V + 3 ≤
      3 * (Finset.univ.filter (fun v => G.degree v = 3)).card := by
  have hinc := M.high_degree_incidence_le_cubic_plus_connectors
  have hpart := M.card_eq_cubic_add_high
  dsimp only at hinc hconnectors
  omega

/-- A high-degree vertex cannot occur in a counterexample on at most five
vertices: it would be universal, and two neighbors of one of its cubic
neighbors would give a four-cycle.
@isnad1 id=le.2h3v.s6.17fdb690ab3a from=translated src=- shape=6ed00493 vocab=bffb8b90
-/
theorem EdgeMinimalCounterexample.six_le_card_of_degree_ge_four
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : EdgeMinimalCounterexample G)
    {r : V} (hr : 4 ≤ G.degree r) :
    6 ≤ Fintype.card V := by
  classical
  by_contra hn
  have hsmall : Fintype.card V ≤ 5 := by omega
  have hsub : G.neighborFinset r ⊆ Finset.univ.erase r := by
    intro v hv
    have hrv := (G.mem_neighborFinset r v).mp hv
    exact Finset.mem_erase.mpr ⟨hrv.ne.symm, Finset.mem_univ v⟩
  have hN : G.neighborFinset r = Finset.univ.erase r := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ,
      SimpleGraph.card_neighborFinset_eq_degree]
    omega
  have hnonempty : (G.neighborFinset r).Nonempty := by
    rw [← Finset.card_pos, SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨v, hv⟩ := hnonempty
  have hrv := (G.mem_neighborFinset r v).mp hv
  have hv3 := M.neighbor_degree_eq_three_of_degree_ge_four hr hrv
  obtain ⟨x, y, hxy, hvx, hvy, hxr, hyr⟩ :=
    exists_two_other_neighbors_of_degree_three hrv hv3
  have hrx : G.Adj r x := by
    apply (G.mem_neighborFinset r x).mp
    rw [hN]
    simp [hxr]
  have hry : G.Adj r y := by
    apply (G.mem_neighborFinset r y).mp
    rw [hN]
    simp [hyr]
  have hvr := M.vertexMinimal.common_neighbor_eq_root_of_nonadjacent_ports
    hrx hry hxy hvx.symm hvy.symm hvx.ne hvy.ne
  exact hrv.ne hvr.symm

/-- The sharp cubic-density conclusion requires the connector bound only
when there are at least two high-degree vertices.  The remaining two cases
follow from the degree condition and the exclusion of four-cycles.
@isnad1 id=and.1h3v.s9.3949deaa36a5 from=translated src=- shape=58246b84 vocab=243ef307
-/
theorem EdgeMinimalCounterexample.cubic_density_of_conditional_connector_bound
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : EdgeMinimalCounterexample G)
    (hconnectors :
      let H := Finset.univ.filter (fun v => 4 ≤ G.degree v)
      let L := Finset.univ.filter (fun v => G.degree v = 3)
      2 ≤ H.card →
        (L.filter (fun v => (H.filter (G.Adj v)).card = 2)).card + 3 ≤
          2 * H.card) :
    2 * (Finset.univ.filter (fun v => 4 ≤ G.degree v)).card + 3 ≤
      (Finset.univ.filter (fun v => G.degree v = 3)).card ∧
    2 * Fintype.card V + 3 ≤
      3 * (Finset.univ.filter (fun v => G.degree v = 3)).card := by
  classical
  let H := Finset.univ.filter (fun v => 4 ≤ G.degree v)
  by_cases htwo : 2 ≤ H.card
  · exact M.cubic_density_of_connector_bound (hconnectors htwo)
  have hpart := M.card_eq_cubic_add_high
  have hfour : 4 ≤ Fintype.card V := by
    obtain ⟨v, hv⟩ := M.exists_degree_eq_three
    have hv3 := (Finset.mem_filter.mp hv).2
    have hvcard := G.degree_lt_card_verts v
    omega
  by_cases hzero : H.card = 0
  · change 2 * H.card + 3 ≤ _ ∧ _
    change Fintype.card V = _ + H.card at hpart
    omega
  have hnonempty : H.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨r, hr⟩ := hnonempty
  have hr4 : 4 ≤ G.degree r := (Finset.mem_filter.mp hr).2
  have hsix := M.six_le_card_of_degree_ge_four hr4
  change 2 * H.card + 3 ≤ _ ∧ _
  change Fintype.card V = _ + H.card at hpart
  omega

end Erdos64
