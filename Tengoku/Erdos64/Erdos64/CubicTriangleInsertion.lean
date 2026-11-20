import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Distinct vertices have at most one common neighbor in a graph with no
four-cycle. This uses no degree or minimal-counterexample assumption.-/
theorem common_neighbor_eq_of_no_four_cycle
    {V : Type u} {G : SimpleGraph V}
    (hfour : ∀ v (c : G.Walk v v), c.IsCycle → c.length ≠ 4)
    {a b u v : V} (hab : a ≠ b)
    (hau : G.Adj a u) (hav : G.Adj a v)
    (hbu : G.Adj b u) (hbv : G.Adj b v) : u = v := by
  by_contra huv
  let q : G.Walk u v := .cons hau.symm (.cons hav .nil)
  have hq : q.IsPath := by
    apply SimpleGraph.Walk.IsPath.cons (SimpleGraph.Walk.IsPath.of_adj hav)
    simp [hau.ne.symm, huv]
  have hb : b ∉ q.support := by
    simp [q, hbu.ne, hbv.ne, hab.symm]
  obtain ⟨c, hc, hlen⟩ := endpoint_fan_cycle_certificate hq hbu hbv hb huv (by simp [q])
  exact hfour u c hc (by simpa [q] using hlen)

/-- At a vertex of degree at most three in a graph with no four-cycle,
there is at most one edge between its neighbors. Thus it lies in at most
one triangle. The degree bound matters: two triangles may share a vertex
of degree four without creating a four-cycle.-/
theorem neighbor_edge_unique_of_degree_le_three
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hfour : ∀ v (c : G.Walk v v), c.IsCycle → c.length ≠ 4)
    {u a b c d : V} (hdegree : G.degree u ≤ 3)
    (hua : G.Adj u a) (hub : G.Adj u b)
    (huc : G.Adj u c) (hud : G.Adj u d)
    (hab : G.Adj a b) (hcd : G.Adj c d) : s(a, b) = s(c, d) := by
  by_cases hac : a = c
  · subst c
    have hbd := common_neighbor_eq_of_no_four_cycle hfour hua.ne hub hud hab hcd
    exact Sym2.eq_iff.mpr (Or.inl ⟨rfl, hbd⟩)
  by_cases had : a = d
  · subst d
    have hbc := common_neighbor_eq_of_no_four_cycle hfour hua.ne hub huc hab hcd.symm
    exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, hbc⟩)
  by_cases hbc : b = c
  · subst c
    have had := common_neighbor_eq_of_no_four_cycle hfour hub.ne hua hud hab.symm hcd
    exact Sym2.eq_iff.mpr (Or.inr ⟨had, rfl⟩)
  by_cases hbd : b = d
  · subst d
    have hac := common_neighbor_eq_of_no_four_cycle hfour hub.ne hua huc hab.symm hcd.symm
    exact Sym2.eq_iff.mpr (Or.inl ⟨hac, rfl⟩)
  have hsub : ({a, b, c, d} : Finset V) ⊆ G.neighborFinset u := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl <;>
      exact (G.mem_neighborFinset _ _).mpr (by assumption)
  have hcard : ({a, b, c, d} : Finset V).card = 4 := by
    simp [hab.ne, hac, had, hbc, hbd, hcd.ne]
  have hle := Finset.card_le_card hsub
  rw [hcard, SimpleGraph.card_neighborFinset_eq_degree] at hle
  omega

/-- There is at most one position at which a vertex of degree at most three
can be inserted into a simple path in a graph with no four-cycle. A valid
position means that both endpoints of that consecutive path edge are
neighbors of the inserted vertex.-/
theorem path_triangle_insertion_index_unique
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hfour : ∀ v (c : G.Walk v v), c.IsCycle → c.length ≠ 4)
    {x y u : V} (p : G.Walk x y) (hp : p.IsPath)
    (hdegree : G.degree u ≤ 3) {i j : ℕ}
    (hi : i < p.length) (hj : j < p.length)
    (hui : G.Adj u (p.getVert i)) (hui' : G.Adj u (p.getVert (i + 1)))
    (huj : G.Adj u (p.getVert j)) (huj' : G.Adj u (p.getVert (j + 1))) :
    i = j := by
  have he := neighbor_edge_unique_of_degree_le_three hfour hdegree
    hui hui' huj huj' (p.adj_getVert_succ hi) (p.adj_getVert_succ hj)
  rcases Sym2.eq_iff.mp he with h | h
  · exact hp.getVert_injOn (by change i ≤ p.length; omega)
      (by change j ≤ p.length; omega) h.1
  · have h₁ := hp.getVert_injOn (by change i ≤ p.length; omega)
      (by change j + 1 ≤ p.length; omega) h.1
    have h₂ := hp.getVert_injOn (by change i + 1 ≤ p.length; omega)
      (by change j ≤ p.length; omega) h.2
    omega

/-- The unique-insertion restriction applies to cubic vertices of any
minimal counterexample. It is a restriction on possible moves, not an
existence theorem for a move or a contradiction.-/
theorem MinimalCounterexample.cubic_path_triangle_insertion_index_unique
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) {x y u : V}
    (p : G.Walk x y) (hp : p.IsPath) (hcubic : G.degree u = 3)
    {i j : ℕ} (hi : i < p.length) (hj : j < p.length)
    (hui : G.Adj u (p.getVert i)) (hui' : G.Adj u (p.getVert (i + 1)))
    (huj : G.Adj u (p.getVert j)) (huj' : G.Adj u (p.getVert (j + 1))) :
    i = j := by
  apply path_triangle_insertion_index_unique (p := p) (hp := hp) ?_
    (by omega : G.degree u ≤ 3) hi hj hui hui' huj huj'
  intro v c hc hlen
  exact M.isCounterexample.2 ⟨2, v, c, by omega, hc, by simpa using hlen⟩

end Erdos64
