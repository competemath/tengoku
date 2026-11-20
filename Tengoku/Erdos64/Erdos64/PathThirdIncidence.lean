import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A simple path uses at most one incidence at its first vertex and at
most two at any other vertex.-/
theorem path_incident_neighbors_card_le
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b : V} (p : G.Walk a b) (hp : p.IsPath) (v : V) :
    (Finset.univ.filter (fun w => s(v, w) ∈ p.edges)).card ≤
      if v = a then 1 else 2 := by
  classical
  induction p generalizing v with
  | nil => simp
  | @cons a b c hab p ih =>
    have hp' := (SimpleGraph.Walk.cons_isPath_iff hab p).mp hp
    by_cases hva : v = a
    · subst v
      have hfilter :
          Finset.univ.filter (fun w => s(a, w) ∈ (p.cons hab).edges) = {b} := by
        ext w
        have htail : s(a, w) ∉ p.edges := by
          intro hw
          exact hp'.2 (p.fst_mem_support_of_mem_edges hw)
        simp [SimpleGraph.Walk.edges_cons, htail, hab.ne]
      rw [hfilter]
      simp
    · by_cases hvb : v = b
      · subst v
        have hsub :
            Finset.univ.filter (fun w => s(b, w) ∈ (p.cons hab).edges) ⊆
              insert a (Finset.univ.filter (fun w => s(b, w) ∈ p.edges)) := by
          intro w hw
          have hm : s(b, w) = s(a, b) ∨ s(b, w) ∈ p.edges := by
            simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
              SimpleGraph.Walk.edges_cons, List.mem_cons] using hw
          rcases hm with heq | he
          · have hwa : w = a := by
              rcases Sym2.eq_iff.mp heq with h | h
              · exact (hab.ne h.1.symm).elim
              · exact h.2
            exact Finset.mem_insert.mpr (Or.inl hwa)
          · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, he⟩))
        have hle := (Finset.card_le_card hsub).trans
          (Finset.card_insert_le _ _)
        have htail := ih hp'.1 b
        simp only [ite_true] at htail
        simp only [ite_eq_right hva]
        omega
      · have hfilter :
            Finset.univ.filter (fun w => s(v, w) ∈ (p.cons hab).edges) =
              Finset.univ.filter (fun w => s(v, w) ∈ p.edges) := by
          ext w
          simp [SimpleGraph.Walk.edges_cons, hva, hvb]
        rw [hfilter]
        simpa [hva, hvb] using ih hp'.1 v

/-- At most two neighbors can be joined to a fixed vertex by edges of a
simple path. This also applies to vertices outside the path.-/
theorem path_incident_neighbors_card_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b : V} (p : G.Walk a b) (hp : p.IsPath) (v : V) :
    (Finset.univ.filter (fun w => s(v, w) ∈ p.edges)).card ≤ 2 := by
  have h := path_incident_neighbors_card_le p hp v
  split_ifs at h <;> omega

/-- A vertex of degree at least three has an incident edge unused by any
specified simple path.-/
theorem exists_adj_not_mem_path_edges
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b v : V}
    (p : G.Walk a b) (hp : p.IsPath) (hdegree : 3 ≤ G.degree v) :
    ∃ w, G.Adj v w ∧ s(v, w) ∉ p.edges := by
  classical
  by_contra h
  have hused : ∀ w, G.Adj v w → s(v, w) ∈ p.edges := by
    intro w hvw
    by_contra hnot
    exact h ⟨w, hvw, hnot⟩
  have hsub : G.neighborFinset v ⊆
      Finset.univ.filter (fun w => s(v, w) ∈ p.edges) := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hused w ((G.mem_neighborFinset v w).mp hw)⟩
  have hle := (Finset.card_le_card hsub).trans
    (path_incident_neighbors_card_le_two p hp v)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hle
  omega

end Erdos64
