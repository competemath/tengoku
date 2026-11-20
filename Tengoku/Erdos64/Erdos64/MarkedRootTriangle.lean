import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

namespace SimpleGraph

namespace Walk

variable {V : Type u} {G : SimpleGraph V}

/-- Three original adjacency hypotheses give the corresponding simple triangle.-/
theorem exists_triangle_of_marked_root_adjacencies
    {r a b : V}
    (hra : G.Adj r a)
    (hrb : G.Adj r b)
    (hab : G.Adj a b) :
    ∃ c : G.Walk a a, c.IsCycle ∧ c.length = 3 := by
  let q : G.Walk b a :=
    SimpleGraph.Walk.cons hrb.symm
      (SimpleGraph.Walk.cons hra SimpleGraph.Walk.nil)
  have hq : q.IsPath := by
    dsimp [q]
    refine (SimpleGraph.Walk.cons_isPath_iff _ _).2 ⟨?_, ?_⟩
    · exact
        (SimpleGraph.Walk.cons_isPath_iff _ _).2
          ⟨SimpleGraph.Walk.IsPath.nil, by simp [hra.ne]⟩
    · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons]
      intro hba
      rcases hba with hba | hba
      · exact (hrb.ne.symm hba).elim
      · rcases hba with hba | hba
        · exact (hab.ne hba.symm).elim
        · simp at hba
  have hnot_edge : s(a, b) ∉ q.edges := by
    dsimp [q]
    simp [Sym2.eq_iff, hra.ne, hra.ne.symm, hrb.ne, hrb.ne.symm,
      hab.ne, hab.ne.symm]
  refine ⟨SimpleGraph.Walk.cons hab q,
    (SimpleGraph.Walk.cons_isCycle_iff q hab).2 ⟨hq, hnot_edge⟩, ?_⟩
  simp [q, SimpleGraph.Walk.length_cons]

end Walk

end SimpleGraph

end Erdos64
