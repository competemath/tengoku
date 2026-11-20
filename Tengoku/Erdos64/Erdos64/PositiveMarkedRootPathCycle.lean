import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

namespace SimpleGraph

namespace Walk

variable {V : Type u} {G : SimpleGraph V}

/-- Two marked root edges and a simple root-avoiding positive path form a
simple cycle. The length-one case is the explicit triangle case.
@isnad1 id=ex.6h6v.s6.677ad546d978 from=translated src=- shape=cc9a83bd vocab=c5275a75
-/
theorem exists_cycle_of_positive_marked_root_path
    {r a b : V} {q : G.Walk a b}
    (hq : q.IsPath)
    (hroot : r ∉ q.support)
    (hra : G.Adj r a)
    (hrb : G.Adj r b)
    (hab : a ≠ b)
    (hpositive : 0 < q.length) :
    ∃ c : G.Walk a a, c.IsCycle ∧ c.length = q.length + 2 := by
  classical
  by_cases hlong : 1 < q.length
  · obtain ⟨c, hc, hlen⟩ := endpoint_fan_cycle_certificate
      hq hra hrb hroot hab hlong
    exact ⟨c, hc, hlen⟩
  · have hlen : q.length = 1 := by omega
    cases q with
    | nil => simp at hpositive
    | cons h p =>
      cases p with
      | nil =>
        have hra_ne : r ≠ a := by
          intro hra_eq
          apply hroot
          simpa [hra_eq]
        have hrb_ne : r ≠ b := by
          intro hrb_eq
          apply hroot
          simpa [hrb_eq]
        refine ⟨SimpleGraph.Walk.cons h
          (SimpleGraph.Walk.cons hrb.symm (SimpleGraph.Walk.cons hra
            SimpleGraph.Walk.nil)), ?_, ?_⟩
        · simp only [SimpleGraph.Walk.cons_isCycle_iff]
          constructor
          · apply (SimpleGraph.Walk.cons_isPath_iff hrb.symm _).2
            refine ⟨?_, ?_⟩
            · apply (SimpleGraph.Walk.cons_isPath_iff hra _).2
              exact ⟨SimpleGraph.Walk.IsPath.nil, by simp [hra_ne]⟩
            · intro hb
              simp only [SimpleGraph.Walk.support_cons,
                SimpleGraph.Walk.support_nil, List.mem_cons,
                List.mem_singleton] at hb
              rcases hb with rfl | rfl | hb
              · exact hrb_ne rfl
              · exact hab rfl
              · simp at hb
          · intro hedge
            simp only [SimpleGraph.Walk.edges_cons,
              SimpleGraph.Walk.edges_nil, List.mem_cons] at hedge
            simp only [Sym2.eq_iff] at hedge
            rcases hedge with h₁ | h₂ | h₃
            · rcases h₁ with h₁ | h₁
              · exact hab h₁.1
              · exact hra_ne h₁.1.symm
            · rcases h₂ with h₂ | h₂
              · exact hra_ne h₂.1.symm
              · exact hrb_ne h₂.2.symm
            · simp at h₃
        · simp [hlen]
      | cons h₂ p₂ =>
        simp at hlen

end Walk

end SimpleGraph

end Erdos64
