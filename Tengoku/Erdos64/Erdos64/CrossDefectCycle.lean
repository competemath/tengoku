import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

namespace SimpleGraph

namespace Walk

variable {V : Type u} {G : SimpleGraph V}

/-- Two disjoint terminal paths, joined crosswise at both ends, form a
    simple cycle. The support and endpoint hypotheses are explicit so this
    constructs a cycle rather than merely a closed walk.-/
theorem isCycle_append_cross_defect_paths
    {a₁ b₁ a₂ b₂ : V} {p : G.Walk a₁ b₁} {q : G.Walk a₂ b₂}
    (hp : p.IsPath)
    (hq : q.IsPath)
    (hab : a₁ ≠ b₁)
    (hcd : a₂ ≠ b₂)
    (hdis : p.support.Disjoint q.support)
    (h₁ : G.Adj b₁ b₂)
    (h₂ : G.Adj a₁ a₂) :
    ∃ c : G.Walk a₁ a₁, c.IsCycle ∧
      c.length = p.length + q.length + 2 := by
  let r : G.Walk b₁ a₁ :=
    SimpleGraph.Walk.cons h₁
      (SimpleGraph.Walk.cons h₂ q).reverse
  have ha₁_not_q : a₁ ∉ q.support := by
    rw [List.disjoint_left] at hdis
    intro ha₁q
    exact hdis p.start_mem_support ha₁q
  have hb₁_not_q : b₁ ∉ q.support := by
    rw [List.disjoint_left] at hdis
    intro hb₁q
    exact hdis p.end_mem_support hb₁q
  have hb₁_not_qpath : b₁ ∉ (SimpleGraph.Walk.cons h₂ q).support := by
    rw [SimpleGraph.Walk.support_cons]
    intro hb₁mem
    rcases List.mem_cons.mp hb₁mem with hb₁a₁ | hb₁q
    · exact hab hb₁a₁.symm
    · exact hb₁_not_q hb₁q
  have hb₁_not_return : b₁ ∉
      (SimpleGraph.Walk.cons h₂ q).reverse.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
      hb₁_not_qpath
  have hleft : (SimpleGraph.Walk.cons h₂ q).IsPath := by
    exact (SimpleGraph.Walk.cons_isPath_iff h₂ q).2 ⟨hq, ha₁_not_q⟩
  have hreturn : r.IsPath := by
    dsimp [r]
    exact (SimpleGraph.Walk.cons_isPath_iff h₁ _).2
      ⟨hleft.reverse, hb₁_not_return⟩
  have ha₁_not_tail : a₁ ∉ p.support.tail := by
    have hnodup : (a₁ :: p.support.tail).Nodup := by
      rw [p.cons_tail_support]
      exact hp.support_nodup
    exact (List.nodup_cons.mp hnodup).1
  have htails : p.support.tail.Disjoint r.support.tail := by
    rw [List.disjoint_left]
    intro z hzp hzr
    have hzreturn : z ∈ (SimpleGraph.Walk.cons h₂ q).reverse.support := by
      simpa [r] using hzr
    have hzreturn' : z ∈ (SimpleGraph.Walk.cons h₂ q).support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
        hzreturn
    rw [SimpleGraph.Walk.support_cons] at hzreturn'
    rcases List.mem_cons.mp hzreturn' with hza₁ | hzq
    · subst z
      exact (ha₁_not_tail hzp).elim
    · exact (List.disjoint_left.mp hdis
        (List.mem_of_mem_tail hzp) hzq).elim
  refine ⟨p.append r, hp.isCycle_append hreturn htails (Or.inr ?_), ?_⟩
  · simp [r, SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_reverse]
  · simp [r, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_reverse,
      Nat.add_assoc]

end Walk

end SimpleGraph

end Erdos64
