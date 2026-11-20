import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A root with two distinct neighbors, joined through a root-avoiding simple
path, gives a simple cycle with the two connector edges on each side.-/
theorem separated_third_neighbor_cycle
    {V : Type u} {G : SimpleGraph V}
    {r x y z w : V} {p : G.Walk z w}
    (hp : p.IsPath)
    (havoid : ∀ v, v ∈ p.support →
      v ≠ r ∧ v ≠ x ∧ v ≠ y)
    (hxy : x ≠ y)
    (hrx : G.Adj r x)
    (hry : G.Adj r y)
    (hxz : G.Adj x z)
    (hyw : G.Adj y w) :
    ∃ c : G.Walk x x, c.IsCycle ∧ r ∈ c.support ∧
      c.length = p.length + 4 := by
  have hzavoid := havoid z p.start_mem_support
  have hwavoid := havoid w p.end_mem_support
  let q : G.Walk x y :=
    SimpleGraph.Walk.cons hxz
      (p.append (SimpleGraph.Walk.cons hyw.symm SimpleGraph.Walk.nil))
  have htail :
      (p.append (SimpleGraph.Walk.cons hyw.symm SimpleGraph.Walk.nil)).IsPath := by
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append]
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.tail_cons]
    apply List.nodup_append.mpr
    refine ⟨hp.support_nodup, by simp, ?_⟩
    intro v hv b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact (havoid v hv).2.2
  have hq : q.IsPath := by
    dsimp [q]
    apply (SimpleGraph.Walk.cons_isPath_iff hxz _).2
    refine ⟨htail, ?_⟩
    rw [SimpleGraph.Walk.support_append]
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.tail_cons, List.mem_append, List.mem_singleton]
    intro hxmem
    rcases hxmem with hxmem | rfl
    · exact (havoid x hxmem).2.1 rfl
    · exact hxy rfl
  let ret : G.Walk y x :=
    SimpleGraph.Walk.cons hry.symm
      (SimpleGraph.Walk.cons hrx SimpleGraph.Walk.nil)
  have hret : ret.IsPath := by
    dsimp [ret]
    apply (SimpleGraph.Walk.cons_isPath_iff hry.symm _).2
    refine ⟨?_, ?_⟩
    · apply (SimpleGraph.Walk.cons_isPath_iff hrx _).2
      exact ⟨SimpleGraph.Walk.IsPath.nil, by
        simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using hrx.ne⟩
    · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons]
      intro hy
      rcases hy with hy | hy
      · exact hry.ne.symm hy
      · rcases hy with hy | hy
        · exact hxy.symm hy
        · simp at hy
  have hdis : q.support.tail.Disjoint ret.support.tail := by
    dsimp [q, ret]
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_nil, List.tail_cons]
    rw [List.disjoint_left]
    intro v hv hu
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_cons.mp hu with hu | hu
      · exact (havoid v hv).1 hu
      · simp only [List.mem_singleton] at hu
        exact (havoid v hv).2.1 hu
    · simp only [List.mem_singleton] at hv
      subst v
      rcases List.mem_cons.mp hu with hu | hu
      · exact hry.ne hu.symm
      · simp only [List.mem_singleton] at hu
        exact hxy hu.symm
  let c := q.append ret
  have hqLength : 1 < q.length := by
    simp [q, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_append]
  have hc : c.IsCycle := by
    dsimp [c]
    exact hq.isCycle_append hret hdis (Or.inl hqLength)
  refine ⟨c, hc, ?_, ?_⟩
  · dsimp [c, ret]
    rw [SimpleGraph.Walk.support_append]
    simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.tail_cons]
  · simp [c, q, ret, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_cons]

end Erdos64
