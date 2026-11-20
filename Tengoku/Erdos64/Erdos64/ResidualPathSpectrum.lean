import Tengoku.Erdos64.Erdos64.SharedRootQuotientResidual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A root-avoiding opposite-port residual path extends to a simple path
between the two ports.  Its length is exactly the dyadic length supplied by
quotient transport.
@isnad1 id=or.8h9v.s8.894cfc5a0b57 from=translated src=- shape=ddee1e28 vocab=51f38e99
-/
theorem cross_residual_path_to_dyadic_port_path
    {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] [DecidableRel G.Adj]
    {r x y u v : V} {p : G.Walk u v} {k : ℕ}
    (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : x ≠ y)
    (hp : p.IsPath)
    (havoid : ∀ w, w ∈ p.support → w ≠ x ∧ w ≠ y)
    (hroot : r ∉ p.support)
    (hlen : p.length + 2 = 2 ^ k)
    (hadj : (G.Adj x u ∧ G.Adj y v) ∨
      (G.Adj y u ∧ G.Adj x v)) :
    (∃ q : G.Walk x y,
      q.IsPath ∧ r ∉ q.support ∧ q.length = 2 ^ k) ∨
    (∃ q : G.Walk y x,
      q.IsPath ∧ r ∉ q.support ∧ q.length = 2 ^ k) := by
  rcases hadj with ⟨hxu, hyv⟩ | ⟨hyu, hxv⟩
  · left
    let tail : G.Walk u y :=
      p.append (SimpleGraph.Walk.cons hyv.symm SimpleGraph.Walk.nil)
    have htail : tail.IsPath := by
      dsimp [tail]
      rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append]
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.tail_cons]
      apply List.nodup_append.mpr
      refine ⟨hp.support_nodup, by simp, ?_⟩
      intro w hw z hz
      simp only [List.mem_singleton] at hz
      subst z
      exact (havoid w hw).2
    let q : G.Walk x y := SimpleGraph.Walk.cons hxu tail
    have hq : q.IsPath := by
      dsimp [q]
      apply (SimpleGraph.Walk.cons_isPath_iff hxu _).2
      refine ⟨htail, ?_⟩
      rw [SimpleGraph.Walk.support_append]
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.tail_cons, List.mem_append, List.mem_singleton]
      intro hxmem
      rcases hxmem with hxmem | rfl
      · exact (havoid x hxmem).1 rfl
      · exact hxy rfl
    have hqroot : r ∉ q.support := by
      have hrv : r ≠ v := by
        intro hrv
        apply hroot
        simpa [hrv] using p.end_mem_support
      simp [q, tail, hroot, hrx.ne, hry.ne, hrv]
    refine ⟨q, hq, hqroot, ?_⟩
    simp [q, tail, SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_append, hlen]
  · right
    let tail : G.Walk u x :=
      p.append (SimpleGraph.Walk.cons hxv.symm SimpleGraph.Walk.nil)
    have htail : tail.IsPath := by
      dsimp [tail]
      rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append]
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.tail_cons]
      apply List.nodup_append.mpr
      refine ⟨hp.support_nodup, by simp, ?_⟩
      intro w hw z hz
      simp only [List.mem_singleton] at hz
      subst z
      exact (havoid w hw).1
    let q : G.Walk y x := SimpleGraph.Walk.cons hyu tail
    have hq : q.IsPath := by
      dsimp [q]
      apply (SimpleGraph.Walk.cons_isPath_iff hyu _).2
      refine ⟨htail, ?_⟩
      rw [SimpleGraph.Walk.support_append]
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.tail_cons, List.mem_append, List.mem_singleton]
      intro hymem
      rcases hymem with hymem | rfl
      · exact (havoid y hymem).2 rfl
      · exact hxy.symm rfl
    have hqroot : r ∉ q.support := by
      have hrv : r ≠ v := by
        intro hrv
        apply hroot
        simpa [hrv] using p.end_mem_support
      simp [q, tail, hroot, hrx.ne, hry.ne, hrv]
    refine ⟨q, hq, hqroot, ?_⟩
    simp [q, tail, SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_append, hlen]

end Erdos64
