import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

/- Two simple paths which have already been normalized at their first
   reunion form a cycle. The distinct first steps rule out the degenerate
   two-edge backtrack. -/
/--
@isnad1 id=ex.9h8v.s7.3b867910407a from=translated src=- shape=7de69bdd vocab=2d367baa
-/
theorem SimpleGraph.Walk.IsPath.cycle_of_first_reunion
    {V : Type u} {G : SimpleGraph V} {w z : V}
    (p q : G.Walk w z) (hp : p.IsPath) (hq : q.IsPath)
    (hfirst : p.snd ≠ q.snd) {i j : ℕ}
    (hi_pos : 0 < i) (hi_le : i ≤ p.length)
    (hj_pos : 0 < j) (hj_le : j ≤ q.length)
    (hmeet : p.getVert i = q.getVert j)
    (hdisjoint :
      (p.take i).support.tail.Disjoint
        (q.take j).reverse.support.tail) :
    ∃ c : G.Walk w w, c.IsCycle ∧
      c.length = i + j ∧ c.length ≤ p.length + q.length := by
  let p' := p.take i
  let q' : G.Walk (p.getVert i) w :=
    (q.take j).reverse.copy hmeet.symm rfl
  have hp' : p'.IsPath := by
    simpa [p'] using hp.take i
  have hq' : q'.IsPath := by
    simpa [q'] using (SimpleGraph.Walk.isPath_reverse_iff (q.take j)).mpr
      (hq.take j)
  have hdisjoint' : p'.support.tail.Disjoint q'.support.tail := by
    simpa [p', q'] using hdisjoint
  have hpi : p'.length = i := by
    simp [p', SimpleGraph.Walk.take_length, Nat.min_eq_left hi_le]
  have hqj : q'.length = j := by
    simp [q', SimpleGraph.Walk.length_reverse,
      SimpleGraph.Walk.take_length, Nat.min_eq_left hj_le]
  have hnontrivial : 1 < p'.length ∨ 1 < q'.length := by
    rw [hpi, hqj]
    by_contra h
    push_neg at h
    have hi_one : i = 1 := by omega
    have hj_one : j = 1 := by omega
    exact hfirst (by simpa [hi_one, hj_one, SimpleGraph.Walk.snd] using hmeet)
  let c := p'.append q'
  refine ⟨c, ?_, ?_, ?_⟩
  · exact hp'.isCycle_append hq' hdisjoint' hnontrivial
  · simp [c, SimpleGraph.Walk.length_append, hpi, hqj]
  · simpa [c, SimpleGraph.Walk.length_append, hpi, hqj] using
      Nat.add_le_add hi_le hj_le

end Erdos64
