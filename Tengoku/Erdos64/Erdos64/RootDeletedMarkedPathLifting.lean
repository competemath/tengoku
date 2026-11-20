import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

namespace SimpleGraph

namespace Walk

variable {V : Type u} {G : SimpleGraph V}

/-- The data of a root-avoiding path together with its two marked root edges.-/
structure MarkedRootPath (r a b : V) where
  path : G.Walk a b
  isPath : path.IsPath
  root_not_mem : r ∉ path.support
  root_adj_start : G.Adj r a
  root_adj_end : G.Adj r b
  endpoints_ne : a ≠ b
  length_gt_one : 1 < path.length

/-- A marked path supplies a genuinely simple cycle, not merely a closed walk.
@isnad1 id=ex.0h6v.s6.4ea4dc4aae66 from=translated src=- shape=f6dd6c23 vocab=0ac63e8f
-/
theorem MarkedRootPath.exists_cycle (P : MarkedRootPath (G := G) r a b) :
    ∃ c : G.Walk a a, c.IsCycle ∧ c.length = P.path.length + 2 := by
  exact endpoint_fan_cycle_certificate P.isPath P.root_adj_start P.root_adj_end
    P.root_not_mem P.endpoints_ne P.length_gt_one

/-- Removing the first and last edges from a cycle rooted at `r` gives the
root-avoiding middle path.
@isnad1 id=ex.1h4v.s7.ba8f51c973ff from=translated src=- shape=7ac84d25 vocab=2ba4e72c
-/
theorem marked_cycle_decompose
    {r : V} {c : G.Walk r r} (hc : c.IsCycle) :
    ∃ q : G.Walk c.snd c.tail.penultimate,
      q.IsPath ∧ r ∉ q.support ∧ q.length + 2 = c.length := by
  have htail : c.tail.IsPath := hc.isPath_tail
  have htail_nil : ¬c.tail.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    simp only [SimpleGraph.Walk.length_tail]
    have hlen := hc.three_le_length
    omega
  let q : G.Walk c.snd c.tail.penultimate := c.tail.dropLast
  have hqpath : q.IsPath := by
    exact htail.dropLast
  have hqroot : r ∉ q.support := by
    intro hrq
    have hrdrop : r ∈ c.tail.support.dropLast := by
      simpa [q, c.tail.support_dropLast htail_nil] using hrq
    have hsplit : c.tail.support.dropLast ++ [r] = c.tail.support := by
      have hsne : c.tail.support ≠ [] := c.tail.support_ne_nil
      simpa using
        (List.dropLast_append_getLast (l := c.tail.support) hsne)
    have hnodup : (c.tail.support.dropLast ++ [r]).Nodup := by
      rw [hsplit]
      exact htail.support_nodup
    have hdisj := (List.nodup_append.mp hnodup).2.2
    exact (hdisj r hrdrop r (by simp)) rfl
  refine ⟨q, hqpath, hqroot, ?_⟩
  have htail_len := c.length_tail_add_one hc.not_nil
  have hdrop_len := c.tail.length_dropLast_add_one htail_nil
  change c.tail.dropLast.length + 2 = c.length
  omega

end Walk

end SimpleGraph

end Erdos64
