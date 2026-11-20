import Tengoku.Erdos64.Erdos64.Basic
import Tengoku.Seed.Combinatorics.SimpleGraph.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Removing a specified edge from a simple cycle preserves every other edge
and leaves a simple path between the edge endpoints.-/
theorem cycle_path_of_mem_edge
    {V : Type u} {G : SimpleGraph V} {a b z : V}
    {c : G.Walk z z} (hc : c.IsCycle)
    (he : s(a, b) ∈ c.edges) :
    ∃ p : G.Walk a b, p.IsPath ∧ s(a, b) ∉ p.edges ∧
      p.length + 1 = c.length := by
  classical
  have hab : a ≠ b := (c.adj_of_mem_edges he).ne
  have ha : a ∈ c.support := c.fst_mem_support_of_mem_edges he
  let d := c.rotate a ha
  have hd : d.IsCycle := hc.rotate ha
  have hde : s(a, b) ∈ d.edges :=
    (c.rotate_edges a ha).perm.mem_iff.mpr he
  have hdlen : d.length = c.length := c.length_rotate a ha
  cases hddef : d with
  | nil => simp [hddef] at hd
  | @cons _ t _ hat q =>
      have hd' : (SimpleGraph.Walk.cons hat q).IsCycle := by
        simpa [hddef] using hd
      have hq := (SimpleGraph.Walk.cons_isCycle_iff q hat |>.mp hd').1
      have hedge := (SimpleGraph.Walk.cons_isCycle_iff q hat |>.mp hd').2
      have hedges : s(a, b) = s(a, t) ∨ s(a, b) ∈ q.edges := by
        simpa only [hddef, SimpleGraph.Walk.edges_cons, List.mem_cons] using hde
      rcases hedges with hfront | hlast
      · have htb : t = b := by
          rcases Sym2.eq_iff.mp hfront with h | h
          · exact h.2.symm
          · exact (hab h.2.symm).elim
        subst t
        refine ⟨q.reverse, hq.reverse, ?_, ?_⟩
        · simpa [Sym2.eq_swap] using hedge
        · simpa [hddef] using hdlen
      · have hbpen : b = q.penultimate := hq.eq_penultimate_of_mem_edges hlast
        have hqnil : ¬q.Nil := SimpleGraph.Walk.not_nil_of_isCycle_cons hd'
        have hdpen : d.penultimate = b := by
          rw [hddef, SimpleGraph.Walk.penultimate_cons_of_not_nil hat q hqnil]
          exact hbpen.symm
        let p := d.dropLast.copy rfl hdpen
        have hp : p.IsPath := by
          simpa [p] using hd.isPath_dropLast
        have hparts : d.dropLast.edges ++ [s(d.penultimate, a)] = d.edges := by
          have heq := congrArg SimpleGraph.Walk.edges
            (SimpleGraph.Walk.concat_dropLast (p := d) (d.adj_penultimate hd.not_nil))
          simpa only [SimpleGraph.Walk.edges_concat, List.concat_eq_append] using heq
        have hnot : s(a, b) ∉ d.dropLast.edges := by
          have hnodup := hd.isTrail.edges_nodup
          rw [← hparts] at hnodup
          intro hmem
          have hdisj := (List.nodup_append.mp hnodup).2.2
          exact hdisj _ hmem _ (by simp [hdpen, Sym2.eq_swap]) rfl
        refine ⟨p, hp, ?_, ?_⟩
        · simpa [p] using hnot
        · simpa [p, hdlen] using d.length_dropLast_add_one hd.not_nil

/-- If adding one edge creates a dyadic cycle in a dyadic-cycle-free graph,
deleting the added edge yields a simple path of length one less than a power
of two. The returned walk uses only edges of the original graph.-/
theorem added_edge_dyadic_cycle_path
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hno : ¬ HasPowerOfTwoCycle G)
    (hyes : HasPowerOfTwoCycle (G ⊔ SimpleGraph.edge a b)) :
    ∃ k : ℕ, ∃ p : G.Walk a b,
      2 ≤ k ∧ p.IsPath ∧ p.length + 1 = 2 ^ k := by
  classical
  have htransfer : ∀ {u v : V}
      (p : (G ⊔ SimpleGraph.edge a b).Walk u v),
      s(a, b) ∉ p.edges → ∀ e, e ∈ p.edges → e ∈ G.edgeSet := by
    intro u v p hav e he
    have heG := p.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_sup] at heG
    rcases heG with heG | headd
    · exact heG
    · have heeq : e = s(a, b) := SimpleGraph.edgeSet_edge_subset headd
      exact (hav (heeq ▸ he)).elim
  obtain ⟨k, z, c, hk, hc, hlen⟩ := hyes
  have he : s(a, b) ∈ c.edges := by
    by_contra he
    let q := c.transfer G (htransfer c he)
    apply hno
    refine ⟨k, z, q, hk, hc.transfer _, ?_⟩
    simpa [q] using hlen
  obtain ⟨p, hp, hpavoid, hplen⟩ := cycle_path_of_mem_edge hc he
  let q := p.transfer G (htransfer p hpavoid)
  refine ⟨k, q, hk, hp.transfer _, ?_⟩
  simpa [q, ← hlen] using hplen

end Erdos64
