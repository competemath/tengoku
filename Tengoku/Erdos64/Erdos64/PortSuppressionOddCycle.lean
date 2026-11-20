import Tengoku.Erdos64.Erdos64.DegreeTwoSuppression
import Tengoku.Erdos64.Erdos64.OneDefectDyadicForcing
import Tengoku.Erdos64.Erdos64.AddedEdgeCyclePath
import Tengoku.Erdos64.Erdos64.RootDeletedNoDyadicTransfer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Close a nontrivial simple path through a fresh vertex, using that vertex
as the basepoint of the resulting simple cycle.-/
theorem cycle_based_at_fresh_vertex
    {W : Type u} {H : SimpleGraph W} {x a b : W}
    (p : H.Walk a b) (hp : p.IsPath) (hab : a ≠ b)
    (hxa : H.Adj x a) (hxb : H.Adj x b) (hx : x ∉ p.support) :
    ∃ c : H.Walk x x, c.IsCycle ∧ c.length = p.length + 2 := by
  let c := SimpleGraph.Walk.cons hxa (p.concat hxb.symm)
  refine ⟨c, ?_, ?_⟩
  · apply (SimpleGraph.Walk.cons_isCycle_iff _ hxa).mpr
    refine ⟨hp.concat hx hxb.symm, ?_⟩
    intro he
    simp only [SimpleGraph.Walk.edges_concat, List.concat_eq_append,
      List.mem_append, List.mem_singleton] at he
    rcases he with he | he
    · exact hx (p.fst_mem_support_of_mem_edges he)
    · rcases Sym2.eq_iff.mp he with he | he
      · exact hxb.ne he.1
      · exact hab he.2
  · simp [c, Nat.add_assoc]

/-- Suppress one degree-two port and double at the other possible defect.
Minimality forces an odd cycle through the suppressed port whose length is
one more than a power of two. The triangle case has exponent one.-/
theorem MinimalCounterexample.two_defect_port_dyadic_successor_cycle
    {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Fintype W] [DecidableEq W] [DecidableRel H.Adj]
    (M : MinimalCounterexample G) (x y : W) (hxy : x ≠ y)
    (hx : H.degree x = 2) (hy : 2 ≤ H.degree y)
    (hother : ∀ w, w ≠ x → w ≠ y → 3 ≤ H.degree w)
    (hno : ¬ HasPowerOfTwoCycle H)
    (hsize : 2 * Fintype.card W - 3 < Fintype.card V) :
    ∃ k : ℕ, ∃ c : H.Walk x x,
      1 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 1 := by
  classical
  obtain ⟨a, b, hab, hN⟩ := Finset.card_eq_two.mp
    (show (H.neighborFinset x).card = 2 by simpa using hx)
  have hneighbors : ∀ w, H.Adj x w ↔ w = a ∨ w = b := by
    intro w
    rw [← SimpleGraph.mem_neighborFinset, hN]
    simp
  have hxa := (hneighbors a).2 (Or.inl rfl)
  have hxb := (hneighbors b).2 (Or.inr rfl)
  by_cases hadj : H.Adj a b
  · have hxavoid : x ∉ hadj.toWalk.support := by
      simp [SimpleGraph.Adj.toWalk, hxa.ne, hxb.ne]
    obtain ⟨c, hc, hlen⟩ := cycle_based_at_fresh_vertex
      hadj.toWalk (SimpleGraph.Walk.IsPath.of_adj hadj) hab hxa hxb hxavoid
    exact ⟨1, c, by omega, hc, by simpa using hlen⟩
  let K := degreeTwoSuppressionGraph H x a b hxa.ne.symm hxb.ne.symm
  let y' : {w : W // w ≠ x} := ⟨y, hxy.symm⟩
  have hdeg : ∀ w, K.degree w = H.degree w.1 :=
    degreeTwoSuppressionGraph_degree H x a b hxa.ne.symm hxb.ne.symm
      hab hadj hneighbors
  have hroot : 2 ≤ K.degree y' := by rw [hdeg]; exact hy
  have hothers : ∀ w, w ≠ y' → 3 ≤ K.degree w := by
    intro w hw
    rw [hdeg]
    exact hother w.1 w.2 (fun h => hw (Subtype.ext h))
  have hcard := card_ne_vertex_add_one x
  have hsmall : 2 * Fintype.card {w : W // w ≠ x} - 1 < Fintype.card V := by
    omega
  have hyes := M.one_defect_small_has_dyadic_cycle y' hroot hothers hsmall
  have hdeleted : ¬ HasPowerOfTwoCycle (H.induce {w | w ≠ x}) :=
    not_hasPowerOfTwoCycle_induce_of_not_hasPowerOfTwoCycle hno
  obtain ⟨k, q, hk, hq, hlen⟩ := added_edge_dyadic_cycle_path hdeleted hyes
  let e : H.induce {w | w ≠ x} ↪g H := SimpleGraph.Embedding.induce _
  let p := q.map e.toHom
  have hp : p.IsPath := hq.map e.injective
  have hxavoid : x ∉ p.support := by
    intro hxmem
    rw [SimpleGraph.Walk.support_map] at hxmem
    obtain ⟨w, _, hw⟩ := List.mem_map.mp hxmem
    exact w.2 hw
  obtain ⟨c, hc, hclen⟩ := cycle_based_at_fresh_vertex p hp hab hxa hxb hxavoid
  refine ⟨k, c, by omega, hc, ?_⟩
  have hplen : p.length + 1 = 2 ^ k := by
    simpa only [p, SimpleGraph.Walk.length_map] using hlen
  omega

end Erdos64
