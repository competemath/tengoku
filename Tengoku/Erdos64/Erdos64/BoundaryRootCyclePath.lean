import Tengoku.Erdos64.Erdos64.BoundaryRootGraph
import Tengoku.Erdos64.Erdos64.Arithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A dyadic cycle introduced by adding a boundary root leaves a simple
path between two distinct boundary vertices when the root is removed.
@isnad1 id=ex.2h3v.s7.23fbeef4cd04 from=translated src=- shape=ee3febb1 vocab=abe3c0af
-/
theorem boundaryRoot_dyadic_cycle_path
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] (B : Finset W)
    (hno : ¬HasPowerOfTwoCycle H)
    (hyes : HasPowerOfTwoCycle (boundaryRootGraph H B)) :
    ∃ k : ℕ, ∃ a b : W, ∃ p : H.Walk a b,
      2 ≤ k ∧ a ∈ B ∧ b ∈ B ∧ a ≠ b ∧ p.IsPath ∧
      p.length + 2 = 2 ^ k := by
  classical
  let K := boundaryRootGraph H B
  obtain ⟨k, z, c, hk, hc, hlen⟩ := hyes
  have hnone : none ∈ c.support := by
    by_contra hav
    obtain ⟨w, d, hd, hdl⟩ := boundaryRoot_cycle_avoiding_root c hc hav
    exact hno ⟨k, w, d, hk, hd, hdl.trans hlen⟩
  let r := c.rotate none hnone
  have hr : r.IsCycle := hc.rotate hnone
  cases hR : r with
  | nil =>
      have hnil : (SimpleGraph.Walk.nil : K.Walk none none).IsCycle := by
        simpa only [hR] using hr
      exact (SimpleGraph.Walk.not_isCycle_nil hnil).elim
  | @cons u v w h q =>
      have hr' : (SimpleGraph.Walk.cons h q).IsCycle := by
        simpa only [hR] using hr
      have hqnotnil : ¬q.Nil := SimpleGraph.Walk.not_nil_of_isCycle_cons hr'
      have hqpath : q.IsPath := by simpa using hr'.isPath_tail
      have hdropnone : ∀ t, t ∈ q.dropLast.support → t ≠ none := by
        intro t ht
        have hnodup : (q.dropLast.support ++ [none]).Nodup := by
          rw [q.support_dropLast_concat hqnotnil]
          exact hqpath.support_nodup
        intro ht_none
        exact (List.disjoint_left.mp (List.disjoint_of_nodup_append hnodup))
          ht (by simp [ht_none])
      let S : Set (Option W) := {t | t ≠ none}
      let qi := q.dropLast.induce S hdropnone
      let e := boundaryRootDeletedIso H B
      let emb : K.induce S ↪g K := SimpleGraph.Embedding.induce S
      have hmap : qi.map emb.toHom = q.dropLast :=
        q.dropLast.map_induce hdropnone
      have hqi : qi.IsPath := by
        apply (SimpleGraph.Walk.isPath_map_iff_of_injective
          (p := qi) (f := emb.toHom) emb.injective).mp
        rw [hmap]
        exact hqpath.dropLast
      let p := qi.map e.toHom
      have hp : p.IsPath := hqi.map e.injective
      have hp_len : p.length = q.dropLast.length := by
        have hind := congrArg SimpleGraph.Walk.length hmap
        rw [SimpleGraph.Walk.length_map] at hind
        exact (SimpleGraph.Walk.length_map e.toHom qi).trans hind
      have hboundary : ∀ t : {t : Option W // t ≠ none},
          K.Adj none t.1 → e t ∈ B := by
        rintro ⟨t, ht⟩ hadj
        cases t with
        | none => exact (ht rfl).elim
        | some a =>
            simpa [e, K] using hadj
      have ha := hboundary
        ⟨v, hdropnone v q.dropLast.start_mem_support⟩ h
      have hb := hboundary
        ⟨q.penultimate, hdropnone _ q.dropLast.end_mem_support⟩
        (q.adj_penultimate hqnotnil).symm
      have hclen : c.length = q.dropLast.length + 2 := by
        calc
          c.length = r.length := (c.length_rotate none hnone).symm
          _ = (SimpleGraph.Walk.cons h q).length := by rw [hR]
          _ = q.length + 1 := by simp
          _ = q.dropLast.length + 2 := by
            rw [← q.length_dropLast_add_one hqnotnil]
      have hplen : p.length + 2 = 2 ^ k := by omega
      have hpos : 0 < p.length := by
        have hpow := four_le_pow_two hk
        omega
      have hab : e ⟨v, hdropnone v q.dropLast.start_mem_support⟩ ≠
          e ⟨q.penultimate, hdropnone _ q.dropLast.end_mem_support⟩ := by
        intro hab
        have hnil := hp.nil_iff_eq.mpr hab
        exact (Nat.ne_of_gt hpos) hnil.length_eq_zero
      exact ⟨k, _, _, p, hk, ha, hb, hab, hp, hplen⟩

end Erdos64
