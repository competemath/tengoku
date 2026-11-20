import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A simple cycle meeting a one-port carrier is contained in that carrier
    together with its boundary root.  The proof uses only the boundary
    condition and the fact that a simple cycle has two disjoint complementary
    arcs away from their endpoints.-/
theorem SimpleGraph.Walk.IsCycle.onePort_support_dichotomy
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {s : V} {c : G.Walk s s} (hc : c.IsCycle)
    (K : Finset V) (x : V) (hx : x ∉ K)
    (hbd :
      ∀ u, u ∈ K → ∀ v, v ∉ K → G.Adj u v → v = x) :
    (∀ v, v ∈ c.support → v ∉ K) ∨
      (∀ v, v ∈ c.support → v = x ∨ v ∈ K) := by
  have path_subset_K :
      ∀ {a b : V} (p : G.Walk a b), p.IsPath → a ∈ K →
        x ∉ p.support → ∀ v, v ∈ p.support → v ∈ K := by
    intro a b p
    induction p with
    | nil =>
        intro _ ha _ v hv
        simp at hv
        subst v
        exact ha
    | @cons a b d h q ih =>
        intro hp ha hxq v hv
        have hqpath : q.IsPath := hp.of_cons
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact ha
        · have hb : b ∈ K := by
            by_contra hbn
            have hbsupport : b ∈ (SimpleGraph.Walk.cons h q).support := by
              simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
              exact Or.inr q.start_mem_support
            have hbx : b = x := hbd a ha b hbn h
            exact hxq (hbx ▸ hbsupport)
          have hxq' : x ∉ q.support := by
            intro hxm
            apply hxq
            simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
            exact Or.inr hxm
          exact ih hqpath hb hxq' v hv
  by_cases hmeet : ∃ u, u ∈ K ∧ u ∈ c.support
  · right
    intro v hv
    by_cases hvK : v ∈ K
    · exact Or.inr hvK
    by_cases hvx : v = x
    · exact Or.inl hvx
    obtain ⟨u, huK, huC⟩ := hmeet
    have huv : u ≠ v := by
      intro huv
      apply hvK
      simpa [huv] using huK
    obtain ⟨p, q, hpq⟩ :=
      SimpleGraph.Walk.IsCycle.exists_path_arcs hc huC hv huv
    have hxu : x ≠ u := by
      intro hxu
      apply hx
      simpa [hxu] using huK
    have hxv : x ≠ v := by
      exact Ne.symm hvx
    have hnodup :
        ((p : G.Walk u v).append (q : G.Walk v u)).support.tail.Nodup := by
      rw [hpq]
      exact (hc.rotate huC).support_nodup
    rw [SimpleGraph.Walk.tail_support_append] at hnodup
    have hdisjoint :
        (p : G.Walk u v).support.tail.Disjoint
          (q : G.Walk v u).support.tail :=
      List.disjoint_of_nodup_append hnodup
    by_cases hxp : x ∈ (p : G.Walk u v).support
    · have hxq : x ∉ (q : G.Walk v u).support := by
        intro hxq
        have hxp_tail : x ∈ (p : G.Walk u v).support.tail := by
          rw [SimpleGraph.Walk.mem_support_iff] at hxp
          exact hxp.resolve_left hxu
        have hxq_tail : x ∈ (q : G.Walk v u).support.tail := by
          rw [SimpleGraph.Walk.mem_support_iff] at hxq
          exact hxq.resolve_left hxv
        exact (List.disjoint_left.mp hdisjoint) hxp_tail hxq_tail
      have hqrevx : x ∉ (q : G.Walk v u).reverse.support := by
        simpa [SimpleGraph.Walk.support_reverse] using hxq
      have hvrev : v ∈ (q : G.Walk v u).reverse.support :=
        (q : G.Walk v u).reverse.end_mem_support
      have hvK' := path_subset_K (q : G.Walk v u).reverse
        q.property.reverse huK hqrevx v hvrev
      exact (hvK hvK').elim
    · have hvK' := path_subset_K (p : G.Walk u v)
        p.property huK hxp v (p : G.Walk u v).end_mem_support
      exact (hvK hvK').elim
  · left
    intro v hv hvK
    exact hmeet ⟨v, hvK, hv⟩

/-- A cycle through the one-port root and its carrier contains an internal
    carrier path between two distinct neighbors of the root.-/
theorem SimpleGraph.Walk.IsCycle.onePort_cycle_excursion
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {s : V} {c : G.Walk s s} (hc : c.IsCycle)
    (x : V) (hxcycle : x ∈ c.support)
    (K : Finset V) (hx : x ∉ K)
    (hbd :
      ∀ u, u ∈ K → ∀ v, v ∉ K → G.Adj u v → v = x)
    (hmeet : ∃ v, v ∈ c.support ∧ v ∈ K) :
    ∃ a b : V, a ∈ K ∧ b ∈ K ∧ a ≠ b ∧
      G.Adj x a ∧ G.Adj b x ∧
      ∃ p : G.Walk a b,
        p.IsPath ∧
        (∀ v, v ∈ p.support → v ∈ K) ∧
        c.length = p.length + 2 := by
  have hcontained : ∀ v, v ∈ c.support → v = x ∨ v ∈ K := by
    rcases Erdos64.SimpleGraph.Walk.IsCycle.onePort_support_dichotomy
      hc K x hx hbd with hnone | hcontained
    · obtain ⟨v, hvC, hvK⟩ := hmeet
      exact (hnone v hvC hvK).elim
    · exact hcontained
  let r := c.rotate x hxcycle
  have hr : r.IsCycle := by
    simpa [r] using hc.rotate hxcycle
  cases hR : r with
  | nil =>
      have hrnil : (SimpleGraph.Walk.nil : G.Walk x x).IsCycle := by
        simpa [hR] using hr
      exact (SimpleGraph.Walk.not_isCycle_nil hrnil).elim
  | @cons a b d h q =>
      have hr' : (SimpleGraph.Walk.cons h q).IsCycle := by
        simpa [hR] using hr
      have hqnotnil : ¬q.Nil :=
        SimpleGraph.Walk.not_nil_of_isCycle_cons hr'
      have hqpath : q.IsPath := by
        simpa using hr'.isPath_tail
      have hxa : G.Adj x b := by
        simpa using h
      have hbx : G.Adj q.penultimate x := by
        simpa using q.adj_penultimate hqnotnil
      have hq_to_c : ∀ {v : V}, v ∈ q.support → v ∈ c.support := by
        intro v hv
        have hvrot : v ∈ r.support := by
          rw [hR]
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
          exact Or.inr hv
        exact (SimpleGraph.Walk.mem_support_rotate_iff c x hxcycle).mp
          (by simpa [r] using hvrot)
      have hxdrop : x ∉ q.dropLast.support := by
        have hnodup : (q.dropLast.support ++ [x]).Nodup := by
          rw [q.support_dropLast_concat hqnotnil]
          exact hqpath.support_nodup
        exact fun hxm =>
          (List.disjoint_left.mp (List.disjoint_of_nodup_append hnodup))
            hxm (by simp)
      have hpK : ∀ v, v ∈ q.dropLast.support → v ∈ K := by
        intro v hv
        have hvq : v ∈ q.support := by
          rw [q.support_dropLast hqnotnil] at hv
          exact List.mem_of_mem_dropLast hv
        have hvx : v ≠ x := by
          intro hvx
          apply hxdrop
          simpa [hvx] using hv
        exact (hcontained v (hq_to_c hvq)).resolve_left hvx
      have haK : b ∈ K := by
        exact (hcontained b (hq_to_c q.start_mem_support)).resolve_left
          (Ne.symm hxa.ne)
      have hbK : q.penultimate ∈ K := by
        apply hpK
        rw [q.support_dropLast hqnotnil]
        exact q.penultimate_mem_dropLast_support hqnotnil
      have hq_len : 2 ≤ q.length := by
        have hlen := hr'.three_le_length
        simp only [SimpleGraph.Walk.length_cons] at hlen
        omega
      have hab : b ≠ q.penultimate := by
        intro hab
        have hget : q.getVert 0 = q.getVert (q.length - 1) := by
          simpa [SimpleGraph.Walk.penultimate] using hab
        have hindex : 0 = q.length - 1 := by
          exact hqpath.getVert_injOn (x₁ := 0) (x₂ := q.length - 1)
            (show 0 ≤ q.length by exact Nat.zero_le _)
            (show q.length - 1 ≤ q.length by exact Nat.sub_le _ _) hget
        omega
      have hlength : c.length = q.dropLast.length + 2 := by
        have hq_length : q.dropLast.length + 1 = q.length :=
          q.length_dropLast_add_one hqnotnil
        calc
          c.length = r.length := by
            symm
            simpa [r] using (SimpleGraph.Walk.length_rotate c x hxcycle)
          _ = (SimpleGraph.Walk.cons h q).length := by rw [hR]
          _ = q.length + 1 := by simp
          _ = q.dropLast.length + 2 := by omega
      exact ⟨b, q.penultimate, haK, hbK, hab, hxa, hbx,
        q.dropLast, hqpath.dropLast, hpK, hlength⟩

end Erdos64
