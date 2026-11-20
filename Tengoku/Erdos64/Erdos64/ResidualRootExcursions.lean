import Tengoku.Erdos64.Erdos64.ResidualPathRootSplit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Endpoint fan cycles remain valid for any positive path length: the fixed
  two-edge return arc supplies the nontrivial cycle side.
@isnad1 id=ex.6h6v.s6.233e39f113c0 from=translated src=- shape=e333ca82 vocab=c5275a75
-/
theorem endpoint_fan_cycle_certificate_of_pos
    {V : Type u} {G : SimpleGraph V}
    {a b v : V} {q : G.Walk a b}
    (hq : q.IsPath)
    (hva : G.Adj v a)
    (hvb : G.Adj v b)
    (hva_not_mem : v ∉ q.support)
    (hab : a ≠ b)
    (hqlen : 0 < q.length) :
    ∃ c : G.Walk a a, c.IsCycle ∧ c.length = q.length + 2 := by
  let r : G.Walk b a :=
    SimpleGraph.Walk.cons hvb.symm (SimpleGraph.Walk.cons hva SimpleGraph.Walk.nil)
  have hr : r.IsPath := by
    dsimp [r]
    refine (SimpleGraph.Walk.cons_isPath_iff _ _).2 ⟨?_, ?_⟩
    · exact
        (SimpleGraph.Walk.cons_isPath_iff _ _).2
          ⟨SimpleGraph.Walk.IsPath.nil, by simp [hva.ne]⟩
    · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons]
      intro hba
      rcases hba with hba | hba
      · exact (hvb.ne.symm hba).elim
      · rcases hba with hba | hba
        · exact (hab hba.symm).elim
        · simp at hba
  have hq_nil : ¬q.Nil := by
    intro hnil
    have hzero : q.length = 0 := by simp [hnil]
    omega
  have ha_not_mem_tail : a ∉ q.support.tail := by
    have hsupp : a :: q.support.tail = q.support := by
      calc
        a :: q.support.tail = a :: q.tail.support := by
          rw [q.support_tail_of_not_nil hq_nil]
        _ = q.support := q.cons_support_tail hq_nil
    have hnodup : (a :: q.support.tail).Nodup := by
      rw [hsupp]
      exact hq.support_nodup
    exact (List.nodup_cons.mp hnodup).1
  have hdis : q.support.tail.Disjoint r.support.tail := by
    dsimp [r]
    simp only [List.disjoint_left, List.mem_cons]
    intro x hxq hxr
    rcases hxr with rfl | hxr
    · exact (hva_not_mem (List.mem_of_mem_tail hxq)).elim
    · rcases hxr with hxr | hxr
      · exact (ha_not_mem_tail (hxr ▸ hxq)).elim
      · simp at hxr
  refine ⟨q.append r, hq.isCycle_append hr hdis (Or.inr ?_), ?_⟩
  · simp [r]
  · rw [SimpleGraph.Walk.length_append]
    simp [r, SimpleGraph.Walk.length_cons]

/-- A root-internal opposite-port residual path splits into two simple
positive-length excursions. Each excursion closes with two endpoint/root-port
edges into a simple cycle of its length plus two, including triangles.
@isnad1 id=ex.8h8v.s8.aa6021404d26 from=translated src=- shape=04e4ba1a vocab=8416ea93
-/
theorem cross_residual_root_internal_excursion_cycles
    {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] [DecidableRel G.Adj]
    {r x y u v : V} {p : G.Walk u v}
    (hrx : G.Adj r x) (hry : G.Adj r y)
    (hp : p.IsPath)
    (havoid : ∀ w, w ∈ p.support → w ≠ x ∧ w ≠ y)
    (hru : u ≠ r) (hrv : v ≠ r)
    (hrp : r ∈ p.support)
    (hadj : (G.Adj x u ∧ G.Adj y v) ∨
      (G.Adj y u ∧ G.Adj x v)) :
    ∃ a : G.Walk u r, ∃ b : G.Walk r v,
      a.IsPath ∧ b.IsPath ∧ a.append b = p ∧
      a.support ⊆ p.support ∧ b.support ⊆ p.support ∧
      a.length + b.length = p.length ∧
      0 < a.length ∧ 0 < b.length ∧
      r ∉ a.support.dropLast ∧ r ∉ b.support.tail ∧
      (∃ c : G.Walk u u, c.IsCycle ∧ c.length = a.length + 2) ∧
      (∃ c : G.Walk v v, c.IsCycle ∧ c.length = b.length + 2) := by
  obtain ⟨a, b, ha, hb, hab, hasub, hbsub, hlen, hapos, hbpos,
      hroota, hrootb⟩ := residual_path_root_internal_split hp hru hrv hrp
  have hxa : x ∉ a.support := by
    intro hx
    exact (havoid x (hasub hx)).1 rfl
  have hya : y ∉ a.support := by
    intro hy
    exact (havoid y (hasub hy)).2 rfl
  have hxb : x ∉ b.support := by
    intro hx
    exact (havoid x (hbsub hx)).1 rfl
  have hyb : y ∉ b.support := by
    intro hy
    exact (havoid y (hbsub hy)).2 rfl
  have hxb' : x ∉ b.reverse.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hxb
  have hyb' : y ∉ b.reverse.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hyb
  rcases hadj with ⟨hxu, hyv⟩ | ⟨hyu, hxv⟩
  · refine ⟨a, b, ha, hb, hab, hasub, hbsub, hlen, hapos, hbpos,
      hroota, hrootb, ?_, ?_⟩
    · exact endpoint_fan_cycle_certificate_of_pos ha hxu hrx.symm hxa hru hapos
    · obtain ⟨c, hc, hclen⟩ := endpoint_fan_cycle_certificate_of_pos
        hb.reverse hyv hry.symm hyb' hrv (by simpa using hbpos)
      exact ⟨c, hc, by simpa [SimpleGraph.Walk.length_reverse] using hclen⟩
  · refine ⟨a, b, ha, hb, hab, hasub, hbsub, hlen, hapos, hbpos,
      hroota, hrootb, ?_, ?_⟩
    · exact endpoint_fan_cycle_certificate_of_pos ha hyu hry.symm hya hru hapos
    · obtain ⟨c, hc, hclen⟩ := endpoint_fan_cycle_certificate_of_pos
        hb.reverse hxv hrx.symm hxb' hrv (by simpa using hbpos)
      exact ⟨c, hc, by simpa [SimpleGraph.Walk.length_reverse] using hclen⟩

end Erdos64

namespace Erdos64

universe u

/-- In a minimal dyadic-free counterexample, a root-internal residual split
produces two endpoint/root-port excursion cycles, and neither resulting cycle
length can be dyadic.
@isnad1 id=ex.9h8v.s8.0b9b39b5301a from=translated src=- shape=c0f525b0 vocab=2f313961
-/
theorem MinimalCounterexample.cross_residual_root_internal_excursions_nondyadic
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    {r x y u v : V} {p : G.Walk u v}
    (hrx : G.Adj r x) (hry : G.Adj r y)
    (hp : p.IsPath)
    (havoid : ∀ w, w ∈ p.support → w ≠ x ∧ w ≠ y)
    (hru : u ≠ r) (hrv : v ≠ r)
    (hrp : r ∈ p.support)
    (hadj : (G.Adj x u ∧ G.Adj y v) ∨
      (G.Adj y u ∧ G.Adj x v)) :
    ∃ a : G.Walk u r, ∃ b : G.Walk r v,
      a.IsPath ∧ b.IsPath ∧ a.append b = p ∧
      a.support ⊆ p.support ∧ b.support ⊆ p.support ∧
      a.length + b.length = p.length ∧
      0 < a.length ∧ 0 < b.length ∧
      r ∉ a.support.dropLast ∧ r ∉ b.support.tail ∧
      (∀ j : ℕ, 2 ≤ j → a.length + 2 ≠ 2 ^ j) ∧
      (∀ j : ℕ, 2 ≤ j → b.length + 2 ≠ 2 ^ j) := by
  obtain ⟨a, b, ha, hb, hab, hasub, hbsub, hlen, hapos, hbpos,
      hroota, hrootb, hca, hcb⟩ :=
    cross_residual_root_internal_excursion_cycles
      hrx hry hp havoid hru hrv hrp hadj
  refine ⟨a, b, ha, hb, hab, hasub, hbsub, hlen, hapos, hbpos,
    hroota, hrootb, ?_, ?_⟩
  · intro j hj hpow
    obtain ⟨c, hc, hclen⟩ := hca
    apply M.isCounterexample.2
    exact ⟨j, u, c, hj, hc, hclen.trans hpow⟩
  · intro j hj hpow
    obtain ⟨c, hc, hclen⟩ := hcb
    apply M.isCounterexample.2
    exact ⟨j, v, c, hj, hc, hclen.trans hpow⟩
