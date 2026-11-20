import Tengoku.Erdos64.Erdos64.AdjacentTwoPortNonbipartite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Contracting a triangle-free edge leaves at least three neighbors at the
new vertex when the original graph has minimum degree at least three.
@isnad1 id=le.3h4v.s7.c08fbfdc423e from=translated src=- shape=b895ce35 vocab=2b1cb606
-/
theorem quotient_root_degree_ge_three_of_adj_no_common
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b) (hmin : 3 ≤ G.minDegree)
    (hcommon : ∀ z, ¬ (G.Adj a z ∧ G.Adj b z)) :
    3 ≤ (terminalQuotientGraph G a b).degree none := by
  classical
  let A := (G.neighborFinset a).erase b
  let B := (G.neighborFinset b).erase a
  have hA : 1 < A.card := by
    have hm := degree_ge_three_of_minDegree_ge_three G hmin a
    simp only [A, Finset.card_erase_of_mem ((G.mem_neighborFinset a b).mpr hab),
      SimpleGraph.card_neighborFinset_eq_degree]
    omega
  have hB : B.Nonempty := by
    have hm := degree_ge_three_of_minDegree_ge_three G hmin b
    apply Finset.card_pos.mp
    simp only [B, Finset.card_erase_of_mem ((G.mem_neighborFinset b a).mpr hab.symm),
      SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hA
  obtain ⟨z, hz⟩ := hB
  have hxa : G.Adj a x := (G.mem_neighborFinset a x).mp (Finset.mem_erase.mp hx).2
  have hya : G.Adj a y := (G.mem_neighborFinset a y).mp (Finset.mem_erase.mp hy).2
  have hzb : G.Adj b z := (G.mem_neighborFinset b z).mp (Finset.mem_erase.mp hz).2
  have hxz : x ≠ z := by
    rintro rfl
    exact hcommon x ⟨hxa, hzb⟩
  have hyz : y ≠ z := by
    rintro rfl
    exact hcommon y ⟨hya, hzb⟩
  let xx : Internal a b := ⟨x, hxa.ne.symm, (Finset.mem_erase.mp hx).1⟩
  let yy : Internal a b := ⟨y, hya.ne.symm, (Finset.mem_erase.mp hy).1⟩
  let zz : Internal a b := ⟨z, (Finset.mem_erase.mp hz).1, hzb.ne.symm⟩
  have hthree : ({some xx, some yy, some zz} : Finset (QuotientVertex a b)).card = 3 := by
    simp [xx, yy, zz, hxy, hxz, hyz]
  have hsub : ({some xx, some yy, some zz} : Finset (QuotientVertex a b)) ⊆
      (terminalQuotientGraph G a b).neighborFinset none := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (Or.inl hxa)
    · exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (Or.inl hya)
    · exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (Or.inr hzb)
  have h := Finset.card_le_card hsub
  simpa only [hthree, SimpleGraph.card_neighborFinset_eq_degree] using h

private theorem path_extend_fresh_terminals
    {V : Type u} {G : SimpleGraph V} {a b x y : V}
    (hab : a ≠ b) (p : G.Walk x y) (hp : p.IsPath)
    (havoid : ∀ v, v ∈ p.support → v ≠ a ∧ v ≠ b)
    (hax : G.Adj a x) (hby : G.Adj b y) :
    ∃ q : G.Walk a b, q.IsPath ∧ q.length = p.length + 2 := by
  have ha : a ∉ p.support := fun h => (havoid a h).1 rfl
  have hb : b ∉ p.support := fun h => (havoid b h).2 rfl
  let q : G.Walk a b := .cons hax (p.concat hby.symm)
  refine ⟨q, ?_, ?_⟩
  · apply SimpleGraph.Walk.IsPath.cons (hp.concat hb hby.symm)
    simpa only [SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton, not_or] using And.intro ha hab
  · simp [q, Nat.add_assoc]

/-- Every adjacent pair in a globally vertex-minimal counterexample has a
simple alternative path of power-of-two length. A triangle gives length two;
otherwise contraction of the edge forces the path with exponent at least two.
This is the path form of Ducoffe--Dumitru, arXiv:2609.28594v1, Lemma 2.1.
@isnad1 id=ex.2h4v.s6.a1ee37ff4812 from=translated src=- shape=6ea15c9d vocab=30b4ca06
-/
theorem MinimalCounterexample.adjacent_dyadic_alternative_path
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) {a b : V} (hab : G.Adj a b) :
    ∃ k : ℕ, ∃ q : G.Walk a b,
      1 ≤ k ∧ q.IsPath ∧ q.length = 2 ^ k ∧ s(a, b) ∉ q.edges := by
  classical
  have hpath : ∃ k : ℕ, ∃ q : G.Walk a b,
      1 ≤ k ∧ q.IsPath ∧ q.length = 2 ^ k := by
    by_cases htriangle : ∃ z, G.Adj a z ∧ G.Adj b z
    · obtain ⟨z, haz, hbz⟩ := htriangle
      let q : G.Walk a b := .cons haz (.cons hbz.symm .nil)
      refine ⟨1, q, by omega, ?_, rfl⟩
      apply SimpleGraph.Walk.IsPath.cons (SimpleGraph.Walk.IsPath.of_adj hbz.symm)
      simp [haz.ne, hab.ne]
    · have hcommon : ∀ z, ¬ (G.Adj a z ∧ G.Adj b z) :=
        fun z hz => htriangle ⟨z, hz⟩
      have hroot := quotient_root_degree_ge_three_of_adj_no_common
        hab M.isCounterexample.1 hcommon
      obtain ⟨k, x, y, p, hk, hp, havoid, hlen, hcross⟩ :=
        M.terminal_cross_path_of_root_and_common hab.ne hroot
          (fun z _ _ hz => (hcommon z hz).elim)
      rcases hcross with ⟨hax, hby⟩ | ⟨hbx, hay⟩
      · obtain ⟨q, hq, hqlen⟩ := path_extend_fresh_terminals hab.ne p hp havoid hax hby
        exact ⟨k, q, by omega, hq, hqlen.trans hlen⟩
      · obtain ⟨q, hq, hqlen⟩ := path_extend_fresh_terminals hab.ne.symm p hp
          (fun v hv => (havoid v hv).symm) hbx hay
        refine ⟨k, q.reverse, by omega, hq.reverse, ?_⟩
        simpa only [SimpleGraph.Walk.length_reverse] using hqlen.trans hlen
  obtain ⟨k, q, hk, hq, hqlen⟩ := hpath
  refine ⟨k, q, hk, hq, hqlen, ?_⟩
  intro he
  have hone := hq.length_eq_one_of_mem_edges he
  have htwo : 2 ≤ 2 ^ k := by
    calc
      2 = 2 ^ 1 := by rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  omega

/-- Every specified edge lies on a simple cycle of length one more than a
power of two. This formalizes Ducoffe--Dumitru Lemma 2.1 using vertex
minimality alone, and applies also when there is no cut vertex.
@isnad1 id=ex.2h4v.s6.1a5968207e72 from=translated src=- shape=711eca99 vocab=ef29ac62
-/
theorem MinimalCounterexample.edge_dyadic_successor_cycle
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) {a b : V} (hab : G.Adj a b) :
    ∃ k : ℕ, ∃ c : G.Walk a a,
      1 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 1 ∧ s(a, b) ∈ c.edges := by
  obtain ⟨k, p, hk, hp, hlen, hedge⟩ := M.adjacent_dyadic_alternative_path hab
  let c := SimpleGraph.Walk.cons hab p.reverse
  refine ⟨k, c, hk, ?_, ?_, ?_⟩
  · apply (SimpleGraph.Walk.cons_isCycle_iff p.reverse hab).mpr
    exact ⟨hp.reverse, by simpa using hedge⟩
  · simpa only [c, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_reverse] using
      congrArg (fun n : ℕ => n + 1) hlen
  · simp [c]

/-- Global vertex minimality excludes bipartite counterexamples: an edge
and its forced even alternative path have opposite parity. This is not a
claim that an arbitrary bipartite minimum-degree-three graph is solved.
@isnad1 id=not.1h2v.s4.bc0006464003 from=translated src=- shape=359c698b vocab=ada2ec29
-/
theorem MinimalCounterexample.not_isBipartite
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) : ¬ G.IsBipartite := by
  obtain ⟨v, c, hc⟩ := exists_simpleCycle_of_minDegree_ge_three G M.isCounterexample.1
  cases c with
  | nil => exact (SimpleGraph.Walk.not_isCycle_nil hc).elim
  | cons hab p =>
    obtain ⟨k, q, hk, _, hlen, _⟩ := M.adjacent_dyadic_alternative_path hab
    have heven : Even q.length := by
      rw [hlen]
      exact (show Even (2 : ℕ) by decide).pow_of_ne_zero (by omega)
    exact not_isBipartite_of_opposite_parity_routes hab.toWalk q (by simp) heven

end Erdos64
