import Tengoku.Erdos64.Erdos64.TwoPortEdgeCompletion
import Tengoku.Erdos64.Erdos64.AddedEdgeCyclePath
import Tengoku.Erdos64.Erdos64.ExactTwoPortResidual
import Tengoku.Erdos64.Erdos64.TwoPortRouteParity
import Tengoku.Erdos64.Erdos64.RootDeletedBalancedSides

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Adding the missing port edge repairs the induced side's minimum degree.
Minimality forces a dyadic cycle in that smaller completion. Removing its
synthetic edge gives an original port path one edge short of a power of two.
@isnad1 id=ex.10h6v.s8.50a83076f8fa from=translated src=- shape=8e6f0156 vocab=02e8edfc
-/
theorem MinimalCounterexample.exact_two_port_side_pow_two_sub_one_path
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (D : Finset V) (r x y : V)
    (hr : r ∉ D) (hx : x ∈ D) (hy : y ∈ D)
    (hrx : G.Adj r x) (hry : G.Adj r y)
    (hxy : x ≠ y) (hnadj : ¬ G.Adj x y)
    (hboundary : ∀ a, a ∈ D → ∀ b, b ∉ D → G.Adj a b → b = r)
    (hports : ∀ a, a ∈ D → G.Adj a r → a = x ∨ a = y) :
    ∃ j : ℕ, ∃ p : G.Walk x y,
      2 ≤ j ∧ p.IsPath ∧ p.length + 1 = 2 ^ j ∧
      (∀ a, a ∈ p.support → a ∈ D) ∧ r ∉ p.support := by
  classical
  have hexact : ∀ a, a ∈ D → (G.Adj a r ↔ a = x ∨ a = y) := by
    intro a ha
    refine ⟨hports a ha, ?_⟩
    rintro (rfl | rfl)
    · exact hrx.symm
    · exact hry.symm
  have hyes := M.two_port_edge_completion_has_dyadic_cycle
    D r x y hr hx hy hxy hnadj hboundary hexact
  have hno : ¬ HasPowerOfTwoCycle (G.induce (↑D : Set V)) :=
    not_hasPowerOfTwoCycle_induce_of_not_hasPowerOfTwoCycle M.isCounterexample.2
  obtain ⟨j, p, hj, hp, hlen⟩ := added_edge_dyadic_cycle_path hno hyes
  let e : G.induce (↑D : Set V) ↪g G := SimpleGraph.Embedding.induce (↑D : Set V)
  let q : G.Walk x y := p.map e.toHom
  have hq : q.IsPath := hp.map e.injective
  have hinside : ∀ a, a ∈ q.support → a ∈ D := by
    intro a ha
    change a ∈ (p.map e.toHom).support at ha
    rw [SimpleGraph.Walk.support_map] at ha
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp ha
    exact z.property
  refine ⟨j, q, hj, hq, ?_, hinside, fun hroot => hr (hinside r hroot)⟩
  change (p.map e.toHom).length + 1 = 2 ^ j
  rw [SimpleGraph.Walk.length_map]
  exact hlen

/-- The same named ports carry genuinely distinct odd and even simple routes.
Both routes stay in the supplied side. No mutual disjointness is asserted.
@isnad1 id=ex.11h6v.s8.cb186c67f6dc from=translated src=- shape=d96b8590 vocab=6016902f
-/
theorem MinimalCounterexample.exact_two_port_side_distinct_routes
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (D : Finset V) (r x y : V)
    (hr : r ∉ D) (hx : x ∈ D) (hy : y ∈ D)
    (hrx : G.Adj r x) (hry : G.Adj r y)
    (hxy : x ≠ y) (hnadj : ¬ G.Adj x y)
    (hroot_degree : 4 ≤ G.degree r)
    (hboundary : ∀ a, a ∈ D → ∀ b, b ∉ D → G.Adj a b → b = r)
    (hports : ∀ a, a ∈ D → G.Adj a r → a = x ∨ a = y) :
    ∃ j k : ℕ, ∃ p q : G.Walk x y,
      2 ≤ j ∧ 2 ≤ k ∧ p.IsPath ∧ q.IsPath ∧
      p.length + 1 = 2 ^ j ∧ q.length = 2 ^ k ∧
      Odd p.length ∧ Even q.length ∧ p.length ≠ q.length ∧ p ≠ q ∧
      (∀ a, a ∈ p.support → a ∈ D) ∧
      (∀ a, a ∈ q.support → a ∈ D) ∧ r ∉ p.support ∧ r ∉ q.support := by
  obtain ⟨j, p, hj, hp, hplen, hpinside, hpr⟩ :=
    M.exact_two_port_side_pow_two_sub_one_path
      D r x y hr hx hy hrx hry hxy hnadj hboundary hports
  obtain ⟨k, q, hk, hq, hqlen, hqinside, hqr⟩ :=
    M.exact_two_port_side_dyadic_path
      D r x y hr hx hy hrx hry hxy hnadj hroot_degree hboundary hports
  obtain ⟨hodd, heven, hlength_ne, hpq, _⟩ :=
    twoPort_routes_parity_of_dyadic_completion p q hj hk hplen hqlen
  exact ⟨j, k, p, q, hj, hk, hp, hq, hplen, hqlen, hodd, heven,
    hlength_ne, hpq, hpinside, hqinside, hpr, hqr⟩

/-- Opposite-parity routes lie in the side itself, so even that induced graph
cannot be bipartite. This is a restriction on a putative counterexample,
not a contradiction in an arbitrary nonbipartite side.
@isnad1 id=not.11h6v.s7.b6e9de1864ee from=translated src=- shape=e18c0ad9 vocab=393b6a43
-/
theorem MinimalCounterexample.exact_two_port_side_not_isBipartite
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (D : Finset V) (r x y : V)
    (hr : r ∉ D) (hx : x ∈ D) (hy : y ∈ D)
    (hrx : G.Adj r x) (hry : G.Adj r y)
    (hxy : x ≠ y) (hnadj : ¬ G.Adj x y)
    (hroot_degree : 4 ≤ G.degree r)
    (hboundary : ∀ a, a ∈ D → ∀ b, b ∉ D → G.Adj a b → b = r)
    (hports : ∀ a, a ∈ D → G.Adj a r → a = x ∨ a = y) :
    ¬ (G.induce (↑D : Set V)).IsBipartite := by
  obtain ⟨j, k, p, q, hj, hk, _, _, hplen, hqlen, _, _, _, _,
      hpinside, hqinside, _, _⟩ :=
    M.exact_two_port_side_distinct_routes
      D r x y hr hx hy hrx hry hxy hnadj hroot_degree hboundary hports
  let p' := p.induce (↑D : Set V) hpinside
  let q' := q.induce (↑D : Set V) hqinside
  have hp'len : p'.length = p.length := by
    have h := congrArg (fun w : G.Walk x y => w.length) (p.map_induce hpinside)
    exact (SimpleGraph.Walk.length_map
      (SimpleGraph.Embedding.induce (↑D : Set V)).toHom p').symm.trans h
  have hq'len : q'.length = q.length := by
    have h := congrArg (fun w : G.Walk x y => w.length) (q.map_induce hqinside)
    exact (SimpleGraph.Walk.length_map
      (SimpleGraph.Embedding.induce (↑D : Set V)).toHom q').symm.trans h
  exact (twoPort_routes_parity_of_dyadic_completion p' q' hj hk
    (hp'len ▸ hplen) (hq'len ▸ hqlen)).2.2.2.2

/-- At a native cut, balance supplies the degree and attachment counts.
If the two ports of one component are nonadjacent, that component's induced
graph cannot be bipartite. No edge-minimality assumption is needed.
@isnad1 id=not.3h5v.s7.ef4f9bfbf574 from=translated src=- shape=21677947 vocab=2ee97499
-/
theorem MinimalCounterexample.rootDeleted_cut_nonadjacent_side_not_isBipartite
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hCD : C ≠ D)
    (hnonadj : ∀ a b,
      a ∈ rootDeletedComponentCarrier G r C →
      b ∈ rootDeletedComponentCarrier G r C →
      G.Adj r a → G.Adj r b → a ≠ b → ¬ G.Adj a b) :
    ¬ (G.induce (↑(rootDeletedComponentCarrier G r C) : Set V)).IsBipartite := by
  classical
  letI := Fintype.ofFinite ((G.induce {v : V | v ≠ r}).ConnectedComponent)
  obtain ⟨_, _, hcard, _, hdegree⟩ :=
    M.rootDeleted_two_components_exact_balanced r C D hCD
  obtain ⟨x, y, hx, hy, hxy, hrx, hry, hports⟩ :=
    rootDeletedComponent_twoPort_attachment_exact r C hcard
  have hboundary : ∀ a, a ∈ rootDeletedComponentCarrier G r C →
      ∀ b, b ∉ rootDeletedComponentCarrier G r C → G.Adj a b → b = r := by
    intro a ha b hb hab
    rcases (rootDeletedComponent_boundary r M.isConnected C).1 a ha b hab with
      hbC | hbr
    · exact (hb hbC).elim
    · exact hbr
  exact M.exact_two_port_side_not_isBipartite
    (rootDeletedComponentCarrier G r C) r x y
    (rootDeletedComponentCarrier_nonempty_not_mem G r C).2
    hx hy hrx hry hxy (hnonadj x y hx hy hrx hry hxy)
    (by omega) hboundary hports

end Erdos64
