import Tengoku.Erdos64.Erdos64.ResidualPathRootSplit
import Tengoku.Erdos64.Erdos64.RootDeletedTwoPortExtraction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A walk that avoids every root attachment of a closed side cannot leave
that side. Only the forward implication of exact two-port attachment is
needed; simplicity and minimality are unnecessary.-/
theorem walk_support_in_side_of_avoiding_ports
    {V : Type u} {G : SimpleGraph V}
    {D : Finset V} {r x y u v : V} (p : G.Walk u v)
    (hu : u ∈ D)
    (hboundary : ∀ a, a ∈ D → ∀ b, b ∉ D → G.Adj a b → b = r)
    (hports : ∀ a, a ∈ D → G.Adj a r → a = x ∨ a = y)
    (havoid : ∀ a, a ∈ p.support → a ≠ x ∧ a ≠ y) :
    ∀ a, a ∈ p.support → a ∈ D := by
  induction p with
  | nil =>
      intro a ha
      simpa using (List.mem_singleton.mp ha) ▸ hu
  | @cons a b c hab q ih =>
      have hb : b ∈ D := by
        by_contra hb
        have hbr := hboundary a hu b hb hab
        have har : G.Adj a r := hbr ▸ hab
        have haavoid := havoid a (by simp)
        rcases hports a hu har with hax | hay
        · exact haavoid.1 hax
        · exact haavoid.2 hay
      have hqavoid : ∀ z, z ∈ q.support → z ≠ x ∧ z ≠ y := by
        intro z hz
        exact havoid z (List.mem_cons_of_mem _ hz)
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hu
      · exact ih hb hqavoid z hz

/-- Opposite-port residual endpoints belong to the port side, and avoiding
its only two root attachments forces the entire residual walk to stay there.
In particular, the root-internal excursion branch is impossible.-/
theorem cross_residual_in_exact_two_port_side
    {V : Type u} {G : SimpleGraph V}
    {D : Finset V} {r x y u v : V} {p : G.Walk u v}
    (hr : r ∉ D) (hx : x ∈ D) (hy : y ∈ D)
    (hboundary : ∀ a, a ∈ D → ∀ b, b ∉ D → G.Adj a b → b = r)
    (hports : ∀ a, a ∈ D → G.Adj a r → a = x ∨ a = y)
    (hur : u ≠ r) (hvr : v ≠ r)
    (havoid : ∀ a, a ∈ p.support → a ≠ x ∧ a ≠ y)
    (hadj : (G.Adj x u ∧ G.Adj y v) ∨ (G.Adj y u ∧ G.Adj x v)) :
    u ∈ D ∧ v ∈ D ∧ (∀ a, a ∈ p.support → a ∈ D) ∧ r ∉ p.support := by
  have hneighbor : ∀ a, a ∈ D → ∀ b, b ≠ r → G.Adj a b → b ∈ D := by
    intro a ha b hbr hab
    by_contra hb
    exact hbr (hboundary a ha b hb hab)
  have huv : u ∈ D ∧ v ∈ D := by
    rcases hadj with ⟨hxu, hyv⟩ | ⟨hyu, hxv⟩
    · exact ⟨hneighbor x hx u hur hxu, hneighbor y hy v hvr hyv⟩
    · exact ⟨hneighbor y hy u hur hyu, hneighbor x hx v hvr hxv⟩
  have hinside := walk_support_in_side_of_avoiding_ports p huv.1 hboundary hports havoid
  exact ⟨huv.1, huv.2, hinside, fun hroot => hr (hinside r hroot)⟩

/-- A closed exact two-port side with nonadjacent ports in a minimal
counterexample contains a simple dyadic port-to-port path. The root-avoidance
premise is proved from the boundary, rather than supplied as an assumption.
Closing this path through the root has length `2^k + 2`, not `2^k`.-/
theorem MinimalCounterexample.exact_two_port_side_dyadic_path
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
    ∃ k : ℕ, ∃ q : G.Walk x y,
      2 ≤ k ∧ q.IsPath ∧ q.length = 2 ^ k ∧
      (∀ a, a ∈ q.support → a ∈ D) ∧ r ∉ q.support := by
  obtain ⟨k, u, v, p, hk, hp, havoid, hlen, hadj⟩ :=
    M.shared_root_quotient_residual_path hrx hry hxy hnadj hroot_degree
  have hur : u ≠ r := hadj.elim (fun h => h.2.2.1) (fun h => h.2.2.1)
  have hvr : v ≠ r := hadj.elim (fun h => h.2.2.2) (fun h => h.2.2.2)
  have hattach : (G.Adj x u ∧ G.Adj y v) ∨ (G.Adj y u ∧ G.Adj x v) :=
    hadj.imp (fun h => ⟨h.1, h.2.1⟩) (fun h => ⟨h.1, h.2.1⟩)
  obtain ⟨_, _, _, hroot⟩ := cross_residual_in_exact_two_port_side
    hr hx hy hboundary hports hur hvr havoid hattach
  have hpath := cross_residual_path_to_dyadic_port_path
    hrx hry hxy hp havoid hroot hlen hattach
  have hnormalized : ∃ q : G.Walk x y,
      q.IsPath ∧ r ∉ q.support ∧ q.length = 2 ^ k := by
    rcases hpath with hforward | ⟨q, hq, hqr, hqlen⟩
    · exact hforward
    · exact ⟨q.reverse, hq.reverse, by simpa using hqr, by simpa using hqlen⟩
  obtain ⟨q, hq, hqr, hqlen⟩ := hnormalized
  exact ⟨k, q, hk, hq, hqlen,
    SimpleGraph.Walk.IsPath.support_subset_of_boundary_avoiding_root
      hq hx hqr hboundary, hqr⟩

/-- An attachment finset of cardinality two exposes the exact two-port
condition needed by the residual closure theorem.-/
theorem rootDeletedComponent_twoPort_attachment_exact
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (r : V)
    (C : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hcard : (rootDeletedComponentAttachments G r C).card = 2) :
    ∃ x y : V,
      x ∈ rootDeletedComponentCarrier G r C ∧
      y ∈ rootDeletedComponentCarrier G r C ∧
      x ≠ y ∧ G.Adj r x ∧ G.Adj r y ∧
      (∀ a, a ∈ rootDeletedComponentCarrier G r C →
        G.Adj a r → a = x ∨ a = y) := by
  classical
  obtain ⟨x, y, hxy, hset⟩ :=
    Finset.card_eq_two.mp hcard
  have hxatt : x ∈ rootDeletedComponentAttachments G r C := by
    rw [hset]
    simp [hxy]
  have hyatt : y ∈ rootDeletedComponentAttachments G r C := by
    rw [hset]
    simp
  have hx := Finset.mem_filter.mp hxatt
  have hy := Finset.mem_filter.mp hyatt
  refine ⟨x, y, hx.2, hy.2, hxy, ?_, ?_, ?_⟩
  · exact (G.mem_neighborFinset r x).mp hx.1
  · exact (G.mem_neighborFinset r y).mp hy.1
  · intro a ha har
    have haatt : a ∈ rootDeletedComponentAttachments G r C := by
      apply Finset.mem_filter.mpr
      exact ⟨(G.mem_neighborFinset r a).mpr har.symm, ha⟩
    rw [hset] at haatt
    simpa only [Finset.mem_insert, Finset.mem_singleton] using haatt

/-- A root-deleted component feeds the exact-side residual theorem when its
attachment finset has cardinality two, the root has degree at least four,
and its two ports are nonadjacent. These are supplied hypotheses; component
closure and avoidance of the root are derived in the proof.-/
theorem MinimalCounterexample.rootDeleted_twoPort_component_dyadic_path
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hcard : (rootDeletedComponentAttachments G r C).card = 2)
    (hroot_degree : 4 ≤ G.degree r)
    (hnonadj : ∀ a b,
      a ∈ rootDeletedComponentCarrier G r C →
      b ∈ rootDeletedComponentCarrier G r C →
      G.Adj r a → G.Adj r b → a ≠ b → ¬ G.Adj a b) :
    ∃ x y : V, ∃ k : ℕ, ∃ q : G.Walk x y,
      x ∈ rootDeletedComponentCarrier G r C ∧
      y ∈ rootDeletedComponentCarrier G r C ∧
      x ≠ y ∧ G.Adj r x ∧ G.Adj r y ∧
      2 ≤ k ∧ q.IsPath ∧ q.length = 2 ^ k ∧
      (∀ a, a ∈ q.support →
        a ∈ rootDeletedComponentCarrier G r C) ∧ r ∉ q.support := by
  obtain ⟨x, y, hx, hy, hxy, hrx, hry, hports⟩ :=
    rootDeletedComponent_twoPort_attachment_exact r C hcard
  have hboundary :
      ∀ a, a ∈ rootDeletedComponentCarrier G r C →
        ∀ b, b ∉ rootDeletedComponentCarrier G r C →
          G.Adj a b → b = r := by
    intro a ha b hb hab
    rcases (rootDeletedComponent_boundary r M.isConnected C).1 a ha b hab with
      hbC | hbr
    · exact (hb hbC).elim
    · exact hbr
  have hxy_nonadj := hnonadj x y hx hy hrx hry hxy
  obtain ⟨k, q, hk, hq, hqlen, hinside, hroot⟩ :=
    M.exact_two_port_side_dyadic_path
      (rootDeletedComponentCarrier G r C) r x y
      (rootDeletedComponentCarrier_nonempty_not_mem G r C).2
      hx hy hrx hry hxy hxy_nonadj hroot_degree hboundary hports
  exact ⟨x, y, k, q, hx, hy, hxy, hrx, hry, hk, hq, hqlen,
    hinside, hroot⟩

end Erdos64
