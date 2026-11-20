import Tengoku.Erdos64.Erdos64.PortSuppressionOddCycle
import Tengoku.Erdos64.Erdos64.MinimalCounterexampleUniqueCut
import Tengoku.Erdos64.Erdos64.RootDeletedBalancedSides
import Tengoku.Erdos64.Erdos64.ExactTwoPortResidual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Every specified cubic port of a sufficiently small closed two-port side
lies on a cycle, contained in that side, one edge longer than a power of two.-/
theorem MinimalCounterexample.exact_two_cubic_port_side_dyadic_successor_cycle
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (D : Finset V) (r x y : V)
    (hr : r ∉ D) (hx : x ∈ D) (hy : y ∈ D) (hxy : x ≠ y)
    (hboundary : ∀ a, a ∈ D → ∀ b, b ∉ D → G.Adj a b → b = r)
    (hexact : ∀ a, a ∈ D → (G.Adj a r ↔ a = x ∨ a = y))
    (hcubic : G.degree x = 3 ∧ G.degree y = 3)
    (hsize : 2 * D.card - 3 < Fintype.card V) :
    ∃ k : ℕ, ∃ c : G.Walk x x,
      1 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 1 ∧
      (∀ a, a ∈ c.support → a ∈ D) ∧ r ∉ c.support := by
  classical
  obtain ⟨hxdeg, hydeg, hretained, _⟩ :=
    two_cubic_ports_boundary_accounting D r x y hr ⟨hx, hy, hxy⟩
      hboundary hexact hcubic
  let H := G.induce (↑D : Set V)
  let x' : (↑D : Set V) := ⟨x, hx⟩
  let y' : (↑D : Set V) := ⟨y, hy⟩
  have hxy' : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
  have hx' : H.degree x' = 2 := by
    rw [degree_induce_coeFinset_eq_internalDegree]
    exact hxdeg
  have hy' : 2 ≤ H.degree y' := by
    rw [degree_induce_coeFinset_eq_internalDegree]
    exact hydeg.ge
  have hother : ∀ v, v ≠ x' → v ≠ y' → 3 ≤ H.degree v := by
    intro v hvx hvy
    rw [degree_induce_coeFinset_eq_internalDegree,
      hretained v.1 v.2 (fun h => hvx (Subtype.ext h))
        (fun h => hvy (Subtype.ext h))]
    exact degree_ge_three_of_minDegree_ge_three G M.isCounterexample.1 v.1
  have hno : ¬ HasPowerOfTwoCycle H :=
    not_hasPowerOfTwoCycle_induce_of_not_hasPowerOfTwoCycle M.isCounterexample.2
  have hsmall : 2 * Fintype.card (↑D : Set V) - 3 < Fintype.card V := by
    simpa using hsize
  obtain ⟨k, c, hk, hc, hlen⟩ :=
    M.two_defect_port_dyadic_successor_cycle x' y' hxy' hx' hy' hother hno hsmall
  let e : H ↪g G := SimpleGraph.Embedding.induce (↑D : Set V)
  let q : G.Walk x x := c.map e.toHom
  have hq : q.IsCycle := hc.map e.injective
  have hinside : ∀ a, a ∈ q.support → a ∈ D := by
    intro a ha
    change a ∈ (c.map e.toHom).support at ha
    rw [SimpleGraph.Walk.support_map] at ha
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
    exact v.2
  refine ⟨k, q, hk, hq, ?_, hinside, fun h => hr (hinside r h)⟩
  change (c.map e.toHom).length = 2 ^ k + 1
  rw [SimpleGraph.Walk.length_map]
  exact hlen

/-- Each attachment of either native cut component lies on a side-contained
cycle of length `2^k + 1`. The cycles supplied for different attachments need
not be distinct.-/
theorem EdgeMinimalCounterexample.rootDeleted_cut_port_dyadic_successor_cycle
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : EdgeMinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hCD : C ≠ D) (x : V)
    (hx : x ∈ rootDeletedComponentCarrier G r C) (hrx : G.Adj r x) :
    ∃ k : ℕ, ∃ c : G.Walk x x,
      1 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 1 ∧
      (∀ a, a ∈ c.support → a ∈ rootDeletedComponentCarrier G r C) ∧
      r ∉ c.support := by
  classical
  let := Fintype.ofFinite ((G.induce {v : V | v ≠ r}).ConnectedComponent)
  obtain ⟨_, _, hcard, _, _, hcubic⟩ :=
    M.rootDeleted_two_components_exact_balanced_cubic r C D hCD
  obtain ⟨a, b, ha, hb, hab, hra, hrb, hports⟩ :=
    rootDeletedComponent_twoPort_attachment_exact r C hcard
  have hpartner : ∃ y, y ∈ rootDeletedComponentCarrier G r C ∧ x ≠ y ∧
      G.Adj r y ∧
      (∀ v, v ∈ rootDeletedComponentCarrier G r C →
        G.Adj v r → v = x ∨ v = y) := by
    rcases hports x hx hrx.symm with rfl | rfl
    · exact ⟨b, hb, hab, hrb, hports⟩
    · refine ⟨a, ha, hab.symm, hra, ?_⟩
      intro v hv hvr
      exact (hports v hv hvr).symm
  obtain ⟨y, hy, hxy, hry, hxyports⟩ := hpartner
  have hexact : ∀ v, v ∈ rootDeletedComponentCarrier G r C →
      (G.Adj v r ↔ v = x ∨ v = y) := by
    intro v hv
    refine ⟨hxyports v hv, ?_⟩
    rintro (rfl | rfl)
    · exact hrx.symm
    · exact hry.symm
  have hboundary : ∀ a, a ∈ rootDeletedComponentCarrier G r C →
      ∀ b, b ∉ rootDeletedComponentCarrier G r C → G.Adj a b → b = r := by
    intro a ha b hb hab
    rcases (rootDeletedComponent_boundary r M.vertexMinimal.isConnected C).1
      a ha b hab with hbC | hbr
    · exact (hb hbC).elim
    · exact hbr
  have horder := M.vertexMinimal.rootDeleted_two_components_order r C D hCD
  exact M.vertexMinimal.exact_two_cubic_port_side_dyadic_successor_cycle
    (rootDeletedComponentCarrier G r C) r x y
    (rootDeletedComponentCarrier_nonempty_not_mem G r C).2 hx hy hxy
    hboundary hexact ⟨hcubic x hrx, hcubic y hry⟩ (by omega)

end Erdos64
