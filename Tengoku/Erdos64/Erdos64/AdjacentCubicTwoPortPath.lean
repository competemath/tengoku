import Tengoku.Erdos64.Erdos64.MinimalCounterexampleBridgeless
import Tengoku.Erdos64.Erdos64.AdjacentTwoPortFourCycle
import Tengoku.Erdos64.Erdos64.SeparatedThirdNeighborComponentSplit
import Tengoku.Erdos64.Erdos64.SeparatedThirdNeighborPath
import Tengoku.Erdos64.Erdos64.SeparatedThirdNeighborCycle
import Tengoku.Erdos64.Erdos64.TwoPortCycleComposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- In a minimal counterexample, adjacent cubic ports have third neighbors
joined by a path avoiding the root and both ports. The separated one-port
alternative would force a fourth neighbor at a cubic port, since a single
attachment edge would be a bridge.

This supplies the previously missing path premise and its root-cycle
consequence. It does not assert that `p.length + 4` is a power of two.-/
theorem MinimalCounterexample.adjacent_cubic_two_ports_path_cycle
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (D : Finset V) (r x y : V)
    (hr : r ∉ D)
    (hports : x ∈ D ∧ y ∈ D ∧ x ≠ y)
    (hboundary :
      ∀ v, v ∈ D → ∀ t, t ∉ D → G.Adj v t → t = r)
    (hexact :
      ∀ v, v ∈ D → (G.Adj v r ↔ v = x ∨ v = y))
    (hcubic : G.degree x = 3 ∧ G.degree y = 3)
    (hxy : G.Adj x y) :
    ∃ (z w : V) (p : G.Walk z w) (c : G.Walk x x),
      z ∈ D ∧ w ∈ D ∧ z ≠ w ∧ ¬G.Adj z w ∧
      G.Adj x z ∧ G.Adj y w ∧ p.IsPath ∧
      (∀ v, v ∈ p.support → v ≠ r ∧ v ≠ x ∧ v ≠ y) ∧
      c.IsCycle ∧ r ∈ c.support ∧ c.length = p.length + 4 := by
  classical
  obtain ⟨z, w, hzD, hwD, hzr, hzx, hzy, hxz, hwr, hwx, hwy, hyw⟩ :=
    adjacent_cubic_two_ports_have_internal_third_neighbors D r x y
      hr hports hboundary hexact hcubic hxy
  have hxr : G.Adj x r := (hexact x hports.1).2 (Or.inl rfl)
  have hyr : G.Adj y r := (hexact y hports.2.1).2 (Or.inr rfl)
  have hno : ¬(z = w ∨ G.Adj z w) := by
    intro hcase
    exact M.isCounterexample.2
      (hasPowerOfTwoCycle_of_adjacent_two_port_third_neighbors
        hports.2.2 hxr.symm hyr.symm hxy
        hzr hzx hzy hxz hwr hwx hwy hyw hcase)
  have hzw : z ≠ w := fun h => hno (Or.inl h)
  have hzw_adj : ¬G.Adj z w := fun h => hno (Or.inr h)
  rcases separated_third_neighbor_component_split D r x y z w
      hr hports hboundary hexact hcubic hxy
      ⟨hzD, hzr, hzx, hzy, hxz⟩ ⟨hwD, hwr, hwx, hwy, hyw⟩
      hzw hzw_adj with
    ⟨C, hzC, hwC⟩ |
    ⟨K, hzK, hKD, _hKproper, _hwK, hxK, hyK, _hKconn, hboundaryK⟩
  · have hroot :
        ∀ v, v ∈ (↑(D.erase x |>.erase y) : Set V) → v ≠ r := by
      intro v hv hvr
      have hvD : v ∈ D :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).2
      exact hr (hvr ▸ hvD)
    have havoidxy :
        ∀ v, v ∈ (↑(D.erase x |>.erase y) : Set V) →
          v ≠ x ∧ v ≠ y := by
      intro v hv
      exact ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1,
        (Finset.mem_erase.mp hv).1⟩
    obtain ⟨p, hp, havoid⟩ :=
      separated_third_neighbor_path hroot havoidxy C
        (by simp [hzD, hzx, hzy]) (by simp [hwD, hwx, hwy]) hzC hwC
    obtain ⟨c, hc, hrc, hlength⟩ :=
      separated_third_neighbor_cycle hp havoid hports.2.2
        hxr.symm hyr.symm hxz hyw
    exact ⟨z, w, p, c, hzD, hwD, hzw, hzw_adj, hxz, hyw,
      hp, havoid, hc, hrc, hlength⟩
  · obtain ⟨t, htK, hxt, htz⟩ :=
      M.exists_second_onePort_neighbor K x z hxK hzK hxz hboundaryK
    have hyr_ne : y ≠ r := fun h => hr (h ▸ hports.2.1)
    have htr : t ≠ r := fun h => hr (h ▸ hKD htK)
    have hyt : y ≠ t := fun h => hyK (h.symm ▸ htK)
    have hfour : ({r, y, z, t} : Finset V).card = 4 := by
      simp [hyr_ne.symm, hzr.symm, htr.symm, hzy.symm, hyt, htz.symm]
    have hsubset : ({r, y, z, t} : Finset V) ⊆ G.neighborFinset x := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · simpa only [SimpleGraph.mem_neighborFinset] using hxr
      · simpa only [SimpleGraph.mem_neighborFinset] using hxy
      · simpa only [SimpleGraph.mem_neighborFinset] using hxz
      · simpa only [SimpleGraph.mem_neighborFinset] using hxt
    have hcard := Finset.card_le_card hsubset
    rw [hfour, SimpleGraph.card_neighborFinset_eq_degree, hcubic.1] at hcard
    omega

/-- The adjacent cubic two-port branch exposes two distinct cycle-length
certificates from the same separated third-neighbor path.-/
theorem MinimalCounterexample.adjacent_cubic_two_ports_two_cycles
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (D : Finset V) (r x y : V)
    (hr : r ∉ D)
    (hports : x ∈ D ∧ y ∈ D ∧ x ≠ y)
    (hboundary :
      ∀ v, v ∈ D → ∀ t, t ∉ D → G.Adj v t → t = r)
    (hexact :
      ∀ v, v ∈ D → (G.Adj v r ↔ v = x ∨ v = y))
    (hcubic : G.degree x = 3 ∧ G.degree y = 3)
    (hxy : G.Adj x y) :
    ∃ (z w : V) (p : G.Walk z w) (c3 c4 : G.Walk x x),
      z ∈ D ∧ w ∈ D ∧ z ≠ w ∧ ¬G.Adj z w ∧
      G.Adj x z ∧ G.Adj y w ∧ p.IsPath ∧
      (∀ v, v ∈ p.support → v ≠ r ∧ v ≠ x ∧ v ≠ y) ∧
      c3.IsCycle ∧ c3.length = p.length + 3 ∧
      c4.IsCycle ∧ c4.length = p.length + 4 := by
  obtain ⟨z, w, p, c4, hzD, hwD, hzw, hzw_adj, hxz, hyw, hp, havoid,
      hc4, hrc4, hlength4⟩ :=
    M.adjacent_cubic_two_ports_path_cycle D r x y hr hports hboundary
      hexact hcubic hxy
  have havoidxy : ∀ v, v ∈ p.support → v ≠ x ∧ v ≠ y := by
    intro v hv
    exact ⟨(havoid v hv).2.1, (havoid v hv).2.2⟩
  obtain ⟨c3, hc3, hlength3⟩ :=
    connector_path_edge_cycle hp havoidxy hports.2.2 hxz hyw.symm hzw hxy
  exact ⟨z, w, p, c3, c4, hzD, hwD, hzw, hzw_adj, hxz, hyw, hp,
    havoid, hc3, hlength3, hc4, hlength4⟩

/-- In a minimal counterexample, the two adjacent-port cycle lengths from
the same separated path are both excluded from the dyadic spectrum.-/
theorem MinimalCounterexample.adjacent_cubic_two_ports_path_no_dyadic
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (D : Finset V) (r x y : V)
    (hr : r ∉ D)
    (hports : x ∈ D ∧ y ∈ D ∧ x ≠ y)
    (hboundary :
      ∀ v, v ∈ D → ∀ t, t ∉ D → G.Adj v t → t = r)
    (hexact :
      ∀ v, v ∈ D → (G.Adj v r ↔ v = x ∨ v = y))
    (hcubic : G.degree x = 3 ∧ G.degree y = 3)
    (hxy : G.Adj x y) :
    ∃ (z w : V) (p : G.Walk z w),
      z ∈ D ∧ w ∈ D ∧ z ≠ w ∧ ¬G.Adj z w ∧
      G.Adj x z ∧ G.Adj y w ∧ p.IsPath ∧
      (∀ v, v ∈ p.support → v ≠ r ∧ v ≠ x ∧ v ≠ y) ∧
      (∀ k, 2 ≤ k → p.length + 3 ≠ 2 ^ k) ∧
      (∀ k, 2 ≤ k → p.length + 4 ≠ 2 ^ k) := by
  obtain ⟨z, w, p, c3, c4, hzD, hwD, hzw, hzw_adj, hxz, hyw, hp,
      havoid, hc3, hlength3, hc4, hlength4⟩ :=
    M.adjacent_cubic_two_ports_two_cycles D r x y hr hports hboundary
      hexact hcubic hxy
  have hno3 : ∀ k, 2 ≤ k → p.length + 3 ≠ 2 ^ k := by
    intro k hk hlen
    apply M.isCounterexample.2
    exact ⟨k, x, c3, hk, hc3, hlength3.trans hlen⟩
  have hno4 : ∀ k, 2 ≤ k → p.length + 4 ≠ 2 ^ k := by
    intro k hk hlen
    apply M.isCounterexample.2
    exact ⟨k, x, c4, hk, hc4, hlength4.trans hlen⟩
  exact ⟨z, w, p, hzD, hwD, hzw, hzw_adj, hxz, hyw, hp, havoid,
    hno3, hno4⟩

end Erdos64
