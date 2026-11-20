import Tengoku.Erdos64.Erdos64.ExactTwoPortResidual
import Tengoku.Erdos64.Erdos64.AdjacentCubicTwoPortPath
import Tengoku.Erdos64.Erdos64.TwoPortDefectBookkeeping

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Adjacent exact ports have internal third neighbors under minimum degree
three; cubicity is only needed for the later separated-component analysis.-/
theorem adjacent_exact_two_ports_have_internal_third_neighbors
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (D : Finset V) (r x y : V)
    (hr : r ∉ D) (hports : x ∈ D ∧ y ∈ D ∧ x ≠ y)
    (hboundary :
      ∀ v, v ∈ D → ∀ w, w ∉ D → G.Adj v w → w = r)
    (hexact :
      ∀ v, v ∈ D → (G.Adj v r ↔ v = x ∨ v = y))
    (hmin : G.minDegree ≥ 3) (hxy : G.Adj x y) :
    ∃ z w, z ∈ D ∧ w ∈ D ∧
      z ≠ r ∧ z ≠ x ∧ z ≠ y ∧ G.Adj x z ∧
      w ≠ r ∧ w ≠ x ∧ w ≠ y ∧ G.Adj y w := by
  have hxr : G.Adj x r := (hexact x hports.1).2 (Or.inl rfl)
  have hyr : G.Adj y r := (hexact y hports.2.1).2 (Or.inr rfl)
  have hxaccount := internalDegree_add_root_indicator_eq_degree
    D r hr hboundary hports.1
  have hyaccount := internalDegree_add_root_indicator_eq_degree
    D r hr hboundary hports.2.1
  have hxdeg : 3 ≤ G.degree x := degree_ge_three_of_minDegree_ge_three G hmin x
  have hydeg : 3 ≤ G.degree y := degree_ge_three_of_minDegree_ge_three G hmin y
  have hxinternal : 2 ≤ internalDegree G D x := by
    simp [hxr] at hxaccount
    omega
  have hyinternal : 2 ≤ internalDegree G D y := by
    simp [hyr] at hyaccount
    omega
  have hyx : y ∈ D.filter (G.Adj x) :=
    Finset.mem_filter.mpr ⟨hports.2.1, hxy⟩
  have hxy' : x ∈ D.filter (G.Adj y) :=
    Finset.mem_filter.mpr ⟨hports.1, hxy.symm⟩
  have hxpos : 0 < ((D.filter (G.Adj x)).erase y).card := by
    rw [Finset.card_erase_of_mem hyx]
    have hxgt : 1 < internalDegree G D x := by omega
    simpa [internalDegree] using hxgt
  have hypos : 0 < ((D.filter (G.Adj y)).erase x).card := by
    rw [Finset.card_erase_of_mem hxy']
    have hygt : 1 < internalDegree G D y := by omega
    simpa [internalDegree] using hygt
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hxpos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hypos
  have hz' := Finset.mem_erase.mp hz
  have hw' := Finset.mem_erase.mp hw
  have hzD : z ∈ D := (Finset.mem_filter.mp hz'.2).1
  have hzx : G.Adj x z := (Finset.mem_filter.mp hz'.2).2
  have hwD : w ∈ D := (Finset.mem_filter.mp hw'.2).1
  have hwy : G.Adj y w := (Finset.mem_filter.mp hw'.2).2
  have hzr : z ≠ r := fun h => hr (h ▸ hzD)
  have hwr : w ≠ r := fun h => hr (h ▸ hwD)
  have hzx_ne : z ≠ x := by
    intro h
    exact G.loopless.irrefl x (h ▸ hzx)
  have hwy_ne : w ≠ y := by
    intro h
    exact G.loopless.irrefl y (h ▸ hwy)
  exact ⟨z, w, hzD, hwD, hzr, hzx_ne, hz'.1, hzx,
    hwr, hw'.1, hwy_ne, hwy⟩

/-- Complete the exact cubic two-port case split. Nonadjacent ports feed the
root-avoiding dyadic-path theorem; adjacent ports expose the separated
third-neighbor path and its two non-dyadic cycle-length constraints.-/
theorem MinimalCounterexample.exact_cubic_two_port_case_split
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (D : Finset V) (r x y : V)
    (hr : r ∉ D) (hports : x ∈ D ∧ y ∈ D ∧ x ≠ y)
    (hrx : G.Adj r x) (hry : G.Adj r y)
    (hboundary :
      ∀ v, v ∈ D → ∀ w, w ∉ D → G.Adj v w → w = r)
    (hexact :
      ∀ v, v ∈ D → (G.Adj v r ↔ v = x ∨ v = y))
    (hcubic : G.degree x = 3 ∧ G.degree y = 3)
    (hroot_degree : 4 ≤ G.degree r) :
    (G.Adj x y ∧
        ∃ (z w : V) (p : G.Walk z w),
          z ∈ D ∧ w ∈ D ∧ z ≠ w ∧ ¬G.Adj z w ∧
          G.Adj x z ∧ G.Adj y w ∧ p.IsPath ∧
          (∀ v, v ∈ p.support → v ≠ r ∧ v ≠ x ∧ v ≠ y) ∧
          (∀ k, 2 ≤ k → p.length + 3 ≠ 2 ^ k) ∧
          (∀ k, 2 ≤ k → p.length + 4 ≠ 2 ^ k)) ∨
      (¬G.Adj x y ∧
        ∃ (k : ℕ) (q : G.Walk x y),
          2 ≤ k ∧ q.IsPath ∧ q.length = 2 ^ k ∧
          (∀ v, v ∈ q.support → v ∈ D) ∧ r ∉ q.support) := by
  by_cases hxy : G.Adj x y
  · left
    exact ⟨hxy, M.adjacent_cubic_two_ports_path_no_dyadic
      D r x y hr hports hboundary hexact hcubic hxy⟩
  · right
    exact ⟨hxy, M.exact_two_port_side_dyadic_path
      D r x y hr hports.1 hports.2.1 hrx hry hports.2.2 hxy
      hroot_degree hboundary (fun v hv => (hexact v hv).mp)⟩

/-- Component-level form of the exact cubic two-port split. The component
attachment cardinality supplies the two ports and exactness; the remaining
branching is only adjacency versus nonadjacency of those ports.-/
theorem MinimalCounterexample.rootDeleted_twoPort_component_cubic_case_split
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hcard : (rootDeletedComponentAttachments G r C).card = 2)
    (hroot_degree : 4 ≤ G.degree r)
    (hcubic : ∀ v, v ∈ rootDeletedComponentCarrier G r C →
      G.Adj v r → G.degree v = 3) :
    (∃ x y : V, ∃ z w : V, ∃ p : G.Walk z w,
        x ∈ rootDeletedComponentCarrier G r C ∧
        y ∈ rootDeletedComponentCarrier G r C ∧
        x ≠ y ∧ G.Adj r x ∧ G.Adj r y ∧ G.Adj x y ∧
        z ∈ rootDeletedComponentCarrier G r C ∧
        w ∈ rootDeletedComponentCarrier G r C ∧ z ≠ w ∧ ¬G.Adj z w ∧
        G.Adj x z ∧ G.Adj y w ∧ p.IsPath ∧
        (∀ v, v ∈ p.support → v ≠ r ∧ v ≠ x ∧ v ≠ y) ∧
        (∀ k, 2 ≤ k → p.length + 3 ≠ 2 ^ k) ∧
        (∀ k, 2 ≤ k → p.length + 4 ≠ 2 ^ k)) ∨
      (∃ x y : V, ∃ k : ℕ, ∃ q : G.Walk x y,
        x ∈ rootDeletedComponentCarrier G r C ∧
        y ∈ rootDeletedComponentCarrier G r C ∧ x ≠ y ∧
        G.Adj r x ∧ G.Adj r y ∧ ¬G.Adj x y ∧
        2 ≤ k ∧ q.IsPath ∧ q.length = 2 ^ k ∧
        (∀ v, v ∈ q.support →
          v ∈ rootDeletedComponentCarrier G r C) ∧ r ∉ q.support) := by
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
  have hexact :
      ∀ v, v ∈ rootDeletedComponentCarrier G r C →
        (G.Adj v r ↔ v = x ∨ v = y) := by
    intro v hv
    constructor
    · exact hports v hv
    · intro hvxy
      rcases hvxy with rfl | rfl
      · exact hrx.symm
      · exact hry.symm
  have hcase := M.exact_cubic_two_port_case_split
    (rootDeletedComponentCarrier G r C) r x y
    (rootDeletedComponentCarrier_nonempty_not_mem G r C).2
    ⟨hx, hy, hxy⟩ hrx hry hboundary hexact
    ⟨hcubic x hx hrx.symm, hcubic y hy hry.symm⟩ hroot_degree
  rcases hcase with hcase | hcase
  · left
    rcases hcase with ⟨hxy_adj, z, w, p, hz, hw, hzw, hzw_adj,
        hxz, hyw, hp, havoid, hno3, hno4⟩
    exact ⟨x, y, z, w, p, hx, hy, hxy, hrx, hry, hxy_adj,
      hz, hw, hzw, hzw_adj, hxz, hyw, hp, havoid, hno3, hno4⟩
  · right
    rcases hcase with ⟨hnadj, k, q, hk, hq, hqlen, hinside, hroot⟩
    exact ⟨x, y, k, q, hx, hy, hxy, hrx, hry, hnadj, hk, hq, hqlen,
      hinside, hroot⟩

end Erdos64
