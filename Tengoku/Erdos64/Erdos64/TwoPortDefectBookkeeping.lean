import Tengoku.Erdos64.Erdos64.TwoPortDefect

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- At a finite carrier with no boundary vertex other than `r`, the ambient
    neighbors of a retained vertex split into its carrier neighbors and the
    possible single boundary neighbor `r`.-/
theorem internalDegree_add_root_indicator_eq_degree
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (D : Finset V) (r : V)
    (hr : r ∉ D)
    (hboundary :
      ∀ v, v ∈ D → ∀ w, w ∉ D → G.Adj v w → w = r)
    {v : V} (hv : v ∈ D) :
    internalDegree G D v + (if G.Adj v r then 1 else 0) = G.degree v := by
  classical
  let B : Finset V := if G.Adj v r then {r} else ∅
  have hsplit : G.neighborFinset v = D.filter (G.Adj v) ∪ B := by
    ext w
    constructor
    · intro hw
      have hvw : G.Adj v w := (G.mem_neighborFinset v w).1 hw
      by_cases hwD : w ∈ D
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hwD, hvw⟩))
      · have hwr : w = r := hboundary v hv w hwD hvw
        subst w
        by_cases hvr : G.Adj v r
        · exact Finset.mem_union.mpr (Or.inr (by simp [B, hvr]))
        · exact False.elim (hvr hvw)
    · intro hw
      rcases Finset.mem_union.mp hw with hwD | hwB
      · exact (G.mem_neighborFinset v w).2 (Finset.mem_filter.mp hwD).2
      · by_cases hvr : G.Adj v r
        · have hwr : w = r := by simpa [B, hvr] using hwB
          subst w
          exact (G.mem_neighborFinset v r).2 hvr
        · simp [B, hvr] at hwB
  have hdisjoint : Disjoint (D.filter (G.Adj v)) B := by
    by_cases hvr : G.Adj v r
    · simp [B, hvr, hr]
    · simp [B, hvr]
  calc
    internalDegree G D v + (if G.Adj v r then 1 else 0) =
        (D.filter (G.Adj v)).card + B.card := by
          by_cases hvr : G.Adj v r <;> simp [internalDegree, B, hvr]
    _ = (D.filter (G.Adj v) ∪ B).card :=
      (Finset.card_union_of_disjoint hdisjoint).symm
    _ = (G.neighborFinset v).card := by rw [← hsplit]
    _ = G.degree v := SimpleGraph.card_neighborFinset_eq_degree G v

/-- Exact degree and boundary accounting for a carrier with two distinct
    cubic ports and no other root-adjacent carrier vertices.-/
theorem two_cubic_ports_boundary_accounting
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (D : Finset V) (r x y : V)
    (hr : r ∉ D)
    (hports : x ∈ D ∧ y ∈ D ∧ x ≠ y)
    (hboundary :
      ∀ v, v ∈ D → ∀ w, w ∉ D → G.Adj v w → w = r)
    (hexact :
      ∀ v, v ∈ D → (G.Adj v r ↔ v = x ∨ v = y))
    (hcubic : G.degree x = 3 ∧ G.degree y = 3) :
    internalDegree G D x = 2 ∧
    internalDegree G D y = 2 ∧
    (∀ v, v ∈ D → v ≠ x → v ≠ y →
      internalDegree G D v = G.degree v) ∧
    (D.filter (G.Adj r)).card = 2 := by
  classical
  have hxroot : G.Adj x r := (hexact x hports.1).2 (Or.inl rfl)
  have hyroot : G.Adj y r := (hexact y hports.2.1).2 (Or.inr rfl)
  have hxaccount := internalDegree_add_root_indicator_eq_degree
    D r hr hboundary hports.1
  have hyaccount := internalDegree_add_root_indicator_eq_degree
    D r hr hboundary hports.2.1
  have hxdeg : internalDegree G D x = 2 := by
    simp [hxroot, hcubic.1] at hxaccount
    omega
  have hydeg : internalDegree G D y = 2 := by
    simp [hyroot, hcubic.2] at hyaccount
    omega
  have hnonport : ∀ v, v ∈ D → v ≠ x → v ≠ y → ¬ G.Adj v r := by
    intro v hv hvx hvy hadj
    rcases (hexact v hv).mp hadj with h | h
    · exact hvx h
    · exact hvy h
  have hretained : ∀ v, v ∈ D → v ≠ x → v ≠ y →
      internalDegree G D v = G.degree v := by
    intro v hv hvx hvy
    have haccount := internalDegree_add_root_indicator_eq_degree
      D r hr hboundary hv
    have hvr := hnonport v hv hvx hvy
    simpa [hvr] using haccount
  have hports_filter : D.filter (G.Adj r) = {x, y} := by
    ext v
    constructor
    · intro hv
      have hvD : v ∈ D := (Finset.mem_filter.mp hv).1
      have hvr : G.Adj v r := (Finset.mem_filter.mp hv).2.symm
      have hvxy : v = x ∨ v = y := (hexact v hvD).mp hvr
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hvxy
    · intro hv
      have hvxy : v = x ∨ v = y := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hv
      rcases hvxy with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hports.1, hxroot.symm⟩
      · exact Finset.mem_filter.mpr ⟨hports.2.1, hyroot.symm⟩
  refine ⟨hxdeg, hydeg, hretained, ?_⟩
  rw [hports_filter]
  simp [hports.2.2]

end Erdos64
