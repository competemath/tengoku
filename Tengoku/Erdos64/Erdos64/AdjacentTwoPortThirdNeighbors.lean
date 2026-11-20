import Tengoku.Erdos64.Erdos64.TwoPortDefectBookkeeping

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- In the exact cubic two-port branch, adjacent ports each have an
    additional internal neighbor.  The two additional neighbors are not
    asserted to be distinct from one another.
@isnad1 id=ex.6h6v.s8.7853730579dd from=translated src=- shape=fae6e584 vocab=6cb45fb4
-/
theorem adjacent_cubic_two_ports_have_internal_third_neighbors
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (D : Finset V) (r x y : V)
    (hr : r ∉ D)
    (hports : x ∈ D ∧ y ∈ D ∧ x ≠ y)
    (hboundary :
      ∀ v, v ∈ D → ∀ w, w ∉ D → G.Adj v w → w = r)
    (hexact :
      ∀ v, v ∈ D → (G.Adj v r ↔ v = x ∨ v = y))
    (hcubic : G.degree x = 3 ∧ G.degree y = 3)
    (hxy : G.Adj x y) :
    ∃ z w, z ∈ D ∧ w ∈ D ∧
      z ≠ r ∧ z ≠ x ∧ z ≠ y ∧ G.Adj x z ∧
      w ≠ r ∧ w ≠ x ∧ w ≠ y ∧ G.Adj y w := by
  have haccount := two_cubic_ports_boundary_accounting D r x y hr hports
    hboundary hexact hcubic
  have hyx : y ∈ D.filter (G.Adj x) :=
    Finset.mem_filter.mpr ⟨hports.2.1, hxy⟩
  have hxy' : x ∈ D.filter (G.Adj y) :=
    Finset.mem_filter.mpr ⟨hports.1, hxy.symm⟩
  have hxcard : (D.filter (G.Adj x)).card = 2 := by
    simpa [internalDegree] using haccount.1
  have hycard : (D.filter (G.Adj y)).card = 2 := by
    simpa [internalDegree] using haccount.2.1
  have hxpos : 0 < ((D.filter (G.Adj x)).erase y).card := by
    rw [Finset.card_erase_of_mem hyx, hxcard]
    omega
  have hypos : 0 < ((D.filter (G.Adj y)).erase x).card := by
    rw [Finset.card_erase_of_mem hxy', hycard]
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hxpos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hypos
  have hz' := Finset.mem_erase.mp hz
  have hw' := Finset.mem_erase.mp hw
  have hzD : z ∈ D := (Finset.mem_filter.mp hz'.2).1
  have hzx : G.Adj x z := (Finset.mem_filter.mp hz'.2).2
  have hwD : w ∈ D := (Finset.mem_filter.mp hw'.2).1
  have hwy : G.Adj y w := (Finset.mem_filter.mp hw'.2).2
  have hzr : z ≠ r := by
    intro hzr
    exact hr (hzr ▸ hzD)
  have hwr : w ≠ r := by
    intro hwr
    exact hr (hwr ▸ hwD)
  have hzx_ne : z ≠ x := by
    intro hzx_ne
    exact G.loopless.irrefl x (hzx_ne ▸ hzx)
  have hwy_ne : w ≠ y := by
    intro hwy_ne
    exact G.loopless.irrefl y (hwy_ne ▸ hwy)
  exact ⟨z, w, hzD, hwD, hzr, hzx_ne, hz'.1, hzx,
    hwr, hw'.1, hwy_ne, hwy⟩

end Erdos64
