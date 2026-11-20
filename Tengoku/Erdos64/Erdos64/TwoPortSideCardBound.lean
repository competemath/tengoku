import Tengoku.Erdos64.Erdos64.StrictRootedDoubleClosedSide

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A closed carrier with two distinct root attachments cannot be smaller than
half of a minimal counterexample.  Rooted doubling supplies the strict descent
when the carrier is below that size, so minimality forces the displayed bound.
@isnad1 id=le.4h6v.s7.29c7a45a2bad from=translated src=- shape=bfc07954 vocab=5a41e32c
-/
theorem MinimalCounterexample.two_port_side_card_bound
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (D : Finset V) (r x y : V)
    (hr : r ∉ D)
    (hports : x ∈ D ∧ y ∈ D ∧ x ≠ y ∧ G.Adj r x ∧ G.Adj r y)
    (hboundary :
      ∀ v, v ∈ D → ∀ w, w ∉ D → G.Adj v w → w = r) :
    Fintype.card V ≤ 2 * D.card + 1 := by
  classical
  let S : Finset V := insert r D
  let root : {v : V // v ∈ S} := ⟨r, Finset.mem_insert_self r D⟩
  have hclosed : ∀ v, v ∈ S → v ≠ root.val →
      ∀ w, G.Adj v w → w ∈ S := by
    intro v hv hvr w hvw
    have hvD : v ∈ D := by
      exact (Finset.mem_insert.mp hv).resolve_left hvr
    by_cases hwD : w ∈ D
    · exact Finset.mem_insert.mpr (Or.inr hwD)
    · exact Finset.mem_insert.mpr (Or.inl (hboundary v hvD w hwD hvw))
  have hpair : ({x, y} : Finset V) ⊆ S.filter (G.Adj r) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_insert.mpr (Or.inr hports.1), hports.2.2.2.1⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_insert.mpr (Or.inr hports.2.1), hports.2.2.2.2⟩
  have hroot : 2 ≤ internalDegree G S root.val := by
    have hcard := Finset.card_le_card hpair
    have hpaircard : ({x, y} : Finset V).card = 2 := by
      simp [hports.2.2.1]
    simpa [root, S, internalDegree, hpaircard] using hcard
  by_contra hbound
  have hsize : 2 * S.card - 1 < Fintype.card V := by
    have hScard : S.card = D.card + 1 := by
      simp [S, hr]
    rw [hScard]
    omega
  exact M.not_exists_strictly_smaller
    (strict_double_of_closed_side M.isCounterexample S root
      hclosed hroot hsize)

end Erdos64
