import Tengoku.Erdos64.Erdos64.ComponentAttachments

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- The ambient carrier of a connected component after deleting a root vertex.-/
noncomputable def rootDeletedComponentCarrier
    {V : Type u} (G : SimpleGraph V) (r : V) [Fintype V] [DecidableEq V]
    (C : (G.induce {v : V | v ≠ r}).ConnectedComponent) : Finset V := by
  letI : Fintype C := Fintype.ofFinite _
  exact C.supp.toFinset.image Subtype.val

@[simp] theorem mem_rootDeletedComponentCarrier_iff
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V)
    (C : (G.induce {v : V | v ≠ r}).ConnectedComponent) (v : V) :
    v ∈ rootDeletedComponentCarrier G r C ↔
      ∃ hv : v ≠ r,
        (⟨v, hv⟩ : {w : V // w ≠ r}) ∈ C.supp := by
  classical
  simp [rootDeletedComponentCarrier]

/-- A root-deleted component is nonempty and has no root vertex.-/
theorem rootDeletedComponentCarrier_nonempty_not_mem
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V)
    (C : (G.induce {v : V | v ≠ r}).ConnectedComponent) :
    (rootDeletedComponentCarrier G r C).Nonempty ∧
      r ∉ rootDeletedComponentCarrier G r C := by
  classical
  constructor
  · obtain ⟨⟨v, hv⟩, hC⟩ := C.nonempty_supp
    exact ⟨v, (mem_rootDeletedComponentCarrier_iff G r C v).2 ⟨hv, hC⟩⟩
  · intro hr
    obtain ⟨hr', _⟩ := (mem_rootDeletedComponentCarrier_iff G r C r).1 hr
    exact hr' rfl

/-- The ambient boundary of a root-deleted connected component is constrained
    to the deleted root, and connectedness gives an actual root attachment.-/
theorem rootDeletedComponent_boundary
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (r : V) (hconn : G.Connected)
    (C : (G.induce {v : V | v ≠ r}).ConnectedComponent) :
    (∀ x, x ∈ rootDeletedComponentCarrier G r C →
      ∀ y, G.Adj x y →
        y ∈ rootDeletedComponentCarrier G r C ∨ y = r) ∧
      ∃ x, x ∈ rootDeletedComponentCarrier G r C ∧ G.Adj x r := by
  classical
  have hclosure : ∀ x, x ∈ rootDeletedComponentCarrier G r C →
      ∀ y, G.Adj x y →
        y ∈ rootDeletedComponentCarrier G r C ∨ y = r := by
    intro x hx y hxy
    by_cases hyr : y = r
    · exact Or.inr hyr
    · left
      obtain ⟨hx', hxC⟩ := (mem_rootDeletedComponentCarrier_iff G r C x).1 hx
      apply (mem_rootDeletedComponentCarrier_iff G r C y).2
      refine ⟨hyr, ?_⟩
      have hCeq :
          (G.induce {v : V | v ≠ r}).connectedComponentMk ⟨x, hx'⟩ = C :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff C ⟨x, hx'⟩).mp hxC
      have hxyD : (G.induce {v : V | v ≠ r}).Adj
          ⟨x, hx'⟩ ⟨y, hyr⟩ := hxy
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact (SimpleGraph.ConnectedComponent.eq.mpr hxyD.reachable.symm).trans hCeq
  have hnonempty : (rootDeletedComponentCarrier G r C).Nonempty :=
    (rootDeletedComponentCarrier_nonempty_not_mem G r C).1
  have hroot_fin : r ∉ rootDeletedComponentCarrier G r C :=
    (rootDeletedComponentCarrier_nonempty_not_mem G r C).2
  have hroot_not_mem : r ∉ (rootDeletedComponentCarrier G r C : Set V) := by
    simpa only [Finset.mem_coe] using hroot_fin
  obtain ⟨x, hx⟩ := hnonempty
  have hx' : x ∈ (rootDeletedComponentCarrier G r C : Set V) := by
    exact Finset.mem_coe.mpr hx
  obtain ⟨u, v, hu, hv, huv⟩ :=
    exists_adj_mem_of_mem_of_not_mem hconn hx' hroot_not_mem
  have hvr : v = r := by
    rcases hclosure u (Finset.mem_coe.mp hu) v huv with hvC | hvr
    · exact (hv (Finset.mem_coe.mpr hvC)).elim
    · exact hvr
  exact ⟨hclosure, ⟨u, Finset.mem_coe.mp hu, hvr ▸ huv⟩⟩

end Erdos64
