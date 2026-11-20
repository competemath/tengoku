import Tengoku.Erdos64.Erdos64.CutVertexComponentBoundary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Root neighbors assigned to one root-deleted connected component.-/
noncomputable def rootDeletedComponentAttachments
    {V : Type u} (G : SimpleGraph V) (r : V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj]
    (C : (G.induce {v : V | v ≠ r}).ConnectedComponent) : Finset V :=
  (G.neighborFinset r).filter (fun x => x ∈ rootDeletedComponentCarrier G r C)

/-- Attachments of distinct root-deleted components are disjoint.-/
theorem rootDeletedComponentAttachments_pairwise_disjoint
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (r : V) :
    letI : Fintype ((G.induce {v : V | v ≠ r}).ConnectedComponent) :=
      Fintype.ofFinite _
    Pairwise (fun C D =>
      Disjoint (rootDeletedComponentAttachments G r C)
        (rootDeletedComponentAttachments G r D)) := by
  classical
  letI : Fintype ((G.induce {v : V | v ≠ r}).ConnectedComponent) :=
    Fintype.ofFinite _
  intro C D hCD
  apply Finset.disjoint_left.2
  intro x hxC hxD
  have hxC' := (Finset.mem_filter.mp hxC).2
  have hxD' := (Finset.mem_filter.mp hxD).2
  obtain ⟨hxne, hCx⟩ :=
    (mem_rootDeletedComponentCarrier_iff G r C x).1 hxC'
  obtain ⟨_, hDx⟩ :=
    (mem_rootDeletedComponentCarrier_iff G r D x).1 hxD'
  have hmkC :
      (G.induce {v : V | v ≠ r}).connectedComponentMk ⟨x, hxne⟩ = C :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff C ⟨x, hxne⟩).mp hCx
  have hmkD :
      (G.induce {v : V | v ≠ r}).connectedComponentMk ⟨x, hxne⟩ = D :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff D ⟨x, hxne⟩).mp hDx
  exact hCD (hmkC.symm.trans hmkD)

/-- The root-neighbor finset is partitioned by the attachments of the actual
    connected components after deleting the root.-/
theorem rootDeletedComponentAttachments_biUnion
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (r : V) :
    letI : Fintype ((G.induce {v : V | v ≠ r}).ConnectedComponent) :=
      Fintype.ofFinite _
    (Finset.univ : Finset ((G.induce {v : V | v ≠ r}).ConnectedComponent)).biUnion
        (rootDeletedComponentAttachments G r) = G.neighborFinset r := by
  classical
  letI : Fintype ((G.induce {v : V | v ≠ r}).ConnectedComponent) :=
    Fintype.ofFinite _
  ext x
  constructor
  · intro hx
    obtain ⟨C, _, hxC⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hxC).1
  · intro hx
    have hxne : x ≠ r := by
      intro hxr
      subst x
      exact G.loopless.irrefl r ((G.mem_neighborFinset r r).mp hx)
    let C : (G.induce {v : V | v ≠ r}).ConnectedComponent :=
      (G.induce {v : V | v ≠ r}).connectedComponentMk ⟨x, hxne⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨C, Finset.mem_univ _, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨hx, ?_⟩
    apply (mem_rootDeletedComponentCarrier_iff G r C x).2
    exact ⟨hxne, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩

end Erdos64
