import Tengoku.Erdos64.Erdos64.BalancedRootDeletedPartition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Every actual root-deleted component has a nonempty root-attachment set in a
    finite connected graph.
@isnad1 id=nonempty.1h4v.s5.ec2bca33e90c from=translated src=- shape=fe808d4b vocab=8b5f9b17
-/
theorem rootDeletedComponentAttachments_nonempty
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (r : V)
    (hconn : G.Connected)
    (C : (G.induce {v : V | v ≠ r}).ConnectedComponent) :
    (rootDeletedComponentAttachments G r C).Nonempty := by
  classical
  obtain ⟨x, hx, hxr⟩ :=
    (rootDeletedComponent_boundary r hconn C).2
  refine ⟨x, Finset.mem_filter.mpr ⟨?_, hx⟩⟩
  exact (G.mem_neighborFinset r x).2 hxr.symm

/-- With root degree four, two distinct actual root-deleted components cannot
    both have at least three root attachments.
@isnad1 id=ex.3h3v.s7.8d8c23483037 from=translated src=- shape=7f96fe47 vocab=e5aa15eb
-/
theorem exists_rootDeletedComponent_attachments_le_two_of_degree_eq_four
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (r : V)
    (hconn : G.Connected) (hdegree : G.degree r = 4)
    (hcomponents : ∃ C D : (G.induce {v : V | v ≠ r}).ConnectedComponent,
      C ≠ D) :
    ∃ C : (G.induce {v : V | v ≠ r}).ConnectedComponent,
      (rootDeletedComponentAttachments G r C).card ≤ 2 := by
  classical
  letI : Fintype ((G.induce {v : V | v ≠ r}).ConnectedComponent) :=
    Fintype.ofFinite _
  obtain ⟨C, D, hCD⟩ := hcomponents
  by_contra hnone
  have hCnot : ¬ (rootDeletedComponentAttachments G r C).card ≤ 2 := by
    intro hC
    exact hnone ⟨C, hC⟩
  have hDnot : ¬ (rootDeletedComponentAttachments G r D).card ≤ 2 := by
    intro hD
    exact hnone ⟨D, hD⟩
  have hC3 : 3 ≤ (rootDeletedComponentAttachments G r C).card := by
    omega
  have hD3 : 3 ≤ (rootDeletedComponentAttachments G r D).card := by
    omega
  have hdisj :
      Disjoint (rootDeletedComponentAttachments G r C)
        (rootDeletedComponentAttachments G r D) :=
    (rootDeletedComponentAttachments_pairwise_disjoint r) hCD
  have hsub :
      rootDeletedComponentAttachments G r C ∪
          rootDeletedComponentAttachments G r D ⊆ G.neighborFinset r := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).1
    · exact (Finset.mem_filter.mp hx).1
  have hunion_card :
      (rootDeletedComponentAttachments G r C ∪
          rootDeletedComponentAttachments G r D).card =
        (rootDeletedComponentAttachments G r C).card +
          (rootDeletedComponentAttachments G r D).card :=
    Finset.card_union_of_disjoint hdisj
  have hle :
      (rootDeletedComponentAttachments G r C ∪
          rootDeletedComponentAttachments G r D).card ≤ 4 := by
    calc
      _ ≤ (G.neighborFinset r).card := Finset.card_le_card hsub
      _ = 4 := by simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdegree
  omega

end Erdos64
