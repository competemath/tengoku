import Tengoku.Erdos64.Erdos64.BalancedRootDeletedPartition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- The attachment finsets of the actual root-deleted components have total
    cardinality equal to the degree of the deleted root.-/
theorem rootDeletedComponentAttachments_sum_card
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (r : V) :
    letI : Fintype ((G.induce {v : V | v ≠ r}).ConnectedComponent) :=
      Fintype.ofFinite _
    (∑ C : (G.induce {v : V | v ≠ r}).ConnectedComponent,
      (rootDeletedComponentAttachments G r C).card) = G.degree r := by
  classical
  letI : Fintype ((G.induce {v : V | v ≠ r}).ConnectedComponent) :=
    Fintype.ofFinite _
  have hcard :
      ((Finset.univ : Finset ((G.induce {v : V | v ≠ r}).ConnectedComponent)).biUnion
        (rootDeletedComponentAttachments G r)).card =
      ∑ C : (G.induce {v : V | v ≠ r}).ConnectedComponent,
        (rootDeletedComponentAttachments G r C).card := by
    rw [Finset.card_biUnion]
    intro (C : (G.induce {v : V | v ≠ r}).ConnectedComponent) _
      (D : (G.induce {v : V | v ≠ r}).ConnectedComponent) _ hCD
    exact (@rootDeletedComponentAttachments_pairwise_disjoint V _ _ G _ r) hCD
  have hpartition := @rootDeletedComponentAttachments_biUnion V _ _ G _ r
  rw [hpartition] at hcard
  simpa [SimpleGraph.card_neighborFinset_eq_degree] using hcard.symm

end Erdos64
