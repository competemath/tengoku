import Tengoku.Erdos64.Erdos64.ComponentAttachmentLowerBound
import Tengoku.Erdos64.Erdos64.BalancedRootDeletedPartition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Criticality forces every native root-deleted component to use at least two
    root ports when the deleted root has degree four.
@isnad1 id=le.4h4v.s6.a55d54ad34cf from=translated src=- shape=90c907d6 vocab=b85cf331
-/
theorem rootDeletedComponentAttachments_ge_two_of_degree_eq_four
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (r : V)
    (hconn : G.Connected) (hmin : G.minDegree ≥ 3)
    (hcritical : IsSubgraphCritical G)
    (C : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hdegree : G.degree r = 4) :
    2 ≤ (rootDeletedComponentAttachments G r C).card := by
  classical
  let K : Finset V := rootDeletedComponentCarrier G r C
  have hKnonempty : K.Nonempty := by
    exact (rootDeletedComponentCarrier_nonempty_not_mem G r C).1
  have hrK : r ∉ K := by
    exact (rootDeletedComponentCarrier_nonempty_not_mem G r C).2
  have hboundary : ∀ x, x ∈ K → ∀ y, y ∉ K → G.Adj x y → y = r := by
    intro x hx y hy hxy
    have hclosed := (rootDeletedComponent_boundary r hconn C).1 x hx y hxy
    rcases hclosed with hyK | hyr
    · exact (hy hyK).elim
    · exact hyr
  obtain ⟨_, hdegree_bound⟩ :=
    component_attachment_lower_bound hconn hmin hcritical K r
      hKnonempty hrK hboundary
  have hdegree_bound' : 4 ≤ (K.filter (G.Adj r)).card + 2 := by
    simpa [hdegree] using hdegree_bound
  have hattach : 2 ≤ (K.filter (G.Adj r)).card := by
    omega
  have hattach_eq :
      rootDeletedComponentAttachments G r C = K.filter (G.Adj r) := by
    ext x
    simp [rootDeletedComponentAttachments, K,
      SimpleGraph.mem_neighborFinset, and_comm]
  rw [hattach_eq]
  exact hattach

end Erdos64
