import Tengoku.Erdos64.Erdos64.SmallCarrierBoundary
import Tengoku.Erdos64.Erdos64.BoundaryRootGraph

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- With at least three boundary vertices, the boundary root itself has
degree at least three. Direct vertex minimality therefore forces a dyadic
cycle using only the order of the carrier plus one new vertex.-/
theorem MinimalCounterexample.boundary_root_has_dyadic_cycle_of_three_boundary
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (K : Finset V)
    (hsingle : ∀ v, v ∈ K → ∀ a, a ∉ K → ∀ b, b ∉ K →
      G.Adj v a → G.Adj v b → a = b)
    (hboundary : 3 ≤ (carrierBoundaryVertices G K).card)
    (hsize : K.card + 1 < Fintype.card V) :
    HasPowerOfTwoCycle
      (boundaryRootGraph (G.induce (↑K : Set V)) (carrierBoundaryVertices G K)) := by
  classical
  let H := G.induce (↑K : Set V)
  let B := carrierBoundaryVertices G K
  let R := boundaryRootGraph H B
  have hdeg : ∀ v, R.degree (some v) = G.degree v.1 := by
    intro v
    rw [boundaryRootGraph_degree_some]
    exact carrier_degree_add_boundary_indicator K hsingle v
  have hmin : 3 ≤ R.minDegree := by
    apply R.le_minDegree_of_forall_le_degree
    intro v
    cases v with
    | none =>
        rw [boundaryRootGraph_degree_none]
        exact hboundary
    | some v =>
        rw [hdeg]
        exact degree_ge_three_of_minDegree_ge_three G M.isCounterexample.1 v.1
  by_contra hno
  apply M.not_exists_strictly_smaller (H := R)
  refine ⟨⟨hmin, hno⟩, ?_⟩
  simpa using hsize

end Erdos64
