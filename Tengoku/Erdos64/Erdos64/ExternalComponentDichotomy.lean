import Tengoku.Erdos64.Erdos64.ExternalComponentBridge
import Tengoku.Erdos64.Erdos64.ExternalComponentCarrier

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Structural bridge/unique-root split with the minimality consequence in the
unique-root branch.  The bridge branch is intentionally left as the existing
bridge witness; no arithmetic conclusion about its cycle lengths is added.-/
theorem externalComponent_bridge_or_rootedBranch_residual
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (m : EdgeMinimalCounterexample G)
    {s : V} {C : G.Walk s s} (hC : C.IsCycle)
    (hG : G.Connected) {x : V} (hx : x ∉ C.support) :
    (∃ bridge : CycleBridgePath G C, True) ∨
      ∃ B : RootedBranchCarrier G,
        B.root ∈ C.support ∧
        (∀ v, v ∈ B.carrier → v ∉ C.support) ∧
        internalDegree G (Finset.univ \ B.carrier) B.root ≤ 2 := by
  rcases externalComponent_bridge_or_unique_root hC hG hx with hbridge | hroot
  · exact Or.inl hbridge
  · rcases hroot with ⟨r, hr, hroot⟩
    rcases externalComponent_exists_rootedBranchCarrier hx hr hroot with
      ⟨B, _, hBroot, houtside, _⟩
    right
    refine ⟨B, ?_, ?_, ?_⟩
    · simpa [hBroot] using hr
    · exact houtside
    · exact B.root_internalDegree_le_two
        m.vertexMinimal.isSubgraphCritical
        m.vertexMinimal.isCounterexample.1

end Erdos64
