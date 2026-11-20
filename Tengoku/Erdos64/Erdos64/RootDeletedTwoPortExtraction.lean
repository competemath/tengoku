import Tengoku.Erdos64.Erdos64.BalancedRootDeletedPartition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- An actual root-deleted component with exactly two attachment vertices
    exposes two distinct root ports together with their carrier membership.
@isnad1 id=ex.1h4v.s6.6b0a070fad22 from=translated src=- shape=b4214d37 vocab=43a57613
-/
theorem rootDeletedComponent_twoPort_extraction
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (r : V)
    (C : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hcard : (rootDeletedComponentAttachments G r C).card = 2) :
    ∃ a b : V, a ≠ b ∧
      a ∈ rootDeletedComponentCarrier G r C ∧
      b ∈ rootDeletedComponentCarrier G r C ∧
      G.Adj r a ∧ G.Adj r b := by
  classical
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp hcard
  have ha : a ∈ rootDeletedComponentAttachments G r C := by
    rw [hs]
    simp [hab]
  have hb : b ∈ rootDeletedComponentAttachments G r C := by
    rw [hs]
    simp [hab]
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  exact ⟨a, b, hab, ha'.2, hb'.2,
    (G.mem_neighborFinset r a).mp ha'.1,
    (G.mem_neighborFinset r b).mp hb'.1⟩

end Erdos64
