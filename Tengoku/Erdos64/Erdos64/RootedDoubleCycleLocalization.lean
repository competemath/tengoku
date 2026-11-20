import Tengoku.Erdos64.Erdos64.RootedDoubleProjection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Every simple cycle in a rooted double is contained in one tagged copy,
apart from the shared root.-/
theorem rootedDouble_cycle_localization
    {V : Type u} {G : SimpleGraph V} [DecidableEq V] {r : V}
    {x : RootedDoubleVertex V r}
    (p : (rootedDoubleGraph G r).Walk x x) (hp : p.IsCycle) :
    ∃ b : Bool, ∀ z, z ∈ p.support →
      z = none ∨ ∃ v : {v : V // v ≠ r}, z = some (b, v) := by
  obtain ⟨b, hb⟩ := rootedDouble_cycle_common_tag p hp
  refine ⟨b, ?_⟩
  intro z hz
  by_cases hnone : z = none
  · exact Or.inl hnone
  · exact Or.inr (hb z hz hnone)

/-- The global localization disjunction supplies the simple-cycle projection
contract, with exact preservation of length.-/
theorem rootedDouble_cycle_localization_projection
    {V : Type u} {G : SimpleGraph V} [DecidableEq V] {r : V}
    {x : RootedDoubleVertex V r}
    (p : (rootedDoubleGraph G r).Walk x x) (hp : p.IsCycle) :
    (p.map rootedDoubleProjectionHom).IsCycle ∧
      (p.map rootedDoubleProjectionHom).length = p.length := by
  exact rootedDouble_cycle_projection p hp

end Erdos64
