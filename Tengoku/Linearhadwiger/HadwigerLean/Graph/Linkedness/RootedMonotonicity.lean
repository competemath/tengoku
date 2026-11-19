import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.Massed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rooted linkedness is inherited by smaller root sets
-/

namespace HadwigerLean
namespace Linkedness

/-- A linkage avoiding a larger root set also avoids any smaller one.
@isnad1 id=rootedli.2h4v.s5.cba144bfc85a from=translated src=- shape=71587487 vocab=2e6de8c5
-/
theorem RootedLinked.of_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {X Y : Finset V}
    (h : RootedLinked G X) (hYX : Y ⊆ X) :
    RootedLinked G Y := by
  intro n P hP hne hY
  have hX : ∀ i, P.terminals i ⊆ (X : Set V) := by
    intro i v hv
    exact hYX (hY i hv)
  obtain ⟨L, hL⟩ := h n P hP hne hX
  exact ⟨L, fun i v hv hroot => hL i v hv (hYX hroot)⟩

end Linkedness
end HadwigerLean
