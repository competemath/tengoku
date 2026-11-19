import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedCliqueMinor.SeparatorRestriction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Connectivity of a completed separator torso

An r-connected graph remains r-connected on either side of an order-r
separation after the boundary is completed to a clique. We use the
generic connected-set restriction theorem to project paths that leave
the chosen side.
-/

namespace HadwigerLean

namespace VertexSeparation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} (S : VertexSeparation G)

/-- A nonempty strict left side makes the right torso strictly smaller
than the original finite graph.
@isnad1 id=lt.1h3v.s5.d37f52fc0116 from=translated src=- shape=b444d85b vocab=05c714cb
-/
theorem right_order_lt_of_strictLeft_nonempty
    [Fintype S.right] (hleft : S.strictLeft.Nonempty) :
    Fintype.card S.right < Fintype.card V := by
  classical
  let Y : Finset V := S.right.toFinset
  obtain ⟨v, hvL, hvR⟩ := hleft
  have hsub : Y ⊂ (Finset.univ : Finset V) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have hvY : v ∈ Y := by rw [heq]; simp
    exact hvR (Set.mem_toFinset.mp (by simpa [Y] using hvY))
  have hcard := Finset.card_lt_card hsub
  simpa [Y] using hcard
end VertexSeparation

end HadwigerLean
