import Tengoku.Erdos64.Erdos64.TwoPortSafeSideDichotomy
import Tengoku.Erdos64.Erdos64.RootDeletedNoDyadicTransfer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- In a dyadic-free minimal counterexample, a proper two-port carrier cannot
have all of its root-attached vertices of degree at least four.  The safe-side
alternative would otherwise be a strictly smaller induced counterexample.
This is the precise minimality specialization of
`two_port_safe_side_or_cubic_defect`.
@isnad1 id=or.5h6v.s7.6a91043ded78 from=translated src=- shape=c461aa9a vocab=dc2eef0e
-/
theorem MinimalCounterexample.two_port_cubic_defect_of_no_dyadic
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (D : Finset V) (r x y : V) (hD : D.Nonempty)
    (hr : r ∉ D)
    (hboundary :
      ∀ v, v ∈ D → ∀ w, w ∉ D → G.Adj v w → w = r)
    (hports : ∀ v, v ∈ D → (G.Adj v r ↔ v = x ∨ v = y)) :
    G.degree x = 3 ∨ G.degree y = 3 := by
  rcases two_port_safe_side_or_cubic_defect D r x y hD hr hboundary
      M.isCounterexample.1 hports with hsafe | hxcubic | hycubic
  · have hcounter :
        IsCounterexample (G.induce (↑D : Set V)) := by
      refine ⟨hsafe, ?_⟩
      exact not_hasPowerOfTwoCycle_induce_of_not_hasPowerOfTwoCycle
        M.isCounterexample.2
    have hcard : Fintype.card (↑D : Set V) < Fintype.card V := by
      apply Fintype.card_subtype_lt (p := fun v : V => v ∈ D) (x := r)
      exact hr
    exact (M.not_exists_strictly_smaller ⟨hcounter, hcard⟩).elim
  · exact Or.inl hxcubic
  · exact Or.inr hycubic

end Erdos64
