import Tengoku.Erdos64.Erdos64.TwoPoleCubicParity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- In the balanced two-pole cut, cubic bookkeeping forces the side order to
    be even and the ambient order to be odd. This is an order invariant, not
    a cycle construction or a dyadic conclusion.
@isnad1 id=and.9h7v.s8.00f99549b92c from=translated src=- shape=3f4f1b2c vocab=5a9d7824
-/
theorem balanced_two_cubic_poles_force_odd_ambient_order
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (D E : Finset V) (r x y : V)
    (hrD : r ∉ D) (hports : x ∈ D ∧ y ∈ D ∧ x ≠ y)
    (hboundary :
      ∀ v, v ∈ D → ∀ w, w ∉ D → G.Adj v w → w = r)
    (hexact :
      ∀ v, v ∈ D → (G.Adj v r ↔ v = x ∨ v = y))
    (hcubic : ∀ v, v ∈ D → G.degree v = 3)
    (hDE : Disjoint D E)
    (hrE : r ∉ E)
    (hpartition : (D ∪ E) ∪ ({r} : Finset V) = Finset.univ)
    (hequal : D.card = E.card) :
    Even D.card ∧ Fintype.card V = 2 * D.card + 1 := by
  have hDeven :=
    (two_pole_cubic_even_order D r x y hrD hports hboundary hexact hcubic).2
  have hroot_disjoint : Disjoint (D ∪ E) ({r} : Finset V) := by
    apply Finset.disjoint_left.2
    intro v hvDE hvr
    rcases Finset.mem_union.mp hvDE with hvD | hvE
    · exact hrD (Finset.mem_singleton.mp hvr ▸ hvD)
    · exact hrE (Finset.mem_singleton.mp hvr ▸ hvE)
  have hcard := congrArg Finset.card hpartition
  rw [Finset.card_union_of_disjoint hroot_disjoint,
    Finset.card_union_of_disjoint hDE,
    Finset.card_singleton, Finset.card_univ] at hcard
  constructor
  · exact hDeven
  · omega

end Erdos64
