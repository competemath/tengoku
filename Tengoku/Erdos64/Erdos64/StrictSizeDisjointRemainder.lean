import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A nonempty side no larger than its disjoint remainder has strict rooted
doubling order.-/
theorem strict_size_of_disjoint_remainder
    {V : Type u} [Fintype V] [DecidableEq V]
    (D E : Finset V)
    (hD : D.Nonempty)
    (hpartition : D ∪ E = Finset.univ)
    (hdisjoint : Disjoint D E)
    (hsmall : D.card ≤ E.card) :
    2 * D.card - 1 < Fintype.card V := by
  have hcard : Fintype.card V = D.card + E.card := by
    rw [← Finset.card_univ, ← hpartition]
    exact Finset.card_union_of_disjoint hdisjoint
  have hDcard : 1 ≤ D.card := Finset.card_pos.mpr hD
  omega

end Erdos64
