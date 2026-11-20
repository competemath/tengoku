import Tengoku.Erdos64.Erdos64.TwoPortSideCardBound

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Two disjoint closed two-port sides covering a minimal counterexample are
forced to have equal cardinality.  The two-port size bound applied to each
side leaves no room for an unequal partition.-/
theorem MinimalCounterexample.two_twoPort_sides_balanced
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (D E : Finset V) (r : V)
    (xD yD xE yE : V)
    (hrD : r ∉ D) (hrE : r ∉ E)
    (hdisj : Disjoint D E)
    (hcover : insert r (D ∪ E) = Finset.univ)
    (hboundaryD :
      ∀ v, v ∈ D → ∀ w, w ∉ D → G.Adj v w → w = r)
    (hboundaryE :
      ∀ v, v ∈ E → ∀ w, w ∉ E → G.Adj v w → w = r)
    (hportsD :
      xD ∈ D ∧ yD ∈ D ∧ xD ≠ yD ∧ G.Adj r xD ∧ G.Adj r yD)
    (hportsE :
      xE ∈ E ∧ yE ∈ E ∧ xE ≠ yE ∧ G.Adj r xE ∧ G.Adj r yE) :
    D.card = E.card := by
  have hDbound := M.two_port_side_card_bound D r xD yD hrD hportsD hboundaryD
  have hEbound := M.two_port_side_card_bound E r xE yE hrE hportsE hboundaryE
  have hrU : r ∉ D ∪ E := by
    simp only [Finset.mem_union, not_or]
    exact ⟨hrD, hrE⟩
  have hcard : (insert r (D ∪ E)).card = D.card + E.card + 1 := by
    rw [Finset.card_insert_of_notMem hrU,
      Finset.card_union_of_disjoint hdisj]
  have htotal : Fintype.card V = D.card + E.card + 1 := by
    calc
      Fintype.card V = (Finset.univ : Finset V).card :=
        (Finset.card_univ).symm
      _ = (insert r (D ∪ E)).card := by rw [hcover]
      _ = D.card + E.card + 1 := hcard
  omega

end Erdos64
