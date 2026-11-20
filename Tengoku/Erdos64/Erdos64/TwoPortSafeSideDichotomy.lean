import Tengoku.Erdos64.Erdos64.HighDegreePortDescent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A boundary carrier with exactly two root ports either gives a strict
    minimum-degree-three induced side, or one of its ports is cubic. This
    isolates the genuine two-defect branch rather than assuming it away.
@isnad1 id=or.5h6v.s8.ec4c459568c5 from=translated src=- shape=85278e8c vocab=9b9641a7
-/
theorem two_port_safe_side_or_cubic_defect
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (D : Finset V) (r x y : V) (hD : D.Nonempty)
    (hr : r ∉ D)
    (hboundary : ∀ v, v ∈ D → ∀ w, w ∉ D → G.Adj v w → w = r)
    (hmin : G.minDegree ≥ 3)
    (hports : ∀ v, v ∈ D → (G.Adj v r ↔ v = x ∨ v = y)) :
    (G.induce (↑D : Set V)).minDegree ≥ 3 ∨
      G.degree x = 3 ∨ G.degree y = 3 := by
  by_cases hsafe : ∀ v, v ∈ D → G.Adj v r → 4 ≤ G.degree v
  · exact Or.inl (induced_minDegree_ge_three_of_high_degree_ports
      D r hD hboundary hmin hsafe)
  · right
    push_neg at hsafe
    obtain ⟨v, hvD, hvr, hvlt⟩ := hsafe
    have hvdeg : G.degree v = 3 := by
      have hvmin : 3 ≤ G.degree v :=
        degree_ge_three_of_minDegree_ge_three G hmin v
      omega
    rcases (hports v hvD).mp hvr with rfl | rfl
    · exact Or.inl hvdeg
    · exact Or.inr hvdeg

end Erdos64
