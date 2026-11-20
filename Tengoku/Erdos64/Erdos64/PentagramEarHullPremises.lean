import Tengoku.Erdos64.Erdos64.Basic
import Tengoku.Erdos64.Erdos64.PentagramEarHull

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

namespace PentagramEarHull

variable {V : Type u} {G : SimpleGraph V}

/- Minimum degree supplies a neighbor of each `b` vertex beyond the two
   attachment vertices already forced by the hull.  This does not claim that
   the new neighbor is outside the whole hull. -/
theorem exists_b_neighbor_outside_two_attachments
    (H : PentagramEarHull G)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hmin : G.minDegree ≥ 3) (i : Fin 5) :
    ∃ w, G.Adj (H.bVertex i) w ∧
      w ≠ H.aVertex i ∧ w ≠ H.aVertex (i + 2) := by
  classical
  let v : V := H.bVertex i
  let x : V := H.aVertex i
  let y : V := H.aVertex (i + 2)
  have hdeg : 3 ≤ (G.neighborFinset v).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact degree_ge_three_of_minDegree_ge_three G hmin v
  by_contra hnone
  push Not at hnone
  have hsub : G.neighborFinset v ⊆ ({x, y} : Finset V) := by
    intro w hw
    have hwAdj : G.Adj v w := (G.mem_neighborFinset v w).1 hw
    have hcases := hnone w hwAdj
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hwx : w = x
    · exact Or.inl hwx
    · exact Or.inr (hcases hwx)
  have hcard := Finset.card_le_card hsub
  have hpair : ({x, y} : Finset V).card ≤ 2 := by
    by_cases hxy : x = y
    · simp [hxy]
    · simp [Finset.card_insert_of_notMem, hxy]
  omega

end PentagramEarHull

end Erdos64
