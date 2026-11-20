import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.Burning
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Data.Set.Card.Arithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cardinality bounds from ranked covers

This is the finite-union counting step common to the exact volume lower bounds.
-/

open scoped BigOperators

namespace SimpleGraph

universe u

variable {V : Type u}

/--
If every radius-`r` ball has at most `f r` vertices, a ranked cover of length `t`
forces the whole graph to have at most `∑ r < t, f r` vertices.
@isnad1 id=le.2h5v.s6.9c405498a9f4 from=translated src=- shape=8fe82827 vocab=fbac517d
-/
theorem card_le_sum_ball_bound [Fintype V] {G : SimpleGraph V} {t : ℕ}
    {centers : Fin t → V} (hcover : G.IsRankedCover centers) (f : ℕ → ℕ)
    (hball : ∀ c r, (G.closedBall c r).ncard ≤ f r) :
    Fintype.card V ≤ ∑ r : Fin t, f r.1 := by
  let covered : Set V := ⋃ r : Fin t, G.closedBall (centers r) r.1
  have huniv : (Set.univ : Set V) ⊆ covered := by
    intro v _
    obtain ⟨r, hr⟩ := hcover v
    exact Set.mem_iUnion.2 ⟨r, hr⟩
  calc
    Fintype.card V = (Set.univ : Set V).ncard := by simp
    _ ≤ covered.ncard := Set.ncard_mono huniv
    _ ≤ ∑ r : Fin t, (G.closedBall (centers r) r.1).ncard := by
      simpa [covered] using
        (Finset.univ.set_ncard_biUnion_le fun r : Fin t ↦ G.closedBall (centers r) r.1)
    _ ≤ ∑ r : Fin t, f r.1 := Finset.sum_le_sum fun r _ ↦ hball (centers r) r.1

end SimpleGraph
