import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.CoverCardinality
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.VolumePolynomial
import Tengoku.Seed.Algebra.BigOperators.Fin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Abstract exact volume lower bound

Once a graph's radius-`r` balls are bounded by the ambient lattice-ball polynomial, the exact
minimum in part (A) follows formally from ranked-cover counting.
-/

namespace BurningPath

universe u

variable {V : Type u}

/--
The exact volume threshold is a lower bound for the burning number of every finite nonempty graph
whose balls satisfy the stated Delannoy-polynomial bound.
@isnad1 id=le.1h3v.s5.853426842edc from=translated src=- shape=0af91d07 vocab=ce103864
-/
theorem volumeThreshold_le_burningNumber_of_ball_bound
    [Fintype V] [Nonempty V] (G : SimpleGraph V) (k : ℕ)
    (hball : ∀ c r, (G.closedBall c r).ncard ≤ latticeBallPolynomial k r) :
    volumeThreshold k (Fintype.card V) ≤ G.burningNumber := by
  apply volumeThreshold_min
  refine ⟨G.one_le_burningNumber, ?_⟩
  obtain ⟨centers, hcover⟩ := G.burningNumber_spec.2
  have hcard :=
    G.card_le_sum_ball_bound hcover (latticeBallPolynomial k) hball
  calc
    Fintype.card V ≤ cumulativeLatticeBallPolynomial k G.burningNumber := by
      simpa [cumulativeLatticeBallPolynomial, Fin.sum_univ_eq_sum_range] using hcard
    _ = rankedVolumePolynomial k G.burningNumber :=
      cumulativeLatticeBallPolynomial_eq k G.burningNumber

end BurningPath
