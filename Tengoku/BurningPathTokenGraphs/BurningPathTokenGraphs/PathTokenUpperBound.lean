import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.BlockBound
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.PathMetricGraphUpper

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Block upper bounds for the path-token burning number

The exact path-token metric converts the explicit ranked covers from `BlockCover` into graph
ranked covers. The burning-number bounds then follow from minimality.
-/

namespace BurningPath

/-- An explicit path-metric ranked cover is a ranked cover of the path-token graph.-/
theorem IsPathMetricRankedCover.isRankedCover_pathTokenGraph {n k t : ℕ}
    {centers : Fin t → Configuration (Fin n) k}
    (h : IsPathMetricRankedCover centers) :
    (pathTokenGraph n k).IsRankedCover centers := by
  intro A
  obtain ⟨r, hr⟩ := h A
  refine ⟨r, ?_⟩
  simp only [SimpleGraph.mem_closedBall,
    pathTokenGraph_edist_eq_pathConfigurationDist]
  exact_mod_cast hr

/-- An explicit path-metric ranked cover gives a feasible path-token burning length.-/
theorem HasPathMetricRankedCover.isBurningLength_pathTokenGraph
    [Nonempty (Configuration (Fin n) k)] {t : ℕ}
    (h : HasPathMetricRankedCover n k t) :
    (pathTokenGraph n k).IsBurningLength t := by
  obtain ⟨centers, hcover⟩ := h
  have hfin : Nonempty (Fin t) := by
    obtain ⟨r, _⟩ :=
      hcover (Classical.choice (inferInstance : Nonempty (Configuration (Fin n) k)))
    exact ⟨r⟩
  exact
    ⟨Fin.pos_iff_nonempty.mpr hfin, centers,
      hcover.isRankedCover_pathTokenGraph⟩

/-- Every admissible block length gives a finite upper bound for the path-token burning number.-/
theorem pathTokenBurningNumber_le_blockUpperBound {n k s : ℕ}
    (hk : k ≤ n) (hs : 1 ≤ s) :
    pathTokenBurningNumber n k hk ≤ blockUpperBound n k s := by
  letI := nonempty_configuration_of_le (Fin n) (by simpa using hk)
  change (pathTokenGraph n k).burningNumber ≤ blockUpperBound n k s
  apply (pathTokenGraph n k).burningNumber_min
  exact
    (hasPathMetricRankedCover_blockUpperBound hk hs).isBurningLength_pathTokenGraph

/--
Part (B), exact finite form: under `k + 1 ≤ n`, the path-token burning
number is at most the minimum of all admissible finite block bounds.-/
theorem pathTokenBurningNumber_le_optimalBlockUpperBound {n k : ℕ}
    (hnk : k + 1 ≤ n) :
    pathTokenBurningNumber n k ((Nat.le_add_right k 1).trans hnk) ≤
      optimalBlockUpperBound n k := by
  let hk : k ≤ n := (Nat.le_add_right k 1).trans hnk
  letI := nonempty_configuration_of_le (Fin n) (by simpa using hk)
  change (pathTokenGraph n k).burningNumber ≤ optimalBlockUpperBound n k
  have hn : 1 ≤ n := by omega
  obtain ⟨s, hs, _, hvalue⟩ :=
    optimalBlockUpperBound_spec (n := n) (k := k) hn
  rw [hvalue]
  apply (pathTokenGraph n k).burningNumber_min
  exact
    (hasPathMetricRankedCover_blockUpperBound hk hs).isBurningLength_pathTokenGraph

end BurningPath
