import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.SimplexPermutation
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lower half of the ordered-simplex density comparison

This formalizes equation (49) and the lower inequality in (48).
-/

namespace BurningPath

/-- Normalized simplex cover count, divided by simplex volume `L^k/k!`.-/
noncomputable def simplexCoverDensityAt (k : ℕ) (L : ℝ) : ℝ :=
  (simplexCoverNumber k L : ℝ) /
    (L ^ k / Nat.factorial k)

/-- Equation (49) in normalized form.
@isnad1 id=le.2h2v.s5.5fbfa22f02ff from=translated src=- shape=2ef6a13d vocab=8949d994
-/
theorem cubeCoverDensityAt_le_simplexCoverDensityAt {k : ℕ} {L : ℝ}
    (hk : 1 ≤ k) (hL : 0 < L) :
    cubeCoverDensityAt k L ≤ simplexCoverDensityAt k L := by
  exact cubeDensity_le_simplexDensity hk hL

/-- Every positive-side simplex density is at least the cube bulk density.
@isnad1 id=le.2h2v.s5.dafd4c8f5e5a from=translated src=- shape=33885082 vocab=0d4fd1e9
-/
theorem cubeBulkDensity_le_simplexCoverDensityAt {k : ℕ} {L : ℝ}
    (hk : 1 ≤ k) (hL : 0 < L) :
    cubeBulkDensity k ≤ simplexCoverDensityAt k L :=
  (cubeBulkDensity_le_densityAt hL).trans
    (cubeCoverDensityAt_le_simplexCoverDensityAt hk hL)

/-- Lower epsilon bound for the ordered-simplex cover number.
@isnad1 id=le.3h3v.s6.3e8e3e59abff from=translated src=- shape=ccda87cf vocab=c3de95ab
-/
theorem simplexCoverNumber_lower {k : ℕ} (hk : 2 ≤ k)
    {ε L : ℝ} (hε : 0 < ε) (hL : 0 < L) :
    (cubeBulkDensity k - ε) *
        (L ^ k / Nat.factorial k) ≤
      (simplexCoverNumber k L : ℝ) := by
  have hdensity :=
    cubeBulkDensity_le_simplexCoverDensityAt (show 1 ≤ k by omega) hL
  have hvolume : 0 < L ^ k / Nat.factorial k := by positivity
  unfold simplexCoverDensityAt at hdensity
  have hmul := (le_div_iff₀ hvolume).mp
    ((sub_le_self _ hε.le).trans hdensity)
  exact hmul

end BurningPath
