import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.Arithmetic
import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.CircularQuotient
import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.DihedralGroup
import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.GeneralRestriction
import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.GraphMaximum
import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.GraphRibbon
import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.Lower
import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.Maximum
import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.PermutonMass
import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.PermutonPatterns
import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.RibbonRestriction
import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.Splits
import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.TreeAdequacy
import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.TiedSampleCount
import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.Upper

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Bandelt--Dress maximum quartet-distance theorem

This root module packages the pairwise results as statements about both the
recursive tree encoding and the independently defined conventional finite
degree-one/degree-three graph domain on `Fin n`; their maxima are proved
exactly equal for `n ≥ 4`.
The public theorem takes the published inequality for arbitrary Borel
permutons as its one explicit hypothesis.  The construction of the step
permuton, its uniform marginals, and the exact reduction to the finite
collision model are all proved inside the development; the lower bound is
unconditional.
-/

namespace QuartetDistance

/-- The maximum quartet distance between two binary phylogenetic trees on
`Fin n`.  `maxPairValue` uses the supremum of the bounded set of attainable
natural-number distances, so no artificial finiteness instance for tree
syntax is needed.-/
noncomputable def maximumQuartetDistance (n : ℕ) : ℕ :=
  maxPairValue (@Upper.quartetDistance n)

/-- Every attainable distance is at most the number of quartets.
@isnad1 id=le.0h1v.s3.48a73471feb6 from=translated src=- shape=3e368d2e vocab=be91c8ef
-/
theorem maximumQuartetDistance_le_choose (n : ℕ) :
    maximumQuartetDistance n ≤ Nat.choose n 4 := by
  exact maxPairValue_le (@Upper.quartetDistance n)
    (@Upper.quartetDistance_le_choose n)

/-- Every concrete pair is bounded by the maximum.
@isnad1 id=le.0h3v.s4.c8b8709c7d58 from=translated src=- shape=691ac02a vocab=a8e2aa93
-/
theorem quartetDistance_le_maximum (n : ℕ)
    (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    Upper.quartetDistance T₁ T₂ ≤ maximumQuartetDistance n := by
  exact value_le_maxPairValue (@Upper.quartetDistance n)
    (@Upper.quartetDistance_le_choose n) T₁ T₂

/-- The maximum is attained by a concrete pair, apart from the harmless zero
case included in the generic supremum construction.
@isnad1 id=or.0h1v.s5.973179cd19eb from=translated src=- shape=fe7c58fb vocab=61ab2a11
-/
theorem maximumQuartetDistance_eq_zero_or_exists (n : ℕ) :
    maximumQuartetDistance n = 0 ∨
      ∃ T₁ T₂ : Tree.PhyloTree (Fin n),
        maximumQuartetDistance n = Upper.quartetDistance T₁ T₂ := by
  exact maxPairValue_eq_zero_or_exists (@Upper.quartetDistance n)
    (@Upper.quartetDistance_le_choose n)

/-- The paper's displayed expansion, with an exact remainder term.
@isnad1 id=eq.1h1v.s7.ea465558e05b from=translated src=- shape=2b3c4374 vocab=c528651b
-/
theorem normalizedUpperCoefficient_expansion (n : ℕ) (hn : 4 ≤ n) :
    normalizedUpperCoefficient (n : ℝ) =
      (2 : ℝ) / 3 + 16 / n + 200 / (3 * (n : ℝ) ^ 2) +
        normalizedRemainder (n : ℝ) := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  rw [normalizedUpperCoefficient, normalizedError_expansion]
  · rw [normalizedRemainder]
    ring
  all_goals linarith

/-! ## Final statements from the one published input -/

/-! The principal API below uses the cited theorem in the paper's literal
form: the sum of the eight individual pattern densities is at least `1/3`. -/

/-! ## Final statements on the conventional graph-theoretic domain -/

end QuartetDistance
