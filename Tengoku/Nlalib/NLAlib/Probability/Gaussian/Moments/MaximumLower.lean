import Tengoku.Nlalib.NLAlib.Probability.Gaussian.Concentration.LowerTail
import Tengoku.Nlalib.NLAlib.Probability.Gaussian.Basic.StandardVector
import Tengoku.Seed.MeasureTheory.SpecificCodomains.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lower maxima of independent standard Gaussian coordinates

The scalar Gaussian lower tail and the exact product law give a uniform
positive probability of a maximum at the square-root logarithmic scale.
This is the lower maximal estimate used for selected independent entries
in Latała--van Handel--Youssef, arXiv:1711.00807v2, Section 3.1.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace NLAlib

/-- An explicit positive universal constant for lower expected Gaussian
coordinate maxima. Its exact value is immaterial to dimension-free bounds.-/
def gaussianMaximumLowerConstant : ℝ :=
  1 - Real.exp (-(Real.exp (-1) / Real.sqrt (2 * Real.pi)) / 2)

/-- The universal Gaussian maximum lower constant is strictly positive.
@isnad1 id=lt.0h0v.s3.1f494ac09b62 from=translated src=- shape=ff3a10fc vocab=9f98f4eb
-/
theorem gaussianMaximumLowerConstant_pos : 0 < gaussianMaximumLowerConstant := by
  unfold gaussianMaximumLowerConstant
  have hc : 0 < Real.exp (-1) / Real.sqrt (2 * Real.pi) := by positivity
  have h := Real.exp_lt_one_iff.mpr (show -(Real.exp (-1) / Real.sqrt (2 * Real.pi)) / 2 < 0 by linarith)
  linarith

end NLAlib
