import Tengoku.Twinprime.TwinPrime.Analytic.CharacterTypeIMean
import Tengoku.Twinprime.TwinPrime.Analytic.VaughanMeanParameters
import Tengoku.Twinprime.TwinPrime.Analytic.ConductorMean
import Tengoku.Twinprime.TwinPrime.Analytic.ConductorReduction
import Tengoku.Twinprime.TwinPrime.Analytic.SmallConductorMean

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A proved primitive-character mean value and conductor tail

Eighth-root internal cutoffs turn the finite Vaughan estimates into a
six-logarithm mean bound in the required modulus range. The proved Abel
identity then controls the large-conductor tail. No character mean-value
or distribution estimate is an argument of these theorems.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/-- Explicit budget after the reciprocal-conductor Abel sum.-/
def bvLargeConductorBudget (T R₀ Q : ℕ) : ℝ :=
  bvMeanConstant * (Real.log T) ^ 6 *
    ((T : ℝ) / R₀ + (T : ℝ) ^ (15 / 16 : ℝ) * (1 + Real.log ((Q : ℝ) / R₀)) +
      2 * Real.sqrt T * Q)

end TwinPrime.Analytic
