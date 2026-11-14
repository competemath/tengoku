import Tengoku.Piirrationalitymeasure.Formalization.CoefficientCharacteristic
import Tengoku.Piirrationalitymeasure.Formalization.GaussianPowerLimit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The centered tilted law satisfies the Gaussian expansion and power limit. -/

namespace PiIrrationality

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology

noncomputable def coefficientVariance (x : ℝ) : ℝ := x * deriv coefficientMean x

theorem coefficientLaw_memLp_two {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    MemLp (fun k : ℕ => (k : ℝ)) 2 (coefficientLaw x hx0 hx1 1).toMeasure := by
  apply memLp_of_mem_interior_integrableExpSet _ 2
  exact coefficientLaw_interior_integrableExpSet hx0 hx1 (by simpa using hx1)

theorem coefficientCentered_memLp_two {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    MemLp (fun k : ℕ => (k : ℝ) - coefficientMean x) 2
      (coefficientLaw x hx0 hx1 1).toMeasure :=
  (coefficientLaw_memLp_two hx0 hx1).sub (memLp_const (coefficientMean x))

end PiIrrationality
