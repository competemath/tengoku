import Tengoku.Piirrationalitymeasure.Formalization.CoefficientCharacteristic
import Tengoku.Piirrationalitymeasure.Formalization.GaussianPowerLimit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The centered tilted law satisfies the Gaussian expansion and power limit. -/

namespace PiIrrationality

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology

noncomputable def coefficientVariance (x : ℝ) : ℝ := x * deriv coefficientMean x

/--
@isnad1 id=memlp.2h1v.s6.bb949d15b69b from=translated src=- shape=4728236e vocab=d3ca697c
-/
theorem coefficientLaw_memLp_two {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    MemLp (fun k : ℕ => (k : ℝ)) 2 (coefficientLaw x hx0 hx1 1).toMeasure := by
  apply memLp_of_mem_interior_integrableExpSet _ 2
  exact coefficientLaw_interior_integrableExpSet hx0 hx1 (by simpa using hx1)

/--
@isnad1 id=memlp.2h1v.s6.ae30cbe36134 from=translated src=- shape=b7b6cce1 vocab=53cd11d1
-/
theorem coefficientCentered_memLp_two {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    MemLp (fun k : ℕ => (k : ℝ) - coefficientMean x) 2
      (coefficientLaw x hx0 hx1 1).toMeasure :=
  (coefficientLaw_memLp_two hx0 hx1).sub (memLp_const (coefficientMean x))

end PiIrrationality
