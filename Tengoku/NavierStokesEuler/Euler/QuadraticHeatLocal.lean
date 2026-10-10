import Tengoku.NavierStokesEuler.Euler.QuadraticCoefficients

/-! Positive-time existence for the actual projected quadratic cylinder correction equation. -/

noncomputable section

namespace EulerQuadraticSource

open MeasureTheory Set EulerCylinderSobolevSpace EulerSobolevHeat
open scoped Topology

/-- Inclusion of a shorter initial time interval into a prescribed positive interval. -/
def timeInclusion {T S : ℝ} (hTS : T ≤ S) : C(Icc (0 : ℝ) T, Icc (0 : ℝ) S) where
  toFun t := ⟨t.val, t.property.1, t.property.2.trans hTS⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

variable (period : ℝ) [Fact (0 < period)]

local instance sobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
local instance sobolevRealSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

end EulerQuadraticSource
