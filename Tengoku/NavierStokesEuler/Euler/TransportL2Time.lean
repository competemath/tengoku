import Tengoku.NavierStokesEuler.Euler.SobolevMetricTransport
import Tengoku.NavierStokesEuler.Euler.TimeLpMultiplier

/-! Genuine time-continuous transport operators at the H¹→L² metric-energy level. -/

noncomputable section

namespace EulerTransportL2Time

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevMetricTransport
  EulerSobolevL2Product EulerSobolevTransport EulerTimeLp EulerVolterraConvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A named local normed-group instance for the actual Sobolev scale. -/
local instance transportL2Group (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance

/-- A named local real normed-space instance for the actual Sobolev scale. -/
local instance transportL2Space (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

end EulerTransportL2Time
