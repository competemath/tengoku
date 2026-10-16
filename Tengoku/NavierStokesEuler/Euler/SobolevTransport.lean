import Tengoku.NavierStokesEuler.Euler.SobolevProduct

/-! Actual one-derivative-losing nonlinear transport on the complete cylinder Sobolev spaces. -/

noncomputable section

namespace EulerSobolevTransport

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerSobolevL2Product EulerMetricTransport EulerTransportDerivatives
open scoped Topology ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

local instance sobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
local instance sobolevRealSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

end EulerSobolevTransport
