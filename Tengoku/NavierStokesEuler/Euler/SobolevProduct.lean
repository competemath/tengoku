import Tengoku.NavierStokesEuler.Euler.SobolevProductApproximation

/-! Actual pointwise multiplication on the complete cylinder Sobolev spaces Hq, q≥6. -/

noncomputable section

namespace EulerSobolevL2Product

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerSpatialSobolevInverse EulerMetricTransport
open scoped Topology ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

end EulerSobolevL2Product
