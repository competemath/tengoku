import Tengoku.NavierStokesEuler.Euler.LiftedTransportComponents
import Tengoku.NavierStokesEuler.Euler.CylinderSobolevDensity

/-! Genuine metric transport energy on finite Sobolev fields, obtained by smooth convolution limits. -/

noncomputable section

namespace EulerSobolevMetricTransport

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerCylinderSobolevSpace EulerSobolevL2Product
  EulerSobolevTransport EulerMollifierRepresentative EulerCylinderGradient
open scoped Topology ContDiff ENNReal NNReal

variable (period : ℝ) [Fact (0 < period)]

end EulerSobolevMetricTransport
