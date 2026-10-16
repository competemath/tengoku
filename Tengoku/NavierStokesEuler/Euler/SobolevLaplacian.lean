import Tengoku.NavierStokesEuler.Euler.SobolevMetricTransport
import Tengoku.NavierStokesEuler.Euler.SobolevHeatGenerator
import Tengoku.NavierStokesEuler.Euler.SobolevRestriction

/-! The genuine commuting coordinate derivatives and bounded Laplacian on the complete Sobolev scale. -/

noncomputable section

namespace EulerSobolevLaplacian

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerCylinderSobolev EulerCylinderSobolevSpace EulerSobolevHeat EulerSobolevHeatGenerator
  EulerMollifierRepresentative EulerPressureSpatialRegularity EulerSpatialSobolevInverse EulerTransportDerivatives
open scoped Topology ContDiff ENNReal NNReal

variable (period : ℝ) [Fact (0 < period)]

end EulerSobolevLaplacian
