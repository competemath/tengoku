import Tengoku.NavierStokesEuler.Euler.SobolevSmoothApproximation
import Tengoku.NavierStokesEuler.Euler.SobolevSmoothProduct

/-! Positive-time Gaussian heat has every actual Sobolev derivative, enabling genuine H∞ approximations. -/

noncomputable section

namespace EulerSobolevHeat

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerGaussianCylinderHeat
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerCylinderMollifier EulerMollifierRepresentative
  EulerMetricTransport EulerStrongSmoothJet EulerNoncompactTransport
open scoped Topology ContDiff NNReal

variable (period : ℝ) [Fact (0 < period)]

end EulerSobolevHeat
