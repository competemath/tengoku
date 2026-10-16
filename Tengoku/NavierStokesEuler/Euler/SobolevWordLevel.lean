import Tengoku.NavierStokesEuler.Euler.SobolevWordBlocks
import Tengoku.NavierStokesEuler.Euler.SobolevGevreyOperators

/-! Actual derivative words at any lower Sobolev level, with exact representative and norm identities. -/

noncomputable section

namespace EulerSobolevWordLevel

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerMetricTransport EulerSobolevWordBlocks EulerH6Pressure EulerStrongSmoothJet
  EulerSobolevGevreyOperators
open scoped ContDiff Topology

variable (period : ℝ) [Fact (0 < period)]

end EulerSobolevWordLevel
