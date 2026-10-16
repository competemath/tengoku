import Tengoku.NavierStokesEuler.Euler.SobolevRestriction
import Tengoku.NavierStokesEuler.Euler.SobolevHeat

/-! Bounded actual derivative-word blocks on the complete Sobolev scale. -/

noncomputable section

namespace EulerSobolevWordBlocks

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSobolevHeat EulerGaussianCylinderHeat EulerPressureSpatialRegularity
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

end EulerSobolevWordBlocks
