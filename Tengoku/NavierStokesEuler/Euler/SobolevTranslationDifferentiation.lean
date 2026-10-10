import Tengoku.NavierStokesEuler.Euler.CylinderSobolevDerivatives

/-! Translation is strongly differentiable in the actual Sobolev topology with one more derivative. -/

noncomputable section

namespace EulerCylinderSobolevSpace

open EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

end EulerCylinderSobolevSpace
