import Tengoku.NavierStokesEuler.Euler.SobolevL2Product
import Tengoku.NavierStokesEuler.Euler.SobolevRestriction

/-! Actual strong product jets from the genuine Sobolev-to-L² bilinear multiplication. -/

noncomputable section

namespace EulerSobolevL2Product

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerSpatialSobolevInverse
open scoped Topology ENNReal

variable (period : ℝ) [Fact (0 < period)]

end EulerSobolevL2Product
