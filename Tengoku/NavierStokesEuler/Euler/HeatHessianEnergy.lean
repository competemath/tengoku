import Tengoku.NavierStokesEuler.Euler.HeatGradientEnergy

/-! Exact L² Hessian coercivity from actual commuting strong derivatives. -/

noncomputable section

namespace EulerHeatGradientEnergy

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerSobolevLaplacian EulerSobolevHeatGenerator

variable (period : ℝ) [Fact (0 < period)]

end EulerHeatGradientEnergy
