import Tengoku.NavierStokesEuler.Euler.HeatRegularizedPaths
import Tengoku.NavierStokesEuler.Euler.SobolevHeatDerivativeCommutation

/-! Genuine heat regularizations of the constructed mild solution satisfy the differentiated heat equation. -/

noncomputable section

namespace EulerRegularizedMildEquation

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerSobolevHeatGenerator EulerSobolevLaplacian EulerHeatRegularizedPaths
  EulerMildWordEquation EulerVolterraConvolution
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

end EulerRegularizedMildEquation
