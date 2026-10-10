import Tengoku.NavierStokesEuler.Euler.WindowSource

/-! Exact continuation-by-pasting for the actual projected quadratic viscous equation. -/

noncomputable section

namespace EulerQuadraticMildPasting

open MeasureTheory Set EulerCylinderSobolevSpace EulerSobolevHeat EulerVolterraConvolution
  EulerUniformHeatLocal EulerQuadraticSource EulerTimePathGluing EulerGainedMildPasting EulerWindowSource
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

end EulerQuadraticMildPasting
