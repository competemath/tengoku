import Tengoku.NavierStokesEuler.Euler.HeatGradientEnergy

/-! Integrated genuine heat gradient energy, with the source measured only in L². -/

noncomputable section

namespace EulerHeatGradientEnergy

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerSobolevLaplacian EulerSobolevHeatGenerator
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

end EulerHeatGradientEnergy
