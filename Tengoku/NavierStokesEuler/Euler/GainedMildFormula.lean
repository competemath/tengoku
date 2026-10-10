import Tengoku.NavierStokesEuler.Euler.MildEquationBridge

/-! Equivalence between genuine gained-derivative and ordinary heat-Duhamel solution formulas. -/

noncomputable section

namespace EulerGainedMildFormula

open MeasureTheory Set EulerCylinderSobolevSpace EulerSobolevHeat EulerSobolevHeatGenerator
  EulerVolterraConvolution EulerDuhamelDifferentiation EulerMildEquationBridge
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

end EulerGainedMildFormula
