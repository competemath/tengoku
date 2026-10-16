import Tengoku.NavierStokesEuler.Euler.SobolevMetricTransport
import Tengoku.NavierStokesEuler.Euler.CylinderViscousEnergy
import Tengoku.NavierStokesEuler.Euler.SobolevRestriction

/-! Finite-family viscous metric energy for actual finite Sobolev solutions. -/

noncomputable section

namespace EulerSobolevViscousEnergy

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerCylinderSobolevSpace
  EulerMetricHeatEnergy EulerFiniteMetricEnergy EulerCylinderViscousEnergy EulerSobolevMetricTransport
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

end EulerSobolevViscousEnergy
