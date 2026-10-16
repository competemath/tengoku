import Tengoku.NavierStokesEuler.Euler.SobolevViscousEnergy
import Tengoku.NavierStokesEuler.Euler.WeightedCylinderEnergy

/-! Exact signed Gevrey integral energy for actual finite-Sobolev viscous solutions. -/

noncomputable section

namespace EulerWeightedSobolevEnergy

open MeasureTheory Set Real InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerCylinderSobolevSpace EulerMetricEnergyEvolution
  EulerMetricHeatEnergy EulerFiniteMetricEnergy EulerCylinderViscousEnergy EulerWeightedRootLimit
  EulerPacketWeights EulerWeightedEnergy EulerWeightedCylinderEnergy EulerSobolevMetricTransport
  EulerSobolevViscousEnergy
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

end EulerWeightedSobolevEnergy
