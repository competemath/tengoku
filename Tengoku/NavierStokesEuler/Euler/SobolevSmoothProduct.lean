import Tengoku.NavierStokesEuler.Euler.SobolevProductJet
import Tengoku.NavierStokesEuler.Euler.GeneralRealCylinderAlgebra

/-! The genuine smooth product bound expressed in the complete cylinder Sobolev norm. -/

noncomputable section

namespace EulerSobolevL2Product

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerSpatialSobolevInverse EulerStrongSmoothJet EulerVectorCylinder
  EulerMetricTransport EulerGeneralCylinderAlgebra
open scoped Topology ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

/-- A fixed Sobolev-order algebra constant for the complete-array norm. -/
def sobolevProductConstant (q : ℕ) : ℝ :=
  (3 * algebraConstant period q) * (Fintype.card (SobolevWord q) : ℝ)^2

theorem sobolevProductConstant_nonneg (q : ℕ) : 0 ≤ sobolevProductConstant period q :=
  mul_nonneg (mul_nonneg (by norm_num) (algebraConstant_nonneg period q)) (sq_nonneg _)

end EulerSobolevL2Product
