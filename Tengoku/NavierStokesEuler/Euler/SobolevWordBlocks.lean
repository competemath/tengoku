import Tengoku.NavierStokesEuler.Euler.SobolevRestriction
import Tengoku.NavierStokesEuler.Euler.SobolevHeat

/-! Bounded actual derivative-word blocks on the complete Sobolev scale. -/

noncomputable section

namespace EulerSobolevWordBlocks

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSobolevHeat EulerGaussianCylinderHeat EulerPressureSpatialRegularity
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- A derivative word as an actual bounded map H^(q+n)→Hq, with its literal differentiation order. -/
def wordBlock (q : ℕ) : (n : ℕ) → (Fin n → Fin 4) →
    SobolevSpace period (q + n) →L[ℝ] SobolevSpace period q
  | 0, _ => ContinuousLinearMap.id ℝ (SobolevSpace period q)
  | n + 1, w => (wordBlock q n (Fin.init w)).comp (derivativeOperator period (q + n) (w (Fin.last n)))

end EulerSobolevWordBlocks
