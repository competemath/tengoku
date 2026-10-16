import Tengoku.NavierStokesEuler.Euler.MildEquationBridge
import Tengoku.NavierStokesEuler.Euler.SobolevWordBlocks

/-! Every available finite derivative word of the actual viscous mild solution satisfies its differentiated L² equation. -/

noncomputable section

namespace EulerMildWordEquation

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerSobolevHeatGenerator EulerVolterraConvolution EulerDuhamelDifferentiation
  EulerMildEquationBridge EulerSobolevWordBlocks
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- Applying a bounded linear spatial map to an actual continuous Sobolev time path. -/
def mapPath {p q : ℕ} (T : ℝ) (A : SobolevSpace period q →L[ℝ] SobolevSpace period p)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period q)) : C(Icc (0 : ℝ) T, SobolevSpace period p) :=
  ⟨fun t => A (u t), A.continuous.comp u.continuous⟩

/-- Every bounded heat-commuting spatial map commutes with the actual Duhamel integral. -/
theorem map_duhamel {p q : ℕ} (A : SobolevSpace period q →L[ℝ] SobolevSpace period p)
    (hA : ∀ v u, A (heatOperator period q v u) = heatOperator period p v (A u))
    (ν T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (t : ℝ) :
    A (duhamel period ν T hT f t) = duhamel period ν T hT (mapPath period T A f) t := by
  unfold duhamel
  rw [← A.intervalIntegral_comp_comm ((shiftedHeat_continuous period ν T hT f t).intervalIntegrable 0 t)]
  apply intervalIntegral.integral_congr
  intro s _
  exact hA _ _

end EulerMildWordEquation
