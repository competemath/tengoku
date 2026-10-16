import Tengoku.NavierStokesEuler.Euler.HeatRestart
import Tengoku.NavierStokesEuler.Euler.SobolevSmoothApproximation

/-! Genuine heat regularization of continuous Sobolev paths, uniformly in time. -/

noncomputable section

namespace EulerHeatRegularizedPaths

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerGaussianCylinderHeat EulerMildWordEquation
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The total actual Gaussian variance of the regularizer. -/
def regularizerVariance (n : ℕ) : ℝ≥0 := smoothingVariance n + (smoothingVariance n + smoothingVariance n)

/-- The total regularizing variance tends to zero. -/
theorem regularizerVariance_tendsto : Filter.Tendsto regularizerVariance Filter.atTop (𝓝 0) := by
  change Filter.Tendsto (fun n => smoothingVariance n + (smoothingVariance n + smoothingVariance n)) Filter.atTop (𝓝 0)
  simpa only [add_zero] using
    smoothingVariance_tendsto.add (smoothingVariance_tendsto.add smoothingVariance_tendsto)

/-- Heat acting pointwise on a continuous Sobolev time path. -/
def pathHeat (q : ℕ) (T : ℝ) (v : ℝ≥0) (u : C(Icc (0 : ℝ) T, SobolevSpace period q)) :
    C(Icc (0 : ℝ) T, SobolevSpace period q) := mapPath period T (heatOperator period q v) u

/-- Strong heat continuity is uniform over every compact continuous time path. -/
theorem pathHeat_continuous {q : ℕ} (T : ℝ) (u : C(Icc (0 : ℝ) T, SobolevSpace period q)) :
    Continuous (fun v : ℝ≥0 => pathHeat period q T v u) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact Continuous.comp
    (g := fun p : ℝ≥0 × SobolevSpace period q => heatOperator period q p.1 p.2)
    (f := fun p : ℝ≥0 × Icc (0 : ℝ) T => (p.1, u p.2))
    (heatOperator_joint_continuous period q) (continuous_fst.prodMk (u.continuous.comp continuous_snd))

end EulerHeatRegularizedPaths
