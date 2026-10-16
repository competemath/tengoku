import Tengoku.NavierStokesEuler.Euler.SobolevHeatKernel
import Tengoku.NavierStokesEuler.Euler.VolterraFixedPoint

/-! The actual cylinder heat kernel in the singular Volterra existence theorem. -/

noncomputable section

namespace EulerSobolevHeat

open EulerCylinderSobolevSpace EulerVolterraConvolution EulerGaussianCylinderHeat MeasureTheory Set
open scoped Topology NNReal

/-- Positive physical time converted to positive Gaussian variance for viscosity ν. -/
def positiveVariance (ν : ℝ) (hν : 0 < ν) (t : {t : ℝ // 0 < t}) : {v : ℝ≥0 // 0 < v} :=
  ⟨⟨2 * ν * t.val, by have ht := t.property; positivity⟩,
    by change (0 : ℝ) < 2 * ν * t.val; have ht := t.property; positivity⟩

/-- Physical time to Gaussian variance is continuous on positive times. -/
theorem positiveVariance_continuous (ν : ℝ) (hν : 0 < ν) : Continuous (positiveVariance ν hν) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_const.mul continuous_subtype_val

variable (period : ℝ) [Fact (0 < period)]

/-- The free viscous heat evolution is an actual continuous path in every Sobolev space. -/
def freeHeatPath (q : ℕ) (ν T : ℝ) (u₀ : SobolevSpace period q) : C(Icc (0 : ℝ) T, SobolevSpace period q) where
  toFun t := heatOperator period q (2 * ν * t.val).toNNReal u₀
  continuous_toFun := (heatOperator_continuous period u₀).comp
    (continuous_real_toNNReal.comp (continuous_const.mul continuous_subtype_val))

/-- The free heat path obeys the initial-data bound in the actual uniform Sobolev norm. -/
theorem freeHeatPath_bound (q : ℕ) (ν T : ℝ) (u₀ : SobolevSpace period q) :
    ‖freeHeatPath period q ν T u₀‖ ≤ ‖u₀‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u₀)).mpr
  intro t
  exact heatOperator_bound period _ u₀

end EulerSobolevHeat
