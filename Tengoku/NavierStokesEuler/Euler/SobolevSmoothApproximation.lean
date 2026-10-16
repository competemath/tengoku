import Tengoku.NavierStokesEuler.Euler.SobolevHeat
import Tengoku.NavierStokesEuler.Euler.CylinderSobolevDensity
import Tengoku.NavierStokesEuler.Euler.SobolevRestriction

/-! Smooth high-regularity approximations converging contractively in the original Sobolev order. -/

noncomputable section

namespace EulerCylinderSobolevSpace

open MeasureTheory EulerLiftedGradientSpace EulerMetricTransport EulerCylinderSobolev EulerCylinderMollifier
  EulerMollifierRepresentative EulerSobolevHeat EulerGaussianCylinderHeat EulerNoncompactTransport
open scoped Topology ContDiff NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- A positive Gaussian scale tending to zero. -/
def smoothingVariance (n : ℕ) : ℝ≥0 := (cutoffScale n).toNNReal

theorem smoothingVariance_pos (n : ℕ) : 0 < smoothingVariance n := Real.toNNReal_pos.mpr (cutoffScale_pos n)

theorem smoothingVariance_tendsto : Filter.Tendsto smoothingVariance Filter.atTop (𝓝 0) := by
  change Filter.Tendsto (fun n => (cutoffScale n).toNNReal) Filter.atTop (𝓝 (0 : ℝ≥0))
  have h := continuous_real_toNNReal.continuousAt.tendsto.comp cutoffScale_tendsto
  simpa only [Real.toNNReal_zero, Function.comp_def, smoothingVariance] using h

theorem contractive_comp_dist {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (M : X →L[ℝ] X) (hM : ∀ z, ‖M z‖ ≤ ‖z‖) (H u : X) :
    dist (M H) u ≤ dist H u + dist (M u) u := by
  have hd : dist (M H) (M u) ≤ dist H u := by
    simpa only [map_sub, ← dist_eq_norm] using hM (H-u)
  exact (dist_triangle (M H) (M u) u).trans (add_le_add hd (le_refl (dist (M u) u)))

end EulerCylinderSobolevSpace
