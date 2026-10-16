import Tengoku.NavierStokesEuler.Euler.HeatGradientIntegral
import Tengoku.NavierStokesEuler.Euler.SobolevEllipticBound
import Tengoku.NavierStokesEuler.Euler.TimeLp

/-! A genuine L²-time H² estimate for regularized heat solutions, with only L² forcing. -/

noncomputable section

namespace EulerHeatMaximalEstimate

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevLaplacian
  EulerSobolevHeatGenerator EulerHeatGradientEnergy EulerSobolevEllipticBound EulerTimeLp
  EulerVolterraConvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
/-- Integrating a continuous scalar upper bound by a constant plus another continuous function. -/
theorem integral_le_constant_add (f g : ℝ → ℝ) (c T : ℝ) (hT : 0 ≤ T)
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ t ∈ Icc 0 T, f t ≤ c + g t) :
    (∫ t in (0 : ℝ)..T, f t) ≤ T*c + ∫ t in (0 : ℝ)..T, g t := by
  have h := intervalIntegral.integral_mono_on hT (hf.intervalIntegrable (μ := volume) 0 T)
    (((continuous_const (y := c)).add hg).intervalIntegrable (μ := volume) 0 T) hfg
  change (∫ t in (0 : ℝ)..T, f t) ≤ ∫ t in (0 : ℝ)..T, c + g t at h
  rw [intervalIntegral.integral_add (intervalIntegrable_const) (hg.intervalIntegrable (μ := volume) 0 T),
    intervalIntegral.integral_const] at h
  simpa only [sub_zero, smul_eq_mul] using h

end EulerHeatMaximalEstimate
