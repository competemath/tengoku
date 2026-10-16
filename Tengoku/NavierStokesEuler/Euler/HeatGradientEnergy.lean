import Tengoku.NavierStokesEuler.Euler.SobolevLaplacian

/-! Genuine gradient energy and maximal-regularity estimates for smooth Sobolev heat solutions. -/

noncomputable section

namespace EulerHeatGradientEnergy

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerCylinderSobolev EulerCylinderSobolevSpace EulerSobolevLaplacian EulerSobolevHeatGenerator
  EulerLiftedWeakDerivative
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
/-- The scalar Young bound with the exact viscosity scaling used by maximal regularity. -/
theorem viscosity_young (ν x y : ℝ) (hν : 0 < ν) : 2*x*y ≤ ν*x^2 + ν⁻¹*y^2 := by
  have h := div_nonneg (sq_nonneg (ν*x-y)) hν.le
  have he : (ν*x-y)^2 / ν = ν*x^2 - 2*x*y + ν⁻¹*y^2 := by
    field_simp
    ring
  rw [he] at h
  linarith

end EulerHeatGradientEnergy
