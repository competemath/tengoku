import Tengoku.NavierStokesEuler.Euler.QuadraticHeatLocal

/-! A uniform positive restart time for bounded data in the actual viscous Sobolev equation. -/

noncomputable section

namespace EulerUniformHeatLocal

open MeasureTheory Set EulerCylinderSobolevSpace EulerSobolevHeat EulerQuadraticSource
open scoped Topology

/-- A translated compact time window inside the prescribed coefficient interval. -/
def timeWindow {S : ℝ} (a T : ℝ) (ha : 0 ≤ a) (haT : a+T ≤ S) :
    C(Icc (0 : ℝ) T, Icc (0 : ℝ) S) where
  toFun t := ⟨a+t.val, by linarith [t.property.1], by linarith [t.property.2]⟩
  continuous_toFun := (continuous_const.add continuous_subtype_val).subtype_mk _

/-- The mass of the actual parabolic kernel bound is monotone in nonnegative time. -/
theorem parabolic_mass_mono (ν s t : ℝ) (hst : s ≤ t) :
    s + 2 * parabolicConstant ν * Real.sqrt s ≤ t + 2 * parabolicConstant ν * Real.sqrt t := by
  have hC := parabolicConstant_nonneg ν
  have hroot := Real.sqrt_le_sqrt hst
  nlinarith

variable (period : ℝ) [Fact (0 < period)]

end EulerUniformHeatLocal
