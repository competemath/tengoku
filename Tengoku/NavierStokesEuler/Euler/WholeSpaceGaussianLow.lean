import Tengoku.NavierStokesEuler.Euler.WholeSpaceGaussianIntegration

/-! The low-frequency derivative of the true Gaussian average is controlled
by the ordinary L² norm of the original field. -/

noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter
open scoped ContDiff ENNReal RealInnerProductSpace

def lowCost : ℝ := Real.sqrt (8*normalization 1*(2:ℝ)^((3:ℝ)/2))

theorem lowCost_nonneg : 0 ≤ lowCost := Real.sqrt_nonneg _

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

end EulerWholeSpaceGaussian
