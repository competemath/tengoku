import Tengoku.NavierStokesEuler.Euler.WholeSpaceGaussian
import Tengoku

/-! Actual first and second Gaussian kernels and their integrable bounds. -/

noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter
open scoped ContDiff ENNReal RealInnerProductSpace

def wideKernel (t : ℝ) (x : Space) : ℝ :=
  normalization t * Real.exp (-(2*t)⁻¹*‖x‖^2)

def firstKernel (t : ℝ) (a x : Space) : ℝ :=
  (-2*t⁻¹*⟪x,a⟫_ℝ) * kernel t x

end EulerWholeSpaceGaussian
