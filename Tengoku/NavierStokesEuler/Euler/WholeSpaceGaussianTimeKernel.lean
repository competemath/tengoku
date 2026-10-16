import Tengoku.NavierStokesEuler.Euler.WholeSpaceGaussianKernel
import Tengoku

/-! The literal time derivative of the Gaussian density and local domination. -/

noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter Set
open scoped ContDiff ENNReal RealInnerProductSpace Topology

def timeKernel (t : ℝ) (y : Space) : ℝ :=
  (t⁻¹^2*‖y‖^2-(3/2:ℝ)*t⁻¹)*kernel t y

def timeEnvelope (t : ℝ) (y : Space) : ℝ :=
  (15*t⁻¹*normalization (t/2))*Real.exp (-(4*t)⁻¹*‖y‖^2)

end EulerWholeSpaceGaussian
