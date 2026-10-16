import Tengoku.NavierStokesEuler.Euler.WholeSpaceGaussianKernel
import Tengoku

/-! The same Gaussian average as a continuous dilation of a fixed kernel. -/

noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter Set
open scoped ContDiff ENNReal RealInnerProductSpace Topology

section Averaging

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- This formula continues the actual heat average to t=0 by dilation. -/
def scaledAverage (t : ℝ) (f : Space → V) (x : Space) : V :=
  ∫ y : Space, kernel 1 y • f (x+Real.sqrt t • y)

end Averaging
end EulerWholeSpaceGaussian
