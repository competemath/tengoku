import Tengoku.NavierStokesEuler.Euler.WholeSpaceGaussianKernel
import Tengoku

/-! Integration by parts for the literal whole-space Gaussian average. -/

noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter Set ContinuousLinearMap
open scoped ContDiff ENNReal RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

end EulerWholeSpaceGaussian
