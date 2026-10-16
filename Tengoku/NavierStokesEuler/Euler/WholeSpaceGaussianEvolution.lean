import Tengoku.NavierStokesEuler.Euler.WholeSpaceGaussianTimeKernel
import Tengoku.NavierStokesEuler.Euler.WholeSpaceGaussianIntegration
import Tengoku.NavierStokesEuler.Euler.WholeSpaceGaussianScale

/-! The true heat-time evolution of Gaussian averaging on ordinary space. -/

noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter Set ContinuousLinearMap
open scoped ContDiff ENNReal RealInnerProductSpace Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def secondAverage (t : ℝ) (f : Space → V) (x : Space) : V :=
  ∑ i : Fin 3, average t (fun z =>
    fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) z
      (EuclideanSpace.single i 1)) x

end EulerWholeSpaceGaussian
