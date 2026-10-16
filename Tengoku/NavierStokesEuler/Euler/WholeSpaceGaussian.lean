import Tengoku.NavierStokesEuler.Euler.LpSmoothField
import Tengoku.NavierStokesEuler.Euler.LpParameterIntegral
import Tengoku

/-!
The normalized Gaussian on ordinary three-dimensional space.  The estimates
below concern the literal Bochner integral, including its L²-to-uniform bound.
The parameterization exp(-|x|²/t) has heat generator one quarter of the Laplacian.
-/

noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation Filter
open scoped ContDiff ENNReal RealInnerProductSpace

def normalization (t : ℝ) : ℝ := (Real.pi*t)^(-(3:ℝ)/2)

def kernel (t : ℝ) (x : Space) : ℝ :=
  normalization t * Real.exp (-t⁻¹*‖x‖^2)

section Averaging

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual whole-space Gaussian average, with no periodic identification. -/
def average (t : ℝ) (f : Space → V) (x : Space) : V :=
  ∫ y : Space, kernel t y • f (x+y)

end Averaging
end EulerWholeSpaceGaussian
