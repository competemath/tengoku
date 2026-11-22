import Tengoku.NavierStokesEuler.Euler.CylinderEndpointData
import Tengoku.NavierStokesEuler.Euler.TransverseSourceCoefficientPath

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Evaluation of the actual cylinder coefficients at a spatial label. -/

noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerVolterraConvolution
  EulerTransverseSourceCoefficientPath EulerTransverseEndpointCoordinates
open scoped BoundedContinuousFunction

variable {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)

def labelFrame (x : Space) : C(Icc (0 : ℝ) T,U →L[ℝ] E) := pathEvaluation x D.Q
def labelFrameDerivative (x : Space) : C(Icc (0 : ℝ) T,U →L[ℝ] E) := pathEvaluation x D.Q₁
def labelFrameSecond (x : Space) : C(Icc (0 : ℝ) T,U →L[ℝ] E) := pathEvaluation x D.Q₂
def labelHessian (x : Space) : C(Icc (0 : ℝ) T,E →L[ℝ] E) := pathEvaluation x D.H

omit [CompleteSpace U] [CompleteSpace E] in
/--
@isnad1 id=le.0h7v.s9.0aa9192ba12d from=translated src=- shape=7658816e vocab=d6f228f2
-/
theorem labelFrame_lower (x : Space) (t : Icc (0 : ℝ) T) (v : U) :
    D.lower*‖v‖^2 ≤ ‖D.labelFrame x t v‖^2 := D.lower_bound t x v

omit [CompleteSpace U] [CompleteSpace E] in
/--
@isnad1 id=hasderiv.0h6v.s9.1ee000e2a7c1 from=translated src=- shape=994d4f89 vocab=90c18b4a
-/
theorem labelFrame_derivative (x : Space) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T D.time_pos.le (D.labelFrame x))
      (D.labelFrameDerivative x t) (Icc (0 : ℝ) T) t := by
  change HasDerivWithinAt (fun s => D.Q (projIcc 0 T D.time_pos.le s) x)
    (D.Q₁ t x) (Icc (0 : ℝ) T) t
  simpa only [extendPath,projIcc_of_mem D.time_pos.le t.property] using D.derivative t t.property x

omit [CompleteSpace U] [CompleteSpace E] in
/--
@isnad1 id=hasderiv.0h6v.s9.f253a3cc6de5 from=translated src=- shape=994d4f89 vocab=c244e6e2
-/
theorem labelFrame_second_derivative (x : Space) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T D.time_pos.le (D.labelFrameDerivative x))
      (D.labelFrameSecond x t) (Icc (0 : ℝ) T) t := by
  change HasDerivWithinAt (fun s => D.Q₁ (projIcc 0 T D.time_pos.le s) x)
    (D.Q₂ t x) (Icc (0 : ℝ) T) t
  simpa only [extendPath,projIcc_of_mem D.time_pos.le t.property] using D.second_derivative t t.property x

omit [CompleteSpace U] [CompleteSpace E] in
/--
@isnad1 id=eq.0h6v.s10.9a254b1f7282 from=translated src=- shape=124eda78 vocab=1156d421
-/
theorem labelFrame_equation (x : Space) (t : Icc (0 : ℝ) T) :
    D.labelFrameSecond x t = -((D.labelHessian x t).comp (D.labelFrame x t)) := by
  apply ContinuousLinearMap.ext
  intro v
  exact D.jacobi t x v

omit [CompleteSpace U] [CompleteSpace E] in
/--
@isnad1 id=le.0h7v.s9.130a726d3b60 from=translated src=- shape=7d197edb vocab=17bd8c79
-/
theorem labelHessian_upper (x : Space) (t : Icc (0 : ℝ) T) (v : E) :
    ⟪D.labelHessian x t v,v⟫_ℝ ≤ D.potential*‖v‖^2 := D.potential_bound t x v

/-- The already constructed finite-dimensional stationary history, at this
label, applied to an ordinary terminal coordinate. -/
def labelCoordinate (x : Space) : U →L[ℝ] C(Icc (0 : ℝ) T,U) :=
  continuousCoordinateVelocity T D.time_pos.le (D.labelFrame x) (D.labelFrameDerivative x)
    (D.labelHessian x) D.lower D.lower_pos (D.labelFrame_lower x) (D.labelFrame_derivative x)
    D.potential D.potential_nonneg (D.labelHessian_upper x) D.small

def labelVelocity (x : Space) : U →L[ℝ] C(Icc (0 : ℝ) T,E) :=
  historyVelocity T D.time_pos.le (D.labelFrame x) (D.labelFrameDerivative x)
    (D.labelHessian x) D.lower D.lower_pos (D.labelFrame_lower x) (D.labelFrame_derivative x)
    D.potential D.potential_nonneg (D.labelHessian_upper x) D.small

/--
@isnad1 id=eq.0h7v.s11.a67465b50508 from=translated src=- shape=1b3d4c49 vocab=4ad94551
-/
theorem labelVelocity_apply (x : Space) (Y : U) (t : Icc (0 : ℝ) T) :
    D.labelVelocity x Y t = D.Q t x (D.labelCoordinate x Y t) := rfl

end EulerCylinderDirichlet.Coefficients
