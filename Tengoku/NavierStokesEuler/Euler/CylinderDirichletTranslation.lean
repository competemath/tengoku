import Tengoku.NavierStokesEuler.Euler.CylinderDirichletNaturality
import Tengoku.NavierStokesEuler.Euler.MeanCoefficientPath

/-! The actual history solve commutes with all mixed spatial/angular translations. -/

noncomputable section

namespace EulerLpCylinderRectangular

open Set ContinuousLinearMap EulerLiftedGradientSpace EulerLpCylinderTranslation EulerMeanCoefficients
open scoped BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

end EulerLpCylinderRectangular

namespace EulerCylinderDirichlet.Coefficients

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerTimeLp EulerTimeLpBoundedMap EulerVolterraConvolution EulerMeanCoefficients
open scoped BoundedContinuousFunction

variable {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)

/-- The actual translated coefficient fields, with their inherited pointwise
time derivatives and unchanged coercivity constants. -/
def shifted (a : Space) : Coefficients T U E where
  time_pos := D.time_pos
  Q := translateCoefficientPath D.Q a
  Q₁ := translateCoefficientPath D.Q₁ a
  Q₂ := translateCoefficientPath D.Q₂ a
  H := translateCoefficientPath D.H a
  lower := D.lower
  lower_pos := D.lower_pos
  lower_bound t x v := D.lower_bound t (x+a) v
  derivative t ht x := D.derivative t ht (x+a)
  second_derivative t ht x := D.second_derivative t ht (x+a)
  jacobi t x v := D.jacobi t (x+a) v
  potential := D.potential
  potential_nonneg := D.potential_nonneg
  potential_bound t x v := D.potential_bound t (x+a) v
  small := D.small

variable (P : ℝ) [Fact (0 < P)]

omit [CompleteSpace U] [CompleteSpace E] in
theorem shifted_frame (a : LiftTangent) (t : Icc (0 : ℝ) T) (u : CylinderL2 P U) :
    (D.shifted a.1).frame P t (translate P a u) = translate P a (D.frame P t u) :=
  fullOperator_translation P a (D.Q t) u

omit [CompleteSpace U] [CompleteSpace E] in
theorem shifted_frameDerivative (a : LiftTangent) (t : Icc (0 : ℝ) T) (u : CylinderL2 P U) :
    (D.shifted a.1).frameDerivative P t (translate P a u) = translate P a (D.frameDerivative P t u) :=
  fullOperator_translation P a (D.Q₁ t) u

omit [CompleteSpace U] [CompleteSpace E] in
theorem shifted_hessian (a : LiftTangent) (t : Icc (0 : ℝ) T) (u : CylinderL2 P E) :
    (D.shifted a.1).hessian P t (translate P a u) = translate P a (D.hessian P t u) :=
  fullOperator_translation P a (D.H t) u

end EulerCylinderDirichlet.Coefficients
