import Tengoku.NavierStokesEuler.Euler.MeanTimeReflection
import Tengoku.NavierStokesEuler.Euler.MeanFixedSpaceInverse

/-!
# Reflection covariance of the full mean variational inverse

Every identity concerns the real time derivative, terminal primitive, initial
trace, and nonlocal boundary form. Uniqueness of the actual coercive inverse
then transports reflection without an assumed symmetry of a solution.
-/

noncomputable section

namespace EulerMeanFixedReflection

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerMeanSolenoidal
  EulerTimeLp EulerTerminalTimePrimitive EulerMeanTimeReflection EulerVolterraConvolution
  EulerMeanVariationalInverse EulerMeanFixedSpaceInverse EulerTimeH1OperatorProduct
  EulerCoerciveProjection

private local instance : NormedAddCommGroup L2 := inferInstance
private local instance : InnerProductSpace ℝ L2 := inferInstance
private local instance : NormedAddCommGroup solenoidalSpace := inferInstance
private local instance : InnerProductSpace ℝ solenoidalSpace := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup (TimeLp T L2) := inferInstance
private local instance (T : ℝ) : InnerProductSpace ℝ (TimeLp T L2) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup (TimeLp T solenoidalSpace) := inferInstance
private local instance (T : ℝ) : InnerProductSpace ℝ (TimeLp T solenoidalSpace) := inferInstance

def ReflectionInvariant (A : L2 →L[ℝ] L2) : Prop :=
  ∀ u, A (reflection u) = reflection (A u)

end EulerMeanFixedReflection
