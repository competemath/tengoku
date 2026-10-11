import Tengoku.NavierStokesEuler.Euler.MeanOperatorReflection

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

variable (T : ℝ) (hT : 0 ≤ T)
  (F F₁ H : C(Icc (0 : ℝ) T,L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2) (L : ℝ)
  (hF : ∀ t, ReflectionInvariant (F t)) (hF₁ : ∀ t, ReflectionInvariant (F₁ t))
  (hH : ∀ t, ReflectionInvariant (H t)) (hM0 : ReflectionInvariant M0) (hA : ReflectionInvariant A)

end EulerMeanFixedReflection
