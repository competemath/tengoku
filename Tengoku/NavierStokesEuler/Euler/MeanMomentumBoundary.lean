import Tengoku.NavierStokesEuler.Euler.MeanMomentumRegularity
import Tengoku.NavierStokesEuler.Euler.TimeWeakBoundary

/-!
# The mean variational solve determines its actual initial momentum trace

All solenoidal terminal-H¹ tests, including those nonzero initially, identify
an explicit AC momentum representative. Its initial value is the adjoint
frame applied to the original `M0 + L A` boundary force.
-/

noncomputable section

namespace EulerMeanVariationalInverse

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerTimeLp
  EulerTerminalTimePrimitive EulerMeanSolenoidal EulerVolterraConvolution
  EulerTimeH1OperatorProduct EulerTransverseMomentumRegularity EulerTimeWeakBoundary

-- Cache the nested Hilbert-space instances used throughout the operator identities.
private local instance : NormedAddCommGroup solenoidalSpace := inferInstance
private local instance : InnerProductSpace ℝ solenoidalSpace := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup (TimeLp T L2) := inferInstance
private local instance (T : ℝ) : InnerProductSpace ℝ (TimeLp T L2) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup (TimeLp T solenoidalSpace) := inferInstance
private local instance (T : ℝ) : InnerProductSpace ℝ (TimeLp T solenoidalSpace) := inferInstance

variable (T : ℝ) (hT : 0 ≤ T)
  (FInv F F' : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))

/-- The original initial boundary force, expressed in the actual solenoidal coordinate space. -/
def meanBoundaryFlux (M0 A : L2 →L[ℝ] L2) (L : ℝ) (u : meanDerivatives T hT FInv) :
    solenoidalSpace :=
  (solenoidalFrame T F ⟨0, le_rfl, hT⟩).adjoint
    ((M0+L • A) (meanTrace T hT FInv u))

end EulerMeanVariationalInverse
