import Tengoku.NavierStokesEuler.Euler.MeanFrameCoefficients
import Tengoku.NavierStokesEuler.Euler.MeanMomentumBoundary
import Tengoku.NavierStokesEuler.Euler.TransverseStrongEquation

/-!
# The actual mean strong equation and initial velocity condition

The time variational solution is upgraded to genuine H² solenoidal coordinates
using its derived AC momentum and the constructed coercive Gram inverse. The
initial momentum trace then cancels the original M0 boundary term. The final
fields contain the actual projected equation (9) and `z_t(0)=L A z(0)`.
-/

noncomputable section

namespace EulerMeanVariationalInverse

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerTimeLp
  EulerTerminalTimePrimitive EulerMeanSolenoidal EulerVolterraConvolution
  EulerTransverseGramInverse EulerTransverseGramPath EulerTransverseCoordinateRegularity
  EulerTransverseMomentumRegularity EulerTransverseStrongAlgebra EulerTransverseStrongEquation

/-- The source's strong mean evolution, with actual time functions and actual
Bochner L² acceleration. Every derivative assertion concerns these functions. -/
structure StrongMeanEvolution (T : ℝ) (hT : 0 ≤ T)
    (FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (A : L2 →L[ℝ] L2) (L : ℝ) (u f : TimeLp T L2) where
  label : ℝ → solenoidalSpace
  velocity : ℝ → solenoidalSpace
  velocityLp : TimeLp T solenoidalSpace
  velocity_ae : (velocityLp : ℝ → solenoidalSpace) =ᵐ[timeMeasure T] velocity
  acceleration : TimeLp T solenoidalSpace
  label_eq : ∀ t : Icc (0 : ℝ) T,
    (label t : L2) = FInv t (realPrimitive T u t)
  label_ac : AbsolutelyContinuousOnInterval label 0 T
  velocity_ac : AbsolutelyContinuousOnInterval velocity 0 T
  terminal : label T = 0
  initial_velocity : (velocity 0 : L2) = L • A (label 0 : L2)
  label_derivative : ∀ᵐ t ∂timeMeasure T, HasDerivAt label (velocity t) t
  velocity_derivative : ∀ᵐ t ∂timeMeasure T, HasDerivAt velocity (acceleration t) t
  equation : ∀ᵐ t ∂timeMeasure T,
    solenoidalProjection ((extendPath T hT F t).adjoint
      (extendPath T hT F t (acceleration t : L2))) =
    solenoidalProjection ((extendPath T hT F t).adjoint
      (f t - (2 : ℝ) • extendPath T hT F₁ t (velocity t : L2)))

variable (T : ℝ) (hT : 0 ≤ T)
  (FInv F F₁ F₂ H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (M0 A : L2 →L[ℝ] L2) (L : ℝ)

end EulerMeanVariationalInverse
