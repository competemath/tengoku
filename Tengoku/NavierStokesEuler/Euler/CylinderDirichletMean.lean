import Tengoku.NavierStokesEuler.Euler.CylinderDirichletNaturality
import Tengoku.NavierStokesEuler.Euler.CylinderAngleAverage
import Tengoku.NavierStokesEuler.Euler.TimeLpLinearity

/-!
# Actual zero angular mean of the history solution

Angle-independent coefficients commute with the genuine cylinder average,
including the adjoint test maps. The constructed inverse and its continuous
velocity therefore preserve zero mean. No pointwise mean condition is assumed
on the solution.
-/

noncomputable section

namespace EulerLpCylinderRectangular

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerCylinderAngleAverage
  EulerBoundedFieldCalculus
open scoped BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem fullOperatorMap_adjoint (Q : Space →ᵇ U →L[ℝ] E) :
    (fullOperatorMap P Q).adjoint = fullOperatorMap P (adjointMap Q) := by
  change (EulerLpOperatorField.full (liftMeasure P) (fieldLift P Q)).adjoint = _
  rw [EulerLpOperatorField.full_adjoint]
  rfl

end EulerLpCylinderRectangular

namespace EulerCylinderDirichlet.Coefficients

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerLpCylinderTranslation
  EulerLpCylinderRectangular EulerCylinderAngleAverage EulerTimeLp EulerTimeLpBoundedMap
  EulerTransverseGramInverse

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)

theorem accelerationPath_zero (t : Icc (0 : ℝ) T) : D.accelerationPath P 0 t = 0 := by
  have hz : pathLp T D.time_pos.le (0 : C(Icc (0 : ℝ) T,CylinderL2 P E)) = 0 :=
    map_zero (pathLpOperator T D.time_pos.le)
  change gramInverse (D.frame P t) D.lower D.lower_pos (D.frame_lower P t)
    ((D.frame P t).adjoint (0-(2 : ℝ) • D.frameDerivative P t
      (D.velocityPath P (pathLp T D.time_pos.le 0) t))) = 0
  rw [hz]
  simp only [map_zero,ContinuousMap.zero_apply,smul_zero,sub_zero]

theorem physicalVelocity_zero (t : Icc (0 : ℝ) T) : D.physicalVelocity P 0 t = 0 := by
  have hz : pathLp T D.time_pos.le (0 : C(Icc (0 : ℝ) T,CylinderL2 P E)) = 0 :=
    map_zero (pathLpOperator T D.time_pos.le)
  change D.frame P t (D.velocityPath P (pathLp T D.time_pos.le 0) t) = 0
  rw [hz]
  simp only [map_zero,ContinuousMap.zero_apply]

theorem physicalDerivative_zero (t : Icc (0 : ℝ) T) : D.physicalDerivative P 0 t = 0 := by
  have hz : pathLp T D.time_pos.le (0 : C(Icc (0 : ℝ) T,CylinderL2 P E)) = 0 :=
    map_zero (pathLpOperator T D.time_pos.le)
  change D.frameDerivative P t (D.velocityPath P (pathLp T D.time_pos.le 0) t)+
    D.frame P t (D.accelerationPath P 0 t) = 0
  rw [hz,D.accelerationPath_zero P t]
  simp only [map_zero,ContinuousMap.zero_apply,add_zero]

variable (f : C(Icc (0 : ℝ) T,CylinderL2 P E)) (hf : ∀ t, average P (f t) = 0)

end EulerCylinderDirichlet.Coefficients
