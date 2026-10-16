import Tengoku.NavierStokesEuler.Euler.CylinderAngleAverage
import Tengoku.NavierStokesEuler.Euler.CylinderAngleRepresentative

/-! The actual L² angular average equals the literal mean of every continuous H³ representative. -/

noncomputable section

namespace EulerCylinderAngleAverage

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerSobolevPointEvaluation EulerSpatialSobolevInverse EulerPressureSpatialRegularity
  EulerLpCylinderTranslation

variable (P : ℝ) [Fact (0 < P)]

theorem sobolevAngleCurve_continuous {q : ℕ} (u : SobolevSpace P q) :
    Continuous (fun s : ℝ => sobolevTranslation P q (EulerCylinderAnglePrimitive.angleShift P s) u) :=
  (sobolevTranslation_continuous P u).comp (EulerCylinderAnglePrimitive.angleShift_continuous P)

end EulerCylinderAngleAverage
