import Tengoku.NavierStokesEuler.Euler.SourceNormalCoefficient
import Tengoku.NavierStokesEuler.Euler.LpCylinderNormalBounds
import Tengoku.NavierStokesEuler.Euler.CylinderScalarPrimitive

/-!
# Source coefficient bounds for the actual pressure path

The normal inverse is constructed from m, and the angular primitive is the
actual bounded scalar cylinder operator. The resulting fixed-Hq estimate
uses one fixed external radius and adds no shift to its supplied inputs.
-/

noncomputable section

namespace EulerSourceNormalResidualBounds

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients
  EulerLpCylinderTranslation EulerLpCylinderRectangular EulerSourceNormalCoefficient
  EulerCylinderScalarPrimitive EulerParameterWordGevrey EulerGevrey EulerTimeLpGramGevrey
  EulerTransverseForwardCoefficientGevrey EulerOperatorGevreyCalculus
open scoped BoundedContinuousFunction ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {K ι : Type*} [TopologicalSpace K] [CompactSpace K] [Fintype ι]
  (M : SmoothCoefficientPath K (Space →L[ℝ] Space)) (m : SmoothCoefficientPath K Space)
  (cm : ℝ) (hcm : 0 < cm) (hm : ∀ t x, cm ≤ ‖m.field t x‖^2)
  (f v : C(K,CylinderL2 P Space))

def sourceResidual : C(K,CylinderL2 P ℝ) :=
  normalResidualPath P (normalFunctional m cm hcm hm) M.field f v

def sourcePressure : C(K,CylinderL2 P ℝ) :=
  pathPrimitive P (sourceResidual P M m cm hcm hm f v)

/-- An explicit fixed-order coefficient polynomial for the pressure source. -/
def pressureCost (ι : Type*) [Fintype ι] (q : ℕ) (Ri Cm CM Df Dv : ℝ) : ℝ :=
  3*sobolevCoefficientAmplitude ι q (4*Ri) (3*Ri*Cm)*
    (Df+6*sobolevCoefficientAmplitude ι q (4*Ri) CM*Dv)

end EulerSourceNormalResidualBounds
