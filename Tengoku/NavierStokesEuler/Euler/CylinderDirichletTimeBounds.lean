import Tengoku.NavierStokesEuler.Euler.CylinderDirichletRegularity
import Tengoku.NavierStokesEuler.Euler.CylinderActionWords
import Tengoku.NavierStokesEuler.Euler.LpCylinderPathBounds
import Tengoku.NavierStokesEuler.Euler.TransverseFixedSobolev
import Tengoku.NavierStokesEuler.Euler.FixedEvolutionSobolev
import Tengoku.NavierStokesEuler.Euler.CylinderDirichletSobolev

/-!
# Genuine fixed-Sobolev bounds for the cylinder history inverse

The actual mixed translation orbit has identical fixed-base word norms at
every translation. Thus the forcing needs a bound only at zero. Coefficient
jets lift to L² operator paths with constant one, and the true fixed-space
inverse adds one shift while preserving the external radius.
-/

noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerTimeLp EulerTimeLpBoundedMap EulerMeanCoefficients EulerTransverseFixedSobolev
  EulerParameterWordGevrey EulerGevrey EulerFixedEvolutionSobolev
  EulerTimeLpGramSobolev EulerTimeLpAccelerationSobolev
open scoped BoundedContinuousFunction ContDiff

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)

private local instance : NormedAddCommGroup (CylinderL2 P U) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 P U) := inferInstance
private local instance : NormedAddCommGroup (CylinderL2 P E) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 P E) := inferInstance
private local instance : NormedAddCommGroup (CylinderL2 P U →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 P U →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedAddCommGroup (CylinderL2 P E →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 P E →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P U →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P U →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P E →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P E →L[ℝ] CylinderL2 P E) := inferInstance

variable {ι : Type*} [Fintype ι]
  (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (hQ : ContDiff ℝ ∞ (translateCoefficientPath D.Q))
  (hQ₁ : ContDiff ℝ ∞ (translateCoefficientPath D.Q₁))
  (hH : ContDiff ℝ ∞ (translateCoefficientPath D.H))
  (Rc C₀ C₁ CH Cf R : ℝ) (hRc : 0 ≤ Rc)
  (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hCH : 0 ≤ CH) (hCf : 0 ≤ Cf)
  (hbQ : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.Q) a‖ ≤ C₀*majorant Rc 0 n)
  (hbQ₁ : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.Q₁) a‖ ≤ C₁*majorant Rc 0 n)
  (hbH : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.H) a‖ ≤ CH*majorant Rc 0 n)
  (hRweak : 2*blockCost ι q T Rc C₀ C₁ CH D.lower Cf*(sobolevCoefficientRadius ι Rc+1) ≤ R)

  (hRstrong : 2*gramBlockCost ι q D.lower Rc C₀
    (accelerationBlockAmplitude ι q Rc C₀ C₁ Cf 1)*(sobolevCoefficientRadius ι Rc+1) ≤ R)

include hdir hQ hQ₁ hH hRc hC₀ hC₁ hCH hCf hbQ hbQ₁ hbH hRweak hRstrong

end EulerCylinderDirichlet.Coefficients
