import Tengoku.NavierStokesEuler.Euler.SourceCylinderForcing
import Tengoku.NavierStokesEuler.Euler.LpCylinderTimeWeight
import Tengoku.NavierStokesEuler.Euler.OperatorGevreyCalculus

/-!
# Same-radius bounds for the actual forward time right side

The coordinate and physical right sides are the literal bounded coefficient
expressions in (12) and its physical reconstruction. They preserve the input
external radius and shift. Scalar time weights commute with these expressions;
in particular no derivative of the positive profile is used.
-/

noncomputable section

namespace EulerSourceCylinderTimeBounds

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderRectangular
  EulerSourceCylinderForcing EulerSourceForwardCoefficient EulerTransverseForwardCoefficientGevrey
  EulerOperatorGevreyCalculus EulerGevrey EulerParameterWordGevrey EulerTimeLpGramGevrey
  EulerContinuousTimeWeight
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]
  {K U E ι : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]
  (S : Set Space) (hS : MeasurableSet S)
  (Q Q₁ : SmoothCoefficientPath K (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q.field t x v‖^2)
  (f : C(K,Supported P E S hS)) (a : C(K,Supported P U S hS))

def coordinateRhs : C(K,Supported P U S hS) :=
  supportedMultiplierMap P S hS (sourceGenerator Q Q₁ c hc hQ) a+
    projectedForcing P S hS Q c hc hQ f

def physicalRhs : C(K,Supported P E S hS) :=
  supportedMultiplierMap P S hS Q₁.field a+
    supportedMultiplierMap P S hS Q.field (coordinateRhs P S hS Q Q₁ c hc hQ f a)

def coordinateCost (ι : Type*) [Fintype ι] (q : ℕ) (Ri C₀ C₁ Df Da : ℝ) : ℝ :=
  3*sobolevCoefficientAmplitude ι q (4*Ri) (18*Ri*C₀*C₁)*Da+
    3*sobolevCoefficientAmplitude ι q (4*Ri) (3*Ri*C₀)*Df

def physicalCost (ι : Type*) [Fintype ι] (q : ℕ) (Ri C₀ C₁ Df Da : ℝ) : ℝ :=
  3*sobolevCoefficientAmplitude ι q (4*Ri) C₁*Da+
    3*sobolevCoefficientAmplitude ι q (4*Ri) C₀*coordinateCost ι q Ri C₀ C₁ Df Da

end EulerSourceCylinderTimeBounds
