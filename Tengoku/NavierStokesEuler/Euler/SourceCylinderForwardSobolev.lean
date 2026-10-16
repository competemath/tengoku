import Tengoku.NavierStokesEuler.Euler.SourceCylinderForward
import Tengoku.NavierStokesEuler.Euler.SourceCylinderForcing

/-!
# The complete physical forward bound at one mixed-word radius

Physical forcing is projected by the actual Gram left inverse, the supported
coordinate equation is solved by the constructed evolution, and the result
is multiplied by the physical frame. All three operations use the same
external radius R. Only the solve spends one shift.
-/

noncomputable section

namespace EulerSourceCylinderForwardSobolev

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderCoefficients
  EulerSourceCylinderForward EulerSourceCylinderForcing EulerSourceForwardCoefficient
  EulerGevrey EulerParameterWordGevrey EulerLinearDuhamel EulerLinearFundamentalExistence
  EulerTimeLpGramGevrey
open scoped ContDiff BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]
  {U E ι : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]
  (T : ℝ) (hT : 0 ≤ T) (S : Set Space) (hS : MeasurableSet S)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q.field t x v‖^2)
  (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)
  (f : C(Icc (0 : ℝ) T,Supported period E S hS)) (a₀ : Supported period U S hS)

private local instance : NormedRing (U →L[ℝ] U) := inferInstance
private local instance : NormedRing (Space →ᵇ U →L[ℝ] U) := inferInstance

/-- Actual profile-normalized coordinates with physical forcing as input. -/
def normalizedCoordinates : C(Icc (0 : ℝ) T,Supported period U S hS) :=
  (evolution period T hT Q Q₁ c hc hQ S hS).weightedSolution g hg
    (projectedForcing period S hS Q c hc hQ f) a₀

/-- The corresponding actual profile-normalized physical velocity. -/
def normalizedVelocity : C(Icc (0 : ℝ) T,Supported period E S hS) :=
  physicalVelocity period S hS Q (normalizedCoordinates period T hT S hS Q Q₁ c hc hQ g hg f a₀)

/-- Explicit coefficient cost of projecting a physical forcing at the fixed base order. -/
def forcingCost (ι : Type*) [Fintype ι] (q : ℕ) (Ri C₀ : ℝ) : ℝ :=
  3*sobolevCoefficientAmplitude ι q (4*Ri) (3*Ri*C₀)

end EulerSourceCylinderForwardSobolev
