import Tengoku.NavierStokesEuler.Euler.SourceForwardCoefficient
import Tengoku.NavierStokesEuler.Euler.LpCylinderRegularSobolev

/-!
# The source Gram generator on the genuine cylinder L²

The generator below is constructed from the actual frame and its first
time-derivative field by bounded-field Gram inversion. Its translated
coefficient bounds are derived from the frame jets. The forward solution
has the localized H3 bound and the true fixed-Hq mixed external-word
estimate at the same input/output radius.
-/

noncomputable section

namespace EulerSourceCylinderForward

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderCoefficients
  EulerLinearDuhamel EulerLinearFundamentalExistence EulerMeanCoefficients
  EulerSourceForwardCoefficient EulerGevrey EulerParameterWordGevrey
  EulerTransverseForwardCoefficientGevrey EulerTimeLpGramGevrey
open scoped BoundedContinuousFunction ContDiff

variable (period : ℝ) [Fact (0 < period)]
  {U E ι : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]
  (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q.field t x v‖^2)

private local instance : NormedRing (U →L[ℝ] U) := inferInstance
private local instance : NormedRing (Space →ᵇ U →L[ℝ] U) := inferInstance

/-- Actual homogeneous evolution from the source Gram generator. -/
def evolution (S : Set Space) (hS : MeasurableSet S) :=
  constructedEvolution period S hS T hT (sourceGenerator Q Q₁ c hc hQ)

end EulerSourceCylinderForward
