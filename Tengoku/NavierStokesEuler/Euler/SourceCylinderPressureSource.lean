import Tengoku.NavierStokesEuler.Euler.SourceCylinderRegularity
import Tengoku.NavierStokesEuler.Euler.SourceNormalCoefficient

/-!
# The actual scalar pressure source on cylinder L²

The normal functional is constructed from the positive one-column Gram
matrix. Applying it to f−2MA gives a genuine scalar L² path, with the literal
normal residual as representative and genuine smooth mixed translation orbit.
-/

noncomputable section

namespace EulerSourceCylinderEquation

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderRectangular
  EulerSourceNormalCoefficient
open scoped ContDiff BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] Space))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q.field t x v‖^2)
  (f : C(Icc (0 : ℝ) T,Supported period Space S hS)) (a₀ : Supported period U S hS)
  (M : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (m : SmoothCoefficientPath (Icc (0 : ℝ) T) Space)
  (cm : ℝ) (hcm : 0 < cm) (hm : ∀ t x, cm ≤ ‖m.field t x‖^2)

/-- A genuine supported scalar path representing the right side of ∂θπ in (11). -/
def pressureSource : C(Icc (0 : ℝ) T,Supported period ℝ S hS) :=
  supportedMultiplierMap period S hS (normalFunctional m cm hcm hm)
    (f - (2 : ℝ) • supportedMultiplierMap period S hS M.field
      (velocity period S hS T hT Q Q₁ c hc hQ f a₀))

end EulerSourceCylinderEquation
