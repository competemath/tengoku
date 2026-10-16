import Tengoku.NavierStokesEuler.Euler.SourceCylinderEquation
import Tengoku.NavierStokesEuler.Euler.SourceCylinderForwardSobolev
import Tengoku.NavierStokesEuler.Euler.LpCylinderTimeWeight

/-!
# The profile estimate belongs to the actual unnormalized PDE solution

The weighted construction is exactly division of the genuine solution with
physical forcing g f by g. This is an algebraic identity of continuous paths;
it does not differentiate g or introduce its extrema into any estimate.
-/

noncomputable section

namespace EulerSourceCylinderEquation

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderRectangular
  EulerSourceForwardCoefficient EulerSourceCylinderForcing EulerSourceCylinderForward
  EulerSourceCylinderForwardSobolev EulerContinuousTimeWeight EulerLinearDuhamel
open scoped BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]
  {U E : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q.field t x v‖^2)
  (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)
  (f : C(Icc (0 : ℝ) T,Supported period E S hS)) (a₀ : Supported period U S hS)

end EulerSourceCylinderEquation
