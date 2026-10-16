import Tengoku.NavierStokesEuler.Euler.SourceForwardCoefficient
import Tengoku.NavierStokesEuler.Euler.LpCylinderRectangularRegularity

/-!
# Actual source forcing and physical velocity on cylinder L²

The projected forcing uses the constructed Gram left inverse. The physical
velocity uses the actual frame. Both preserve the closed spatial support,
actual mixed-orbit smoothness, and the external-word radius at fixed Hq.
-/

noncomputable section

namespace EulerSourceCylinderForcing

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients
  EulerSourceForwardCoefficient EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerLpCylinderRectangular EulerGevrey EulerParameterWordGevrey
  EulerTimeLpGramGevrey EulerTransverseForwardCoefficientGevrey
open scoped BoundedContinuousFunction ContDiff

variable (period : ℝ) [Fact (0 < period)]
  {K U E ι : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]
  (S : Set Space) (hS : MeasurableSet S)
  (Q : SmoothCoefficientPath K (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q.field t x v‖^2)

/-- The actual projected forcing on the supported cylinder. -/
def projectedForcing (f : C(K,Supported period E S hS)) : C(K,Supported period U S hS) :=
  supportedMultiplierMap period S hS (sourceForcing Q c hc hQ) f

/-- The actual physical velocity associated with the coordinate field. -/
def physicalVelocity (u : C(K,Supported period U S hS)) : C(K,Supported period E S hS) :=
  supportedMultiplierMap period S hS Q.field u

theorem projectedForcing_contDiff (f : C(K,Supported period E S hS))
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS f))) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a
      (includePath period S hS (projectedForcing period S hS Q c hc hQ f))) :=
  supported_product_orbit_contDiff period (sourceForcing Q c hc hQ)
    (sourceForcing_translation_contDiff Q c hc hQ) S hS f hf

end EulerSourceCylinderForcing
