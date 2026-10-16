import Tengoku.NavierStokesEuler.Euler.LpCylinderRectangular
import Tengoku

/-! Actual angular averaging on the cylinder, including its supported spaces. -/

noncomputable section

namespace EulerCylinderAngleAverage

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderRectangular
  EulerLpSupportedSubspace EulerMeanCoefficients
open scoped BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]

section Average

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def angleCurve (u : CylinderL2 P V) (s : ℝ) : CylinderL2 P V :=
  translate P (0,s) u

omit [CompleteSpace V] in
theorem angleCurve_continuous (u : CylinderL2 P V) : Continuous (angleCurve P u) :=
  (translate_continuous P u).comp (continuous_const.prodMk continuous_id)

def averageIntegral (u : CylinderL2 P V) : CylinderL2 P V :=
  P⁻¹ • (∫ s in (0 : ℝ)..P, angleCurve P u s)

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

end Average

section Intertwining

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

end Intertwining

section Coefficients

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

end Coefficients

section Supported

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (S : Set Space) (hS : MeasurableSet S)

end Supported

end EulerCylinderAngleAverage
