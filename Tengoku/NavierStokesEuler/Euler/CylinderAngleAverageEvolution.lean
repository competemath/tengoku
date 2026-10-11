import Tengoku.NavierStokesEuler.Euler.CylinderAngleAverage
import Tengoku.NavierStokesEuler.Euler.LpCylinderCoefficientTime
import Tengoku.NavierStokesEuler.Euler.LinearDuhamelNaturality
import Tengoku.NavierStokesEuler.Euler.LinearDuhamelOperator

/-! The actual supported Duhamel solution preserves zero angular mean. -/

noncomputable section

namespace EulerCylinderAngleAverage

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderRectangular
  EulerLpCylinderCoefficients EulerLinearDuhamel
open scoped BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]

section Coefficients

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  (S : Set Space) (hS : MeasurableSet S)

end Coefficients

section Paths

variable {K V : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (S : Set Space) (hS : MeasurableSet S)

private local instance : NormedAddCommGroup (Supported P V S hS) := inferInstance
private local instance : NormedSpace ℝ (Supported P V S hS) := inferInstance
private local instance : NormedAddCommGroup C(K,Supported P V S hS) := inferInstance
private local instance : NormedSpace ℝ C(K,Supported P V S hS) := inferInstance
private local instance : NormedAddCommGroup (C(K,Supported P V S hS) →L[ℝ] C(K,Supported P V S hS)) := inferInstance
private local instance : NormedSpace ℝ (C(K,Supported P V S hS) →L[ℝ] C(K,Supported P V S hS)) := inferInstance

end Paths

section Evolution

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ) (hT : 0 ≤ T)
  (B : C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V))
  (U : Evolution T hT (liftedOperatorPath P S hS T B))

end Evolution
end EulerCylinderAngleAverage
