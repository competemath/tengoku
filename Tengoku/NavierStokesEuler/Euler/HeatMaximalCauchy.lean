import Tengoku.NavierStokesEuler.Euler.HeatMaximalEstimate
import Tengoku.NavierStokesEuler.Euler.QuadraticCauchy

/-! Strong L²-time H² Cauchy convergence from genuine heat energy, avoiding weak compactness. -/

noncomputable section

namespace EulerHeatMaximalCauchy

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevLaplacian
  EulerHeatMaximalEstimate EulerTimeLp EulerVolterraConvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A bounded linear observation preserves the difference form of the forced heat right hand side. -/
theorem linear_heat_rhs_sub {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (L : Y →L[ℝ] Z) (A : X →L[ℝ] Y) (ν : ℝ) (u v : X) (f g : Y) :
    L (ν • A (u-v)+(f-g)) = L (ν • A u+f)-L (ν • A v+g) := by
  rw [map_sub A, smul_sub, sub_add_sub_comm, map_sub L]

/-- Restrict a regularized path to its actual H¹ topology. -/
def lowerPath (T : ℝ) (u : C(Icc (0 : ℝ) T, SobolevSpace period 3)) :
    C(Icc (0 : ℝ) T, SobolevSpace period 1) :=
  (restrictOperator period (by norm_num : 1 ≤ 3)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u

/-- Embed the actual undifferentiated forcing into L² time. -/
def sourceTime (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, SobolevSpace period 1)) :
    TimeLp T (LiftL2 period) :=
  pathLp T hT ((valueOperator period 1).compLeftContinuous ℝ (Icc (0 : ℝ) T) f)

/-- The lower path restriction preserves differences. -/
theorem lowerPath_sub (T : ℝ) (u v : C(Icc (0 : ℝ) T, SobolevSpace period 3)) :
    lowerPath period T (u-v) = lowerPath period T u-lowerPath period T v :=
  map_sub ((restrictOperator period (by norm_num : 1 ≤ 3)).compLeftContinuous ℝ (Icc (0 : ℝ) T)) u v

/-- The actual source time embedding preserves differences. -/
theorem sourceTime_sub (T : ℝ) (hT : 0 ≤ T) (f g : C(Icc (0 : ℝ) T, SobolevSpace period 1)) :
    sourceTime period T hT (f-g) = sourceTime period T hT f-sourceTime period T hT g := by
  let A := (valueOperator period 1).compLeftContinuous ℝ (Icc (0 : ℝ) T)
  exact (congrArg (pathLp T hT) (map_sub A f g)).trans (pathLp_sub T hT (A f) (A g))

end EulerHeatMaximalCauchy
