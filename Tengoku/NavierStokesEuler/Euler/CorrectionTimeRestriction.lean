import Tengoku.NavierStokesEuler.Euler.EulerCorrectionLocal

namespace EulerCorrectionOperators
end EulerCorrectionOperators
namespace Set
end Set
namespace EulerCylinderSobolevSpace
end EulerCylinderSobolevSpace
namespace EulerSpatialSobolevInverse
end EulerSpatialSobolevInverse
namespace EulerSobolevCoefficientPressure
end EulerSobolevCoefficientPressure
namespace EulerQuadraticSource
end EulerQuadraticSource
namespace Topology
end Topology

namespace NavierStokesEulerFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Actual correction coefficient data restricted along continuous time maps. -/

noncomputable section

namespace EulerCorrectionOperators
open _root_.EulerCorrectionOperators

open Set EulerCylinderSobolevSpace EulerSpatialSobolevInverse EulerSobolevCoefficientPressure
  EulerQuadraticSource
open _root_.Set _root_.EulerCylinderSobolevSpace _root_.EulerSpatialSobolevInverse _root_.EulerSobolevCoefficientPressure
open _root_.EulerQuadraticSource hiding Coefficients Coefficients.apply Coefficients.apply_bound Coefficients.apply_sub_bound Coefficients.ballBound Coefficients.ballBound_nonneg Coefficients.ballLipschitz Coefficients.ballLipschitz_nonneg Coefficients.casesOn Coefficients.comp Coefficients.comp_apply Coefficients.continuous Coefficients.ctorIdx Coefficients.forcing Coefficients.linear Coefficients.mk Coefficients.mk.inj Coefficients.mk.injEq Coefficients.mk.noConfusion Coefficients.mk.sizeOf_spec Coefficients.noConfusion Coefficients.noConfusionType Coefficients.projection Coefficients.quadratic Coefficients.rec Coefficients.recOn nestedGroup
open scoped Topology _root_.Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Restrict the actual spatial coefficient and its jet along a continuous parameter map. -/
def CoefficientPath.comp {q : ℕ} {T U : Type*} [TopologicalSpace T] [TopologicalSpace U]
    (A : CoefficientPath period q T) (f : C(U,T)) : CoefficientPath period q U where
  coefficient t := A.coefficient (f t)
  jet t := A.jet (f t)
  continuous := A.continuous.comp f.continuous

/-- Restrict every actual coefficient, background field, and residual along the same time map. -/
def CorrectionData.comp {q : ℕ} {T U : Type*} [TopologicalSpace T] [TopologicalSpace U]
    (D : CorrectionData period q T) (f : C(U,T)) : CorrectionData period q U where
  κ := D.κ
  direction := D.direction
  scale_bound := D.scale_bound
  direction_bound := D.direction_bound
  metric := D.metric.comp period f
  coercivity := D.coercivity
  coercivity_pos := D.coercivity_pos
  metric_pos t := D.metric_pos (f t)
  linear := D.linear.comp period f
  quadratic i := (D.quadratic i).comp period f
  approximation := D.approximation.comp f
  residual := D.residual.comp f

/-- The restricted correction source is the original actual source at the restricted time. -/
theorem CorrectionData.comp_source {q : ℕ} {T U : Type*} [TopologicalSpace T] [TopologicalSpace U]
    (D : CorrectionData period q T) (f : C(U,T)) (hq : 6 ≤ q)
    (t : U) (u : SobolevSpace period (q+1)) :
    ((D.comp period f).coefficients period hq).apply t u =
      (D.coefficients period hq).apply (f t) u := rfl

/-- Restricting the concrete data gives precisely the same nonlinear mild equation on a shorter interval. -/
theorem CorrectionData.comp_quadraticDuhamel {q : ℕ} (hq : 6 ≤ q)
    (ν : ℝ) (hν : 0 < ν) {T S : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (D : CorrectionData period q (Icc (0 : ℝ) S))
    (u₀ : SobolevSpace period (q+1)) (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (t : Icc (0 : ℝ) T) :
    quadraticDuhamel period ν hν hT le_rfl
        ((D.comp period (timeInclusion hTS)).coefficients period hq) u₀ u t =
      quadraticDuhamel period ν hν hT hTS (D.coefficients period hq) u₀ u t := rfl

end EulerCorrectionOperators
