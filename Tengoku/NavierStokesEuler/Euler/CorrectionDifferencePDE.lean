import Tengoku.NavierStokesEuler.Euler.CorrectionDifference
import Tengoku.NavierStokesEuler.Euler.CorrectionMildEquation

/-! Tengoku repair: `differenceRhs_eq_sub` ran out of heartbeats in the tree; `synthInstance.maxHeartbeats` is 160000 for it (was 20000). -/

namespace EulerCorrectionDifferencePDE
end EulerCorrectionDifferencePDE
namespace MeasureTheory
end MeasureTheory
namespace Set
end Set
namespace EulerLiftedGradientSpace
end EulerLiftedGradientSpace
namespace EulerCylinderSobolevSpace
end EulerCylinderSobolevSpace
namespace EulerCorrectionOperators
end EulerCorrectionOperators
namespace EulerQuadraticSource
end EulerQuadraticSource
namespace EulerCorrectionContinuation
end EulerCorrectionContinuation
namespace EulerCorrectionDifference
end EulerCorrectionDifference
namespace EulerSobolevTransport
end EulerSobolevTransport
namespace EulerSobolevMetricTransport
end EulerSobolevMetricTransport
namespace EulerSobolevHeatGenerator
end EulerSobolevHeatGenerator
namespace EulerVolterraConvolution
end EulerVolterraConvolution
namespace Topology
end Topology

namespace NavierStokesEulerFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The exact viscosity-difference equation of two genuine nonlinear mild corrections. -/

noncomputable section

namespace EulerCorrectionDifferencePDE
open _root_.EulerCorrectionDifferencePDE

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCorrectionOperators
  EulerQuadraticSource EulerCorrectionContinuation EulerCorrectionDifference EulerSobolevTransport
  EulerSobolevMetricTransport EulerSobolevHeatGenerator EulerVolterraConvolution
open _root_.MeasureTheory _root_.Set _root_.EulerLiftedGradientSpace _root_.EulerCylinderSobolevSpace _root_.EulerCorrectionOperators _root_.EulerCorrectionContinuation _root_.EulerCorrectionDifference _root_.EulerSobolevTransport _root_.EulerSobolevMetricTransport _root_.EulerSobolevHeatGenerator _root_.EulerVolterraConvolution
open _root_.EulerQuadraticSource hiding Coefficients Coefficients.apply Coefficients.apply_bound Coefficients.apply_sub_bound Coefficients.ballBound Coefficients.ballBound_nonneg Coefficients.ballLipschitz Coefficients.ballLipschitz_nonneg Coefficients.casesOn Coefficients.comp Coefficients.comp_apply Coefficients.continuous Coefficients.ctorIdx Coefficients.forcing Coefficients.linear Coefficients.mk Coefficients.mk.inj Coefficients.mk.injEq Coefficients.mk.noConfusion Coefficients.mk.sizeOf_spec Coefficients.noConfusion Coefficients.noConfusionType Coefficients.projection Coefficients.quadratic Coefficients.rec Coefficients.recOn nestedGroup
open scoped Topology _root_.Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The existing Sobolev normed-group instance, fixed explicitly for difference-equation elaboration. -/
local instance differenceSobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
/-- The existing real Sobolev module instance, fixed explicitly for difference-equation elaboration. -/
local instance differenceSobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The literal right side of the viscosity-difference equation, including its genuine pressure difference. -/
def differenceRhs {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (ν μ : ℝ) (t : T)
    (u v : SobolevSpace period (q+1)) : LiftL2 period :=
  ν • laplacianEvaluation period (q+1) (by omega) (u-v)+
    (ν-μ) • laplacianEvaluation period (q+1) (by omega) v-
    value period (transportBilinear period hq (velocityComponents D.κ D.direction)
      (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound) (D.approximation t+u) (u-v))-
    value period (differenceRemainder period D hq t u v)-
    (D.metric.coefficient t).operator (value period (D.pressure period hq t u)-value period (D.pressure period hq t v))

/-- Exact vector subtraction for a bilinear evolution with two viscosities. -/
theorem vector_difference_identity {H : Type*} [AddCommGroup H] [Module ℝ H]
    (ν μ : ℝ) (a b ru rv top rem pu pv : H) (hraw : ru-rv=top+rem) :
    ν • (a-b)+(ν-μ) • b-top-rem-(pu-pv) =
      (ν • a-ru-pu)-(μ • b-rv-pv) := by
  have hr : ru=rv+(top+rem) := (sub_eq_iff_eq_add.mp hraw).trans (add_comm _ _)
  rw [hr,smul_sub,sub_smul]
  abel

set_option synthInstance.maxHeartbeats 160000 in
/-- The exposed difference equation is exactly the subtraction of the two actual PDE right sides. -/
theorem differenceRhs_eq_sub {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (ν μ : ℝ) (t : T)
    (u v : SobolevSpace period (q+1)) :
    differenceRhs period D hq ν μ t u v =
      (ν • laplacianEvaluation period (q+1) (by omega) u-value period (D.rawSource period hq t u)-
        (D.metric.coefficient t).operator (value period (D.pressure period hq t u)))-
      (μ • laplacianEvaluation period (q+1) (by omega) v-value period (D.rawSource period hq t v)-
        (D.metric.coefficient t).operator (value period (D.pressure period hq t v))) := by
  have hraw := congrArg (valueOperator period q) (rawSource_sub period D hq t u v)
  change value period (D.rawSource period hq t u)-value period (D.rawSource period hq t v) =
    value period (transportBilinear period hq (velocityComponents D.κ D.direction)
      (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
      (D.approximation t+u) (u-v))+value period (differenceRemainder period D hq t u v) at hraw
  have hlap := (laplacianEvaluation period (q+1) (by omega)).map_sub u v
  have hp := (D.metric.coefficient t).operator.map_sub
    (value period (D.pressure period hq t u)) (value period (D.pressure period hq t v))
  unfold differenceRhs
  rw [hlap,hp]
  exact vector_difference_identity ν μ _ _ _ _ _ _ _ _ hraw

/-- Subtracting two actual mild correction equations gives the literal transport-pressure-heat difference equation. -/
theorem correction_difference_hasDerivAt {q : ℕ} (hq : 6 ≤ q) (ν μ : ℝ) (hν : 0 < ν) (hμ : 0 < μ)
    (T : ℝ) (hT : 0 ≤ T) (D : CorrectionData period q (Icc (0 : ℝ) T))
    (u v : C(Icc (0 : ℝ) T,SobolevSpace period (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel period ν hν hT le_rfl (D.coefficients period hq) 0 u t)
    (hv : ∀ t, v t = quadraticDuhamel period μ hμ hT le_rfl (D.coefficients period hq) 0 v t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => value period (extendPath T hT u s)-value period (extendPath T hT v s))
      (differenceRhs period D hq ν μ ⟨t,ht.1.le,ht.2.le⟩ (u ⟨t,ht.1.le,ht.2.le⟩) (v ⟨t,ht.1.le,ht.2.le⟩)) t := by
  have hu' := correction_mild_hasDerivAt period hq ν hν hT le_rfl D u hu t ht
  have hv' := correction_mild_hasDerivAt period hq μ hμ hT le_rfl D v hv t ht
  apply (hu'.sub hv').congr_deriv
  exact (differenceRhs_eq_sub period D hq ν μ ⟨t,ht.1.le,ht.2.le⟩ _ _).symm

end EulerCorrectionDifferencePDE
