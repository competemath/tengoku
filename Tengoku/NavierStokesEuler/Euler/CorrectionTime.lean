import Tengoku.NavierStokesEuler.Euler.CorrectionOperators
import Tengoku.NavierStokesEuler.Euler.SobolevPressureTime
import Tengoku.NavierStokesEuler.Euler.QuadraticHeatLocal

/-! Tengoku repair: `instance at line 60` ran out of heartbeats in the tree; `synthInstance.maxHeartbeats` is 160000 for it (was 20000). -/

namespace EulerCorrectionOperators
end EulerCorrectionOperators
namespace MeasureTheory
end MeasureTheory
namespace InnerProductSpace
end InnerProductSpace
namespace Set
end Set
namespace EulerLiftedGradientSpace
end EulerLiftedGradientSpace
namespace EulerPressureSpatialRegularity
end EulerPressureSpatialRegularity
namespace EulerSpatialSobolevInverse
end EulerSpatialSobolevInverse
namespace EulerCylinderSobolev
end EulerCylinderSobolev
namespace EulerCylinderSobolevSpace
end EulerCylinderSobolevSpace
namespace EulerSobolevCoefficientPressure
end EulerSobolevCoefficientPressure
namespace EulerQuadraticSource
end EulerQuadraticSource
namespace Topology
end Topology

namespace NavierStokesEulerFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The actual time-dependent coefficients and nonlinear source of the lifted Euler correction. -/

noncomputable section

namespace EulerCorrectionOperators
open _root_.EulerCorrectionOperators

open MeasureTheory InnerProductSpace Set EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerCylinderSobolevSpace
  EulerSobolevCoefficientPressure EulerQuadraticSource
open _root_.MeasureTheory _root_.InnerProductSpace _root_.Set _root_.EulerLiftedGradientSpace _root_.EulerPressureSpatialRegularity _root_.EulerSpatialSobolevInverse _root_.EulerCylinderSobolev _root_.EulerCylinderSobolevSpace _root_.EulerSobolevCoefficientPressure
open _root_.EulerQuadraticSource hiding Coefficients Coefficients.apply Coefficients.apply_bound Coefficients.apply_sub_bound Coefficients.ballBound Coefficients.ballBound_nonneg Coefficients.ballLipschitz Coefficients.ballLipschitz_nonneg Coefficients.casesOn Coefficients.comp Coefficients.comp_apply Coefficients.continuous Coefficients.ctorIdx Coefficients.forcing Coefficients.linear Coefficients.mk Coefficients.mk.inj Coefficients.mk.injEq Coefficients.mk.noConfusion Coefficients.mk.sizeOf_spec Coefficients.noConfusion Coefficients.noConfusionType Coefficients.projection Coefficients.quadratic Coefficients.rec Coefficients.recOn nestedGroup
open scoped Topology _root_.Topology

variable {X Y T : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [TopologicalSpace T]

/-- Continuous coefficient multipliers act continuously on any fixed genuine bilinear product. -/
theorem postcompose_continuous (A : T → Y →L[ℝ] Y) (hA : Continuous A)
    (B : X →L[ℝ] X →L[ℝ] Y) : Continuous (fun t => postcompose (A t) B) :=
  ((ContinuousLinearMap.compL ℝ X Y Y).continuous.comp hA).clm_comp_const B

variable (period : ℝ) [Fact (0 < period)]

local instance timeSobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
local instance timeSobolevRealSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance
set_option synthInstance.maxHeartbeats 160000 in
local instance timeSobolevBilinearGroup (q : ℕ) : SeminormedAddCommGroup
    (SobolevSpace period (q+1) →L[ℝ] SobolevSpace period (q+1) →L[ℝ] SobolevSpace period q) := inferInstance

/-- Time continuity of the actual order-zero quadratic terms. -/
theorem algebraicBilinear_continuous {q : ℕ} (hq : 6 ≤ q)
    (C : T → Fin 3 → SobolevSpace period q →L[ℝ] SobolevSpace period q)
    (hC : ∀ i, Continuous (fun t => C t i)) : Continuous (fun t => algebraicBilinear period hq (C t)) := by
  apply continuous_finsetSum
  intro i _
  exact postcompose_continuous (fun t => C t i) (hC i) (coordinateProduct period hq i)

/-- Time continuity of the literal transport-plus-algebraic Euler nonlinearity. -/
theorem eulerBilinear_continuous {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C : T → Fin 3 → SobolevSpace period q →L[ℝ] SobolevSpace period q)
    (hC : ∀ i, Continuous (fun t => C t i)) : Continuous (fun t => eulerBilinear period hq L hL (C t)) := by
  have ht : Continuous (fun _ : T => EulerSobolevTransport.transportBilinear period hq L hL) := continuous_const
  exact ht.add (algebraicBilinear_continuous period hq C hC)

/-- The actual Sobolev pressure projection as a continuous coefficient path. -/
def pressureProjectionPath {q : ℕ}
    (G : T → SmoothCoefficient period) (K : ∀ t, CoefficientJet period standardDirection q (G t))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ t x v, c*‖v‖^2 ≤ ⟪(G t).coefficient x v, v⟫_ℝ)
    (hG : Continuous (fun t => coefficientSobolevOperator period (K t))) :
    C(T, SobolevSpace period q →L[ℝ] SobolevSpace period q) where
  toFun t := projectedSourceOperator period (K t) κ m c hc (hpos t)
  continuous_toFun := continuous_iff_continuousAt.mpr fun t =>
    projectedSource_continuousAt period G K κ m c hc hpos t hG.continuousAt

/-- Concrete coefficient data for equation (17): actual pressure, actual transport, and actual order-zero coefficient multipliers. -/
def correctionCoefficients {q : ℕ} (hq : 6 ≤ q)
    (G : T → SmoothCoefficient period) (K : ∀ t, CoefficientJet period standardDirection q (G t))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ t x v, c*‖v‖^2 ≤ ⟪(G t).coefficient x v, v⟫_ℝ)
    (hG : Continuous (fun t => coefficientSobolevOperator period (K t)))
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C₀ : C(T, SobolevSpace period q →L[ℝ] SobolevSpace period q))
    (C : Fin 3 → C(T, SobolevSpace period q →L[ℝ] SobolevSpace period q))
    (z : C(T, SobolevSpace period (q+1))) (r : C(T, SobolevSpace period q)) :
    Coefficients T (SobolevSpace period (q+1)) (SobolevSpace period q) where
  projection := pressureProjectionPath period G K κ m c hc hpos hG
  forcing := r
  linear := ⟨fun t => linearize (eulerBilinear period hq L hL (fun i => C i t))
      ((C₀ t).comp (truncateOperator period q)) (z t),
    linearize_continuous _ _ _ (eulerBilinear_continuous period hq L hL _ (fun i => (C i).continuous))
      (C₀.continuous.clm_comp_const (truncateOperator period q)) z.continuous⟩
  quadratic := ⟨fun t => eulerBilinear period hq L hL (fun i => C i t),
    eulerBilinear_continuous period hq L hL _ (fun i => (C i).continuous)⟩

/-- The correction is exactly pressure applied to the residual and the nonlinear increment about z. -/
theorem correction_source_identity {q : ℕ} (hq : 6 ≤ q)
    (G : T → SmoothCoefficient period) (K : ∀ t, CoefficientJet period standardDirection q (G t))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ t x v, c*‖v‖^2 ≤ ⟪(G t).coefficient x v, v⟫_ℝ)
    (hG : Continuous (fun t => coefficientSobolevOperator period (K t)))
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C₀ : C(T, SobolevSpace period q →L[ℝ] SobolevSpace period q))
    (C : Fin 3 → C(T, SobolevSpace period q →L[ℝ] SobolevSpace period q))
    (z : C(T, SobolevSpace period (q+1))) (r : C(T, SobolevSpace period q))
    (t : T) (e : SobolevSpace period (q+1)) :
    (correctionCoefficients period hq G K κ m c hc hpos hG L hL C₀ C z r).apply t e =
      -(projectedSourceOperator period (K t) κ m c hc (hpos t)
        (r t + C₀ t (truncateOperator period q e) +
          eulerBilinear period hq L hL (fun i => C i t) (z t+e) (z t+e) -
          eulerBilinear period hq L hL (fun i => C i t) (z t) (z t))) := by
  change -(projectedSourceOperator period (K t) κ m c hc (hpos t)
    (r t + linearize (eulerBilinear period hq L hL (fun i => C i t))
      ((C₀ t).comp (truncateOperator period q)) (z t) e +
      eulerBilinear period hq L hL (fun i => C i t) e e)) = _
  congr 2
  simp only [linearize_apply, map_add, add_apply, ContinuousLinearMap.comp_apply]
  abel

/-- The actual nonlinear correction source is divergence-free for every input. -/
theorem correction_source_gradient_zero {q : ℕ} (hq : 6 ≤ q)
    (G : T → SmoothCoefficient period) (K : ∀ t, CoefficientJet period standardDirection q (G t))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ t x v, c*‖v‖^2 ≤ ⟪(G t).coefficient x v, v⟫_ℝ)
    (hG : Continuous (fun t => coefficientSobolevOperator period (K t)))
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C₀ : C(T, SobolevSpace period q →L[ℝ] SobolevSpace period q))
    (C : Fin 3 → C(T, SobolevSpace period q →L[ℝ] SobolevSpace period q))
    (z : C(T, SobolevSpace period (q+1))) (r : C(T, SobolevSpace period q))
    (t : T) (e : SobolevSpace period (q+1)) :
    gradientProjection period κ m (value period
      ((correctionCoefficients period hq G K κ m c hc hpos hG L hL C₀ C z r).apply t e)) = 0 := by
  rw [correction_source_identity]
  change gradientProjection period κ m (-value period (projectedSourceOperator period (K t) κ m c hc (hpos t) _)) = 0
  rw [map_neg, projectedSource_gradient_zero, neg_zero]

end EulerCorrectionOperators
