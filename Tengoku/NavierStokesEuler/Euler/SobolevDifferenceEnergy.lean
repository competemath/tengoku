import Tengoku.NavierStokesEuler.Euler.CorrectionDifference
import Tengoku.NavierStokesEuler.Euler.CorrectionStabilityConstants
import Tengoku.NavierStokesEuler.Euler.SquaredMetricStability

namespace EulerSobolevDifferenceEnergy
end EulerSobolevDifferenceEnergy
namespace MeasureTheory
end MeasureTheory
namespace Set
end Set
namespace InnerProductSpace
end InnerProductSpace
namespace EulerLiftedGradientSpace
end EulerLiftedGradientSpace
namespace EulerLiftedPressure
end EulerLiftedPressure
namespace EulerSpatialSobolevInverse
end EulerSpatialSobolevInverse
namespace EulerCylinderSobolevSpace
end EulerCylinderSobolevSpace
namespace EulerCorrectionOperators
end EulerCorrectionOperators
namespace EulerCorrectionDifference
end EulerCorrectionDifference
namespace EulerCorrectionStabilityConstants
end EulerCorrectionStabilityConstants
namespace EulerSobolevTransport
end EulerSobolevTransport
namespace EulerSobolevMetricTransport
end EulerSobolevMetricTransport
namespace EulerSobolevHeatGenerator
end EulerSobolevHeatGenerator
namespace EulerMetricHeatEnergy
end EulerMetricHeatEnergy
namespace EulerSobolevL2Product
end EulerSobolevL2Product
namespace EulerSquaredMetricStability
end EulerSquaredMetricStability
namespace Topology
end Topology

namespace NavierStokesEulerFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Actual pointwise squared metric energy for the difference of viscous corrections. -/

noncomputable section

namespace EulerSobolevDifferenceEnergy
open _root_.EulerSobolevDifferenceEnergy

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerSpatialSobolevInverse EulerCylinderSobolevSpace EulerCorrectionOperators EulerCorrectionDifference
  EulerCorrectionStabilityConstants EulerSobolevTransport
  EulerSobolevMetricTransport EulerSobolevHeatGenerator EulerMetricHeatEnergy EulerSobolevL2Product
  EulerSquaredMetricStability
open _root_.MeasureTheory _root_.Set _root_.InnerProductSpace _root_.EulerLiftedGradientSpace _root_.EulerLiftedPressure _root_.EulerSpatialSobolevInverse _root_.EulerCylinderSobolevSpace _root_.EulerCorrectionOperators _root_.EulerCorrectionDifference _root_.EulerCorrectionStabilityConstants _root_.EulerSobolevTransport _root_.EulerSobolevMetricTransport _root_.EulerSobolevHeatGenerator _root_.EulerMetricHeatEnergy _root_.EulerSobolevL2Product _root_.EulerSquaredMetricStability
open scoped Topology _root_.Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The existing Sobolev normed-group instance for the actual difference-energy calculation. -/
local instance energySobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
/-- The existing real Sobolev module instance for the actual difference-energy calculation. -/
local instance energySobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- Actual Hq transport has the uniform variable-metric pairing bound used for viscosity differences. -/
theorem difference_transport_bound {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T) (K : SmoothCoefficient period)
    (u v : SobolevSpace period (q+1)) (Kx Z R : ℝ)
    (hKx : (K.firstBound : ℝ) ≤ Kx) (hZ : ‖D.approximation t‖ ≤ Z) (hu : ‖u‖ ≤ R)
    (hsym : ∀ x a b, ⟪K.coefficient x a,b⟫_ℝ=⟪a,K.coefficient x b⟫_ℝ)
    (hz : value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction)
    (hud : value period u ∈ divergenceFreeSpace period D.κ D.direction) :
    |⟪K.operator (value period (u-v)),value period (transportBilinear period hq
      (velocityComponents D.κ D.direction) (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
      (D.approximation t+u) (u-v))⟫_ℝ| ≤ Kx*velocityBound period q Z R*‖value period (u-v)‖^2 := by
  have hz0 := (norm_nonneg (D.approximation t)).trans hZ
  have hr0 := (norm_nonneg u).trans hu
  have hV := velocityBound_nonneg period q Z R hz0 hr0
  let z := truncateOperator period q (D.approximation t+u)
  have hzB : ∀ᵐ x ∂liftMeasure period, ‖value period z x‖ ≤ (velocityBound period q Z R).toNNReal := by
    filter_upwards [value_ae_bound period (by omega : 3 ≤ q) z] with x hx
    rw [Real.coe_toNNReal _ hV]
    apply hx.trans
    unfold velocityBound
    apply mul_le_mul_of_nonneg_left _ (sobolevEmbeddingConstant_nonneg period q)
    exact (truncateOperator_bound period (D.approximation t+u)).trans ((norm_add_le _ _).trans (add_le_add hZ hu))
  have hzd : value period z ∈ divergenceFreeSpace period D.κ D.direction := by
    change value period (D.approximation t)+value period u ∈ _
    exact (divergenceFreeSpace period D.κ D.direction).add_mem hz hud
  have h := metric_transport_bound period (by omega : 3 ≤ q) D.κ D.direction K z
    (restrictOperator period (by omega : 1 ≤ q+1) (u-v)) hsym hzd (velocityBound period q Z R).toNNReal hzB
  rw [transportBilinear_eq_transportOperator period hq D.κ D.direction D.scale_bound D.direction_bound]
  apply h.trans
  rw [Real.coe_toNNReal _ hV]
  have hKx0 := K.firstBound.coe_nonneg.trans hKx
  have hd := add_le_add D.scale_bound D.direction_bound
  have hprod := mul_le_mul hKx hd (add_nonneg (abs_nonneg _) (norm_nonneg _)) hKx0
  have hβ : (1/2 : ℝ)*K.firstBound*((|D.κ|+‖D.direction‖)*velocityBound period q Z R) ≤
      Kx*velocityBound period q Z R := by
    have hh := mul_le_mul_of_nonneg_right hprod hV
    nlinarith
  exact mul_le_mul_of_nonneg_right hβ (sq_nonneg _)

/-- The actual Sobolev Laplacian has the fixed metric heat bound obtained by integration by parts. -/
theorem difference_heat_bound {q : ℕ} (hq : 2 ≤ q) (K : SmoothCoefficient period)
    (u : SobolevSpace period q) (c Kx : ℝ) (hc : 0 < c)
    (hKx : (K.firstBound : ℝ) ≤ Kx)
    (hpos : ∀ x a, c^2*‖a‖^2 ≤ ⟪K.coefficient x a,a⟫_ℝ) :
    ⟪K.operator (value period u),laplacianEvaluation period q hq u⟫_ℝ ≤
      (2*Kx^2/c^2)*‖value period u‖^2 := by
  rw [laplacianEvaluation_eq_jet]
  have h := metric_heat_bound period K (value period u)
    (EulerH6Pressure.SpatialJet.restrict (toJet period u) 2 hq) c hc hpos
  have hd : 0 ≤ ∑ i : Fin 4, ‖(EulerH6Pressure.SpatialJet.restrict (toJet period u) 2 hq).word (fun _ : Fin 1 => i)‖^2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hsq : (K.firstBound : ℝ)^2 ≤ Kx^2 := by nlinarith [K.firstBound.coe_nonneg]
  have hcoef := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2)) (sq_nonneg c)
  have hprod := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖value period u‖)
  nlinarith [sq_nonneg c]

end EulerSobolevDifferenceEnergy
