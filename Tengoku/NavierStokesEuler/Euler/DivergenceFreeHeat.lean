import Tengoku.NavierStokesEuler.Euler.SobolevHeatVolterra
import Tengoku.NavierStokesEuler.Euler.SobolevPressureResolvent

/-! The actual Gaussian heat and Volterra integrals preserve the lifted divergence constraint. -/

noncomputable section

namespace EulerDivergenceFreeHeat

open MeasureTheory ProbabilityTheory EulerLiftedGradientSpace EulerGaussianCylinderHeat
  EulerCylinderSobolevSpace EulerSobolevHeat EulerVolterraConvolution EulerSobolevCoefficientPressure
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The actual lifted gradient projection commutes with each Gaussian directional heat average. -/
theorem gradientProjection_lineHeat (κ : ℝ) (m : Vector3) (a : LiftTangent) (v : ℝ≥0) (f : LiftL2 period) :
    gradientProjection period κ m (lineHeat period a v f) =
      lineHeat period a v (gradientProjection period κ m f) := by
  unfold lineHeat
  rw [← (gradientProjection period κ m).integral_comp_comm (lineOrbit_integrable period a f _)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r =>
    (gradientProjection_translation period κ m (EulerPressureSpatialRegularity.translationPath period a r) f).symm

/-- The lifted gradient projection commutes with every finite product of Gaussian heat averages. -/
theorem gradientProjection_heatList (κ : ℝ) (m : Vector3) (directions : List LiftTangent)
    (v : ℝ≥0) (f : LiftL2 period) :
    gradientProjection period κ m (heatList period directions v f) =
      heatList period directions v (gradientProjection period κ m f) := by
  induction directions with
  | nil => rfl
  | cons a tail ih => rw [heatList, heatList, gradientProjection_lineHeat, ih]

/-- The actual cylinder heat semigroup preserves the lifted gradient projection exactly. -/
theorem gradientProjection_cylinderHeat (κ : ℝ) (m : Vector3) (v : ℝ≥0) (f : LiftL2 period) :
    gradientProjection period κ m (cylinderHeat period v f) =
      cylinderHeat period v (gradientProjection period κ m f) :=
  gradientProjection_heatList period κ m cylinderDirections v f

/-- The continuous constraint map on an actual complete Sobolev space. -/
def gradientEvaluation (q : ℕ) (κ : ℝ) (m : Vector3) : SobolevSpace period q →L[ℝ] LiftL2 period :=
  (gradientProjection period κ m).comp (valueOperator period q)

/-- The Sobolev constraint is exactly the underlying lifted L² gradient projection. -/
@[simp]
theorem gradientEvaluation_apply {q : ℕ} (κ : ℝ) (m : Vector3) (u : SobolevSpace period q) :
    gradientEvaluation period q κ m u = gradientProjection period κ m (value period u) := rfl

/-- Vanishing of the continuous constraint map is exactly membership in the genuine divergence-free subspace. -/
theorem gradientEvaluation_zero_iff {q : ℕ} (κ : ℝ) (m : Vector3) (u : SobolevSpace period q) :
    gradientEvaluation period q κ m u = 0 ↔ value period u ∈ divergenceFreeSpace period κ m := by
  constructor
  · intro h
    apply (gradientSpace period κ m).orthogonalProjectionOnto_eq_zero_iff.mp
    apply Subtype.ext
    exact h
  · intro h
    have hz := (gradientSpace period κ m).orthogonalProjectionOnto_eq_zero_iff.mpr h
    exact congrArg Subtype.val hz

/-- The Sobolev heat flow evolves the divergence constraint by the same genuine L² heat semigroup. -/
theorem gradientEvaluation_heat {q : ℕ} (κ : ℝ) (m : Vector3) (v : ℝ≥0) (u : SobolevSpace period q) :
    gradientEvaluation period q κ m (heatOperator period q v u) =
      cylinderHeat period v (gradientEvaluation period q κ m u) := by
  rw [gradientEvaluation_apply, heatOperator_value, gradientProjection_cylinderHeat, gradientEvaluation_apply]

end EulerDivergenceFreeHeat
