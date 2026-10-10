import Tengoku.NavierStokesEuler.Euler.SobolevSmoothing
import Tengoku.NavierStokesEuler.Euler.GaussianHeatTotal

/-! The actual Gaussian cylinder heat semigroup on the complete Sobolev scale. -/

noncomputable section

namespace EulerSobolevHeat

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevSmoothing EulerGaussianCylinderHeat
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The genuine cylinder heat semigroup lifted to the complete Sobolev space. -/
def heatOperator (q : ℕ) (v : ℝ≥0) : SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  liftOperator period q (cylinderHeat period v) (cylinderHeat_translation period v)

/-- Every Sobolev derivative coordinate evolves by the actual L² heat semigroup. -/
@[simp]
theorem heatOperator_apply {q : ℕ} (v : ℝ≥0) (u : SobolevSpace period q) (w : SobolevWord q) :
    (heatOperator period q v u).val w = cylinderHeat period v (u.val w) := rfl

/-- The heat semigroup is contractive in every complete Sobolev norm. -/
theorem heatOperator_bound {q : ℕ} (v : ℝ≥0) (u : SobolevSpace period q) :
    ‖heatOperator period q v u‖ ≤ ‖u‖ := by
  change ‖(heatOperator period q v u).val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
  intro w
  exact (cylinderHeat_norm_le period v _).trans (word_norm_le period u w)

/-- The underlying L² field evolves by exactly the original heat operator. -/
@[simp]
theorem heatOperator_value {q : ℕ} (v : ℝ≥0) (u : SobolevSpace period q) :
    value period (heatOperator period q v u) = cylinderHeat period v (value period u) := rfl

/-- Zero variance is the identity on the complete Sobolev space. -/
@[simp]
theorem heatOperator_zero {q : ℕ} (u : SobolevSpace period q) : heatOperator period q 0 u = u := by
  apply value_injective period
  simp only [heatOperator_value, cylinderHeat_zero]

/-- The actual Sobolev heat operators obey the semigroup law. -/
theorem heatOperator_semigroup {q : ℕ} (v w : ℝ≥0) (u : SobolevSpace period q) :
    heatOperator period q v (heatOperator period q w u) = heatOperator period q (v + w) u := by
  apply value_injective period
  simp only [heatOperator_value, cylinderHeat_semigroup]

/-- Strong heat continuity holds in every complete Sobolev norm, including at zero variance. -/
theorem heatOperator_continuous {q : ℕ} (u : SobolevSpace period q) :
    Continuous (fun v : ℝ≥0 => heatOperator period q v u) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro w
  exact cylinderHeat_continuous period (u.val w)

/-- The explicit parabolic derivative constant of the Gaussian heat operator. -/
def heatDerivativeConstant (v : ℝ≥0) : ℝ := gaussianAbsMoment 1 / Real.sqrt (v : ℝ)

/-- The Gaussian derivative constant is nonnegative. -/
theorem heatDerivativeConstant_nonneg (v : ℝ≥0) : 0 ≤ heatDerivativeConstant v :=
  div_nonneg (gaussianAbsMoment_nonneg 1) (Real.sqrt_nonneg _)

end EulerSobolevHeat
