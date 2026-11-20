import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.RescaledProduct
import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.ConvolutionMonotonicity
import Tengoku.Seed.MeasureTheory.Measure.Haar.NormedSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Dilation of the heat flow and cancellation of the geometric Jacobian -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeometricBrascampLieb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem gaussian_exponent_scale {a : ℝ} (ha : 0 < a) (x z : E) :
    -(4*a^2)⁻¹*‖a • x-z‖^2 = -(1/4 : ℝ)*‖x-a⁻¹ • z‖^2 := by
  have he : a • x-z = a • (x-a⁻¹ • z) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp

theorem gaussianConvolution_scale (f : E → ℝ) {a : ℝ} (ha : 0 < a) (x : E) :
    gaussianConvolution (4*a^2)⁻¹ f (a • x) = rescaledConvolution f a⁻¹ x := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change f z*Real.exp (-(4*a^2)⁻¹*‖a • x-z‖^2) = _
    rw [gaussian_exponent_scale ha]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem heatNormalization_scale {a : ℝ} (ha : 0 < a) :
    heatNormalization (E := E) (a^2) =
      Real.exp (-(Module.finrank ℝ E : ℝ)*Real.log a)*heatNormalization (E := E) 1 := by
  rw [heatNormalization, heatNormalization, mul_one,
    Real.log_mul (by positivity : 4*Real.pi ≠ 0) (pow_ne_zero 2 ha.ne'), Real.log_pow,
    ← Real.exp_add]
  congr 1
  ring

theorem heatConvolution_scale (f : E → ℝ) {a : ℝ} (ha : 0 < a) (x : E) :
    heatConvolution f (a^2) (a • x) =
      Real.exp (-(Module.finrank ℝ E : ℝ)*Real.log a)*rescaledHeat f a⁻¹ x := by
  rw [heatConvolution, gaussianConvolution_scale f ha, heatNormalization_scale ha, rescaledHeat, mul_assoc]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem exp_neg_nat_mul_log {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Real.exp (-(n : ℝ)*Real.log a) = (a^n)⁻¹ := by
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log ha]

end GeometricBrascampLieb

namespace GeometricBrascampLieb.Datum

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)]
  [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)]
  [MeasurableSpace E] [BorelSpace E]
  [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)]
  (D : Datum ι E F) {f : ∀ i, F i → ℝ}
  (hf : ∀ i, Integrable (f i)) (hf0 : ∀ i z, 0 ≤ f i z) (hmass : ∀ i, 0 < ∫ z, f i z)

include hf hf0 hmass

omit [MeasurableSpace E] [BorelSpace E] in
theorem heatProduct_convolution_scale {a : ℝ} (ha : 0 < a) (x : E) :
    D.heatProduct (fun i => convolutionLogHeatFlow (hf i) (hf0 i) (hmass i)) (a^2) (a • x) =
      (a^Module.finrank ℝ E)⁻¹*D.rescaledProduct f a⁻¹ x := by
  rw [← exp_neg_nat_mul_log ha, rescaledProduct, ← Real.exp_add]
  apply congrArg Real.exp
  change (∑ i, D.weight i*Real.log (heatConvolution (f i) (a^2) (D.map i (a • x)))) = _
  simp only [map_smul, heatConvolution_scale _ ha,
    Real.log_mul (Real.exp_pos _).ne' (rescaledHeat_pos (hf _) (hf0 _) (hmass _) a⁻¹ _).ne',
    Real.log_exp]
  calc
    _ = -(Real.log a)*(∑ i, D.weight i*(Module.finrank ℝ (F i) : ℝ))+
        ∑ i, D.weight i*Real.log (rescaledHeat (f i) a⁻¹ (D.map i x)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [D.dimension_identity]; ring

/-- The geometric dimension identity exactly cancels the change-of-variables factor.-/
theorem integral_heatProduct_eq_rescaled {a : ℝ} (ha : 0 < a) :
    (∫ x, D.heatProduct (fun i => convolutionLogHeatFlow (hf i) (hf0 i) (hmass i)) (a^2) x) =
      ∫ x, D.rescaledProduct f a⁻¹ x := by
  let Q := D.heatProduct (fun i => convolutionLogHeatFlow (hf i) (hf0 i) (hmass i)) (a^2)
  have hs := Measure.integral_comp_smul_of_nonneg (volume : Measure E) Q a (hR := ha.le)
  have hp : (∫ x, Q (a • x)) = (a^Module.finrank ℝ E)⁻¹*(∫ x, D.rescaledProduct f a⁻¹ x) := by
    change (∫ x, D.heatProduct (fun i => convolutionLogHeatFlow (hf i) (hf0 i) (hmass i)) (a^2) (a • x)) = _
    simp_rw [D.heatProduct_convolution_scale hf hf0 hmass ha]
    rw [integral_const_mul]
  rw [hp, smul_eq_mul] at hs
  exact (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ ha.ne')) hs).symm

theorem integral_prod_heatConvolution_eq_rescaled {a : ℝ} (ha : 0 < a) :
    (∫ x, ∏ i, (heatConvolution (f i) (a^2) (D.map i x))^D.weight i) =
      ∫ x, D.rescaledProduct f a⁻¹ x := by
  have h := D.integral_heatProduct_eq_rescaled hf hf0 hmass ha
  simp_rw [D.heatProduct_convolution_eq_prod hf hf0 hmass (sq_pos_of_pos ha)] at h
  exact h

end GeometricBrascampLieb.Datum
