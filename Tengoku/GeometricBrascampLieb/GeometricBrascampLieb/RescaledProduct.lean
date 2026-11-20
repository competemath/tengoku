import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.RescaledConvolution
import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.ConvolutionIntegrability

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The Gaussian endpoint of the rescaled geometric product -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GeometricBrascampLieb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integral_normalized_gaussian :
    (∫ x : E, heatNormalization (E := E) 1 * Real.exp (-(1/4 : ℝ)*‖x‖^2)) = 1 := by
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by norm_num : 0 < (1/4 : ℝ))]
  rw [show Real.pi / (1/4 : ℝ) = 4*Real.pi by ring,
    Real.rpow_def_of_pos (by positivity : 0 < 4*Real.pi), heatNormalization]
  simp only [mul_one, ← Real.exp_add]
  rw [show -(↑(Module.finrank ℝ E) / 2) * Real.log (4*Real.pi) +
    Real.log (4*Real.pi) * (↑(Module.finrank ℝ E) / 2) = 0 by ring, Real.exp_zero]

end GeometricBrascampLieb

namespace GeometricBrascampLieb.Datum

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)]
  [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)]
  [MeasurableSpace E] [BorelSpace E]
  [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)]
  (D : Datum ι E F)

def rescaledProduct (f : ∀ i, F i → ℝ) (e : ℝ) (x : E) : ℝ :=
  Real.exp (∑ i, D.weight i*Real.log (rescaledHeat (f i) e (D.map i x)))

omit [MeasurableSpace E] [BorelSpace E]
  [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)] in
theorem sum_weight_affine_quadratic (a : ι → ℝ) (k b : ℝ) (x : E) :
    (∑ i, D.weight i*(a i+k*(Module.finrank ℝ (F i) : ℝ)-b*‖D.map i x‖^2)) =
      (∑ i, D.weight i*a i)+k*(Module.finrank ℝ E : ℝ)-b*‖x‖^2 := by
  calc
    _ = (∑ i, D.weight i*a i)+k*(∑ i, D.weight i*(Module.finrank ℝ (F i) : ℝ))-
        b*(∑ i, D.weight i*‖D.map i x‖^2) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [D.dimension_identity, D.sum_weight_norm_sq]

variable {f : ∀ i, F i → ℝ}
  (hf : ∀ i, Integrable (f i)) (hf0 : ∀ i z, 0 ≤ f i z) (hmass : ∀ i, 0 < ∫ z, f i z)

include hf hf0 hmass

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem rescaledProduct_continuous :
    Continuous (fun p : ℝ × E => D.rescaledProduct f p.1 p.2) := by
  apply Real.continuous_exp.comp
  apply continuous_finsetSum
  intro i _
  apply continuous_const.mul
  have hu : Continuous (fun p : ℝ × E => rescaledHeat (f i) p.1 (D.map i p.2)) :=
    (rescaledHeat_continuous (hf i)).comp (continuous_fst.prodMk ((D.map i).continuous.comp continuous_snd))
  exact hu.log (fun p => (rescaledHeat_pos (hf i) (hf0 i) (hmass i) p.1 _).ne')

omit [MeasurableSpace E] [BorelSpace E] in
theorem rescaledProduct_le {R : ι → ℝ}
    (hsupport : ∀ i z, f i z ≠ 0 → ‖z‖ ≤ R i) {e : ℝ} (he : |e| ≤ 1) (x : E) :
    D.rescaledProduct f e x ≤ D.convolutionAmplitude f R 1*Real.exp (-(1/8 : ℝ)*‖x‖^2) := by
  rw [convolutionAmplitude, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ∑ i, D.weight i*(convolutionLogAmplitude (f i) (R i) 1-(1/8 : ℝ)*‖D.map i x‖^2) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (rescaledHeat_log_le (hf i) (hf0 i) (hmass i) (hsupport i) he _) (D.weight_nonneg i)
    _ = _ := by
      simpa only [zero_mul, add_zero, sub_eq_add_neg, neg_mul] using
        D.sum_weight_affine_quadratic (fun i => convolutionLogAmplitude (f i) (R i) 1) 0 (1/8) x

theorem integral_rescaledProduct_continuousAt_zero {R : ι → ℝ}
    (hsupport : ∀ i z, f i z ≠ 0 → ‖z‖ ≤ R i) :
    ContinuousAt (fun e => ∫ x, D.rescaledProduct f e x) 0 := by
  have hc := D.rescaledProduct_continuous hf hf0 hmass
  have he : ∀ᶠ e : ℝ in 𝓝 0, |e| < 1 :=
    ContinuousAt.eventually_lt continuous_abs.continuousAt continuous_const.continuousAt (by norm_num)
  apply continuousAt_of_dominated
    (bound := fun x : E => D.convolutionAmplitude f R 1*Real.exp (-(1/8 : ℝ)*‖x‖^2))
  · exact Eventually.of_forall fun e =>
      (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [he] with e he
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (show 0 < D.rescaledProduct f e x from Real.exp_pos _)]
      exact D.rescaledProduct_le hf hf0 hmass hsupport he.le x
  · exact (integrable_gaussian (E := E) (by norm_num : 0 < (1/8 : ℝ))).const_mul _
  · exact Eventually.of_forall fun x => (hc.comp (continuous_id.prodMk continuous_const)).continuousAt

omit hf hf0 [MeasurableSpace E] [BorelSpace E] in
theorem rescaledProduct_zero (x : E) :
    D.rescaledProduct f 0 x = Real.exp (∑ i, D.weight i*Real.log (∫ z, f i z))*
      (heatNormalization (E := E) 1*Real.exp (-(1/4 : ℝ)*‖x‖^2)) := by
  rw [rescaledProduct, heatNormalization, ← Real.exp_add, ← Real.exp_add]
  simp only [mul_one, rescaledHeat_log_zero (hmass _)]
  apply congrArg Real.exp
  calc
    _ = ∑ i, D.weight i*(Real.log (∫ z, f i z)+
        (-Real.log (4*Real.pi)/2)*(Module.finrank ℝ (F i) : ℝ)-(1/4 : ℝ)*‖D.map i x‖^2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [D.sum_weight_affine_quadratic]; ring

omit hf hf0 in
theorem integral_rescaledProduct_zero :
    (∫ x, D.rescaledProduct f 0 x) = ∏ i, (∫ z, f i z)^D.weight i := by
  simp_rw [D.rescaledProduct_zero hmass]
  rw [integral_const_mul, integral_normalized_gaussian, mul_one, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [Real.rpow_def_of_pos (hmass i)]
  congr 1
  ring

/-- The rescaled heat-product integral converges to the product of initial masses.-/
theorem tendsto_integral_rescaledProduct_zero {R : ι → ℝ}
    (hsupport : ∀ i z, f i z ≠ 0 → ‖z‖ ≤ R i) :
    Tendsto (fun e => ∫ x, D.rescaledProduct f e x) (𝓝 0)
      (𝓝 (∏ i, (∫ z, f i z)^D.weight i)) := by
  have h := D.integral_rescaledProduct_continuousAt_zero hf hf0 hmass hsupport
  rw [ContinuousAt, D.integral_rescaledProduct_zero hmass] at h
  exact h

end GeometricBrascampLieb.Datum
