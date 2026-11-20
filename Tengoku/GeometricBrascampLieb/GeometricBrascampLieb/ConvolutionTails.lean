import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.ConvolutionBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Gaussian tails for the geometric product of heat convolutions -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeometricBrascampLieb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def convolutionLogAmplitude (f : E → ℝ) (R t : ℝ) : ℝ :=
  -((Module.finrank ℝ E : ℝ)/2)*Real.log (4*Real.pi*t) + Real.log (∫ z, f z) + (4*t)⁻¹*R^2

/--
@isnad1 id=continuo.1h4v.s6.85c97048b73a from=translated src=- shape=0e204d5d vocab=45a1bf1e
-/
theorem convolutionLogAmplitude_continuousAt (f : E → ℝ) (R : ℝ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (convolutionLogAmplitude f R) t := by
  unfold convolutionLogAmplitude
  fun_prop (disch := positivity)

/--
@isnad1 id=le.5h5v.s8.e23dd6daac91 from=translated src=- shape=d13814b6 vocab=5ac137f2
-/
theorem convolutionLogHeatFlow_logValue_le {f : E → ℝ}
    (hf : Integrable f) (hf0 : ∀ z, 0 ≤ f z) (hmass : 0 < ∫ z, f z) {R : ℝ}
    (hsupport : ∀ z, f z ≠ 0 → ‖z‖ ≤ R) {t : ℝ} (ht : 0 < t) (x : E) :
    (convolutionLogHeatFlow hf hf0 hmass).logValue t x ≤
      convolutionLogAmplitude f R t - ((4*t)⁻¹/2)*‖x‖^2 := by
  have hupper : heatConvolution f t x ≤
      Real.exp (convolutionLogAmplitude f R t - ((4*t)⁻¹/2)*‖x‖^2) := by
    calc
      _ ≤ heatNormalization (E := E) t * ((∫ z, f z)*
          (Real.exp ((4*t)⁻¹*R^2)*Real.exp (-((4*t)⁻¹/2)*‖x‖^2))) :=
        mul_le_mul_of_nonneg_left (gaussianConvolution_le_of_support_bound hf hf0 hsupport
          (by positivity : 0 < (4*t)⁻¹) x) (Real.exp_pos _).le
      _ = _ := by
        simp only [convolutionLogAmplitude, heatNormalization, sub_eq_add_neg, Real.exp_add,
          Real.exp_log hmass, neg_mul]
        ring
  have hlog := Real.log_le_log (heatConvolution_pos hf hf0 hmass ht x) hupper
  change Real.log (heatConvolution f t x) ≤ _
  simpa only [Real.log_exp] using hlog

end GeometricBrascampLieb

namespace GeometricBrascampLieb.Datum

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)] [∀ i, FiniteDimensional ℝ (F i)]
  (D : Datum ι E F) (U : ∀ i, LogHeatFlow (F i))

/--
@isnad1 id=le.1h9v.s8.a4f5fa580fc6 from=translated src=- shape=56462a7d vocab=329b4f56
-/
theorem heatProduct_le_of_logValue_le (t : ℝ) (a : ι → ℝ) (b : ℝ)
    (hlog : ∀ i y, (U i).logValue t y ≤ a i-b*‖y‖^2) (x : E) :
    D.heatProduct U t x ≤ Real.exp (∑ i, D.weight i*a i)*Real.exp (-b*‖x‖^2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ∑ i, D.weight i*(a i-b*‖D.map i x‖^2) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hlog i _) (D.weight_nonneg i)
    _ = (∑ i, D.weight i*a i) - b*(∑ i, D.weight i*‖D.map i x‖^2) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [D.sum_weight_norm_sq]; ring

end GeometricBrascampLieb.Datum
