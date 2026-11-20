import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.ConvolutionTails
import Tengoku.Seed.MeasureTheory.Integral.DominatedConvergence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A fixed-width representation of the large-time heat profile

The parameter is the reciprocal spatial scale. At parameter zero the initial
datum contributes only its mass. Continuity follows from domination by `‖f‖`.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace GeometricBrascampLieb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def rescaledConvolution (f : E → ℝ) (e : ℝ) (x : E) : ℝ :=
  ∫ z, f z*Real.exp (-(1/4 : ℝ)*‖x-e • z‖^2)

def rescaledHeat (f : E → ℝ) (e : ℝ) (x : E) : ℝ :=
  heatNormalization (E := E) 1*rescaledConvolution f e x

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/--
@isnad1 id=le.0h5v.s7.e6699ff564a3 from=translated src=- shape=a3dc06ee vocab=7a41c49a
-/
theorem rescaledConvolution_integrand_norm_le (f : E → ℝ) (e : ℝ) (x z : E) :
    ‖f z*Real.exp (-(1/4 : ℝ)*‖x-e • z‖^2)‖ ≤ ‖f z‖ := by
  rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
  have hk : Real.exp (-(1/4 : ℝ)*‖x-e • z‖^2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖x-e • z‖])
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hk (norm_nonneg (f z))

/--
@isnad1 id=integrab.1h4v.s8.0a36e0fdd568 from=translated src=- shape=740f31cc vocab=4462f688
-/
theorem rescaledConvolution_integrand_integrable {f : E → ℝ} (hf : Integrable f)
    (e : ℝ) (x : E) : Integrable (fun z => f z*Real.exp (-(1/4 : ℝ)*‖x-e • z‖^2)) := by
  have hc : Continuous (fun z : E => Real.exp (-(1/4 : ℝ)*‖x-e • z‖^2)) := by fun_prop
  exact hf.norm.mono' (hf.aestronglyMeasurable.mul hc.aestronglyMeasurable)
    (Eventually.of_forall (rescaledConvolution_integrand_norm_le f e x))

/--
@isnad1 id=continuo.1h2v.s7.9f2a37389f80 from=translated src=- shape=53d9c6ad vocab=8c755069
-/
theorem rescaledConvolution_continuous {f : E → ℝ} (hf : Integrable f) :
    Continuous (fun p : ℝ × E => rescaledConvolution f p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply continuousAt_of_dominated (bound := fun z => ‖f z‖)
  · exact Eventually.of_forall fun q =>
      (rescaledConvolution_integrand_integrable hf q.1 q.2).aestronglyMeasurable
  · exact Eventually.of_forall fun q =>
      Eventually.of_forall (rescaledConvolution_integrand_norm_le f q.1 q.2)
  · exact hf.norm
  · exact Eventually.of_forall fun z => by fun_prop

/--
@isnad1 id=continuo.1h2v.s7.f576d884d304 from=translated src=- shape=53d9c6ad vocab=c74b4860
-/
theorem rescaledHeat_continuous {f : E → ℝ} (hf : Integrable f) :
    Continuous (fun p : ℝ × E => rescaledHeat f p.1 p.2) :=
  continuous_const.mul (rescaledConvolution_continuous hf)

/--
@isnad1 id=lt.3h4v.s7.88dfb48a6606 from=translated src=- shape=0f80d476 vocab=fc42cdca
-/
theorem rescaledConvolution_pos {f : E → ℝ} (hf : Integrable f) (hf0 : ∀ z, 0 ≤ f z)
    (hmass : 0 < ∫ z, f z) (e : ℝ) (x : E) : 0 < rescaledConvolution f e x := by
  have hs : Function.support (fun z => f z*Real.exp (-(1/4 : ℝ)*‖x-e • z‖^2)) = Function.support f := by
    ext z
    simp only [Function.mem_support, mul_ne_zero_iff]
    exact ⟨And.left, fun hz => ⟨hz, (Real.exp_pos _).ne'⟩⟩
  rw [rescaledConvolution, integral_pos_iff_support_of_nonneg
    (fun z => mul_nonneg (hf0 z) (Real.exp_pos _).le)
    (rescaledConvolution_integrand_integrable hf e x), hs]
  exact (integral_pos_iff_support_of_nonneg hf0 hf).mp hmass

/--
@isnad1 id=lt.3h4v.s7.e4d33376aca0 from=translated src=- shape=0f80d476 vocab=b8c514bb
-/
theorem rescaledHeat_pos {f : E → ℝ} (hf : Integrable f) (hf0 : ∀ z, 0 ≤ f z)
    (hmass : 0 < ∫ z, f z) (e : ℝ) (x : E) : 0 < rescaledHeat f e x :=
  mul_pos (Real.exp_pos _) (rescaledConvolution_pos hf hf0 hmass e x)

/--
@isnad1 id=eq.0h3v.s7.70d4fb64b4b5 from=translated src=- shape=4bbcc267 vocab=a54001ba
-/
theorem rescaledHeat_zero (f : E → ℝ) (x : E) :
    rescaledHeat f 0 x = heatNormalization (E := E) 1*(∫ z, f z)*Real.exp (-(1/4 : ℝ)*‖x‖^2) := by
  simp only [rescaledHeat, rescaledConvolution, zero_smul, sub_zero, integral_mul_const]
  ring

/--
@isnad1 id=eq.1h3v.s8.829148d466db from=translated src=- shape=1feab35a vocab=cd599e98
-/
theorem rescaledHeat_log_zero {f : E → ℝ} (hmass : 0 < ∫ z, f z) (x : E) :
    Real.log (rescaledHeat f 0 x) =
      -((Module.finrank ℝ E : ℝ)/2)*Real.log (4*Real.pi) + Real.log (∫ z, f z) - (1/4 : ℝ)*‖x‖^2 := by
  rw [rescaledHeat_zero, heatNormalization,
    Real.log_mul (mul_pos (Real.exp_pos _) hmass).ne' (Real.exp_pos _).ne',
    Real.log_mul (Real.exp_pos _).ne' hmass.ne']
  simp only [mul_one, Real.log_exp]
  ring

/--
@isnad1 id=le.5h5v.s8.d2aa8f75ebd4 from=translated src=- shape=3498f9de vocab=7247f312
-/
theorem rescaledHeat_log_le {f : E → ℝ} (hf : Integrable f) (hf0 : ∀ z, 0 ≤ f z)
    (hmass : 0 < ∫ z, f z) {R : ℝ} (hsupport : ∀ z, f z ≠ 0 → ‖z‖ ≤ R)
    {e : ℝ} (he : |e| ≤ 1) (x : E) :
    Real.log (rescaledHeat f e x) ≤ convolutionLogAmplitude f R 1 - (1/8 : ℝ)*‖x‖^2 := by
  have hg : rescaledConvolution f e x ≤
      (∫ z, f z)*(Real.exp ((1/4 : ℝ)*R^2)*Real.exp (-(1/8 : ℝ)*‖x‖^2)) := by
    rw [rescaledConvolution, ← integral_mul_const]
    apply integral_mono (rescaledConvolution_integrand_integrable hf e x) (hf.mul_const _)
    intro z
    by_cases hz : f z = 0
    · simp only [hz, zero_mul, le_refl]
    · have hcentre : ‖e • z‖ ≤ R := by
        rw [norm_smul, Real.norm_eq_abs]
        calc
          |e| * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right he (norm_nonneg z)
          _ = ‖z‖ := one_mul _
          _ ≤ R := hsupport z hz
      have h := gaussian_shift_le_uniform x (e • z) hcentre (by norm_num : 0 ≤ (1/4 : ℝ))
      norm_num only [show (1/4 : ℝ)/2 = 1/8 by norm_num] at h
      exact mul_le_mul_of_nonneg_left h (hf0 z)
  have hu : rescaledHeat f e x ≤ Real.exp (convolutionLogAmplitude f R 1 - (1/8 : ℝ)*‖x‖^2) := by
    calc
      _ ≤ heatNormalization (E := E) 1*((∫ z, f z)*
          (Real.exp ((1/4 : ℝ)*R^2)*Real.exp (-(1/8 : ℝ)*‖x‖^2))) :=
        mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le
      _ = _ := by
        simp only [convolutionLogAmplitude, heatNormalization, mul_one,
          sub_eq_add_neg, Real.exp_add, Real.exp_log hmass, neg_mul]
        norm_num
        ring
  simpa only [Real.log_exp] using Real.log_le_log (rescaledHeat_pos hf hf0 hmass e x) hu

end GeometricBrascampLieb
