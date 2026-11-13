import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Complex.Harmonic.RealBoundaryMeasure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Normalized positive Stieltjes representation

A holomorphic upper-half-plane function with nonnegative imaginary part
and finite Stieltjes normalization is the Cauchy transform of an actual
positive finite real measure. This supplies the scalar analytic bridge
in Ajanki--Erdos--Kruger, Proposition 2.1, arXiv:1604.08188v5.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Metric Set
open scoped Topology
namespace Complex

/-- A circle Herglotz kernel is integrable at every upper-half-plane argument.-/
theorem integrable_herglotzRieszKernel_cayley (μ : Measure Circle) [IsFiniteMeasure μ]
    {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun ξ : Circle => herglotzRieszKernel 0 (cayleyTransform z) ξ) μ := by
  have hc := continuous_herglotzRieszKernel_circle
    (by simpa only [mem_ball, dist_zero_right] using norm_cayleyTransform_lt_one hz)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Subtracting the kernel at `i` cancels the affine coordinate, without
a first-moment assumption on the real measure.-/
theorem sub_I_mul_herglotzRieszKernel_cayley
    {z : ℂ} (hz : 0 < z.im) {ξ : Circle} (hξ : ξ ≠ 1) :
    I * herglotzRieszKernel 0 (cayleyTransform z) ξ -
      I * herglotzRieszKernel 0 (cayleyTransform I) ξ =
    (2 / (1 - (ξ : ℂ).re) : ℝ) •
      (((cayleyBoundaryReal ξ : ℂ) - z)⁻¹ - ((cayleyBoundaryReal ξ : ℂ) - I)⁻¹) := by
  rw [I_mul_herglotzRieszKernel_cayleyTransform hz hξ,
    I_mul_herglotzRieszKernel_cayleyTransform (by simp) hξ,
    ← one_add_sq_cayleyBoundaryReal hξ, Complex.real_smul]
  ring

/-- The circle representation transports to the real-line Cauchy
transform after subtracting its value at `i`.-/
theorem integral_sub_herglotzRieszKernel_cayley_eq
    (μ : Measure Circle) [IsFiniteMeasure μ] (hzero : μ {(1 : Circle)} = 0)
    {z : ℂ} (hz : 0 < z.im) :
    I * (∫ ξ : Circle, herglotzRieszKernel 0 (cayleyTransform z) ξ ∂μ) -
      I * (∫ ξ : Circle, herglotzRieszKernel 0 (cayleyTransform I) ξ ∂μ) =
    ∫ x : ℝ, ((x : ℂ) - z)⁻¹ - ((x : ℂ) - I)⁻¹ ∂cayleyBoundaryMeasure μ := by
  have hI : 0 < I.im := by simp
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_sub ((integrable_herglotzRieszKernel_cayley μ hz).const_mul I)
      ((integrable_herglotzRieszKernel_cayley μ hI).const_mul I)]
  rw [cayleyBoundaryMeasure, integral_map measurable_cayleyBoundaryReal.aemeasurable
    (by fun_prop : Measurable (fun x : ℝ => ((x : ℂ) - z)⁻¹ -
      ((x : ℂ) - I)⁻¹)).aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      measurable_cayleyBoundaryWeight.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  have hae : ∀ᵐ ξ : Circle ∂μ, ξ ≠ 1 := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using hzero
  filter_upwards [hae] with ξ hξ
  rw [ENNReal.toReal_ofReal (div_nonneg (by norm_num)
    (sub_nonneg.mpr (circle_re_le_one ξ)))]
  exact sub_I_mul_herglotzRieszKernel_cayley hz hξ

/-- Finite Stieltjes normalization forces decay of the function itself
on the positive imaginary axis.-/
theorem tendsto_zero_of_tendsto_mul_I {f : ℂ → ℂ} {c : ℂ}
    (hlim : Tendsto (fun y : ℝ => (y : ℂ) * I * f ((y : ℂ) * I))
      atTop (𝓝 c)) :
    Tendsto (fun y : ℝ => f ((y : ℂ) * I)) atTop (𝓝 0) := by
  have ht : Tendsto (fun y : ℝ =>
      -I * ((1 / y : ℝ) • ((y : ℂ) * I * f ((y : ℂ) * I)))) atTop (𝓝 0) := by
    simpa only [zero_smul, mul_zero, id_eq] using
      (tendsto_const_nhds (x := -I)).mul
        ((tendsto_id.const_div_atTop (1 : ℝ)).smul hlim)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  rw [Complex.real_smul, ofReal_div, ofReal_one]
  field_simp [ne_of_gt hy]
  simp only [I_sq]
  ring

end Complex
