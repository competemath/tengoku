import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Complex.Harmonic.StieltjesRepresentation
import Tengoku.Nlalib.NLAlib.ForMathlib.MeasureTheory.CauchyRegularization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite positive measures are determined by their Stieltjes transforms

Cauchy regularization expresses each bounded continuous integral as a
limit determined by the transform's imaginary part. This proves actual
measure uniqueness without compact support or moment assumptions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace Complex

/-- The Cauchy probability density is the imaginary Cauchy kernel divided by `π`.
@isnad1 id=eq.0h3v.s5.f6daf4dd7b7c from=translated src=- shape=ab78a5ce vocab=55375bd2
-/
theorem cauchyPDFReal_eq_inv_pi_mul_im (x y : ℝ) (γ : NNReal) :
    cauchyPDFReal x γ y = Real.pi⁻¹ *
      (((x : ℂ) - ((y : ℂ) + (γ : ℝ) * I))⁻¹).im := by
  simp only [cauchyPDFReal, inv_im, sub_im, ofReal_im, add_im, mul_im, ofReal_re,
    I_re, I_im, mul_one, mul_zero, zero_add, add_zero, zero_sub, neg_neg,
    normSq_apply, sub_re, add_re, mul_re, sub_zero]
  ring_nf

/-- Cauchy regularized density is determined pointwise by the Stieltjes
transform's imaginary part.
@isnad1 id=eq.1h3v.s6.0a7e47fade36 from=translated src=- shape=c9b4f253 vocab=833e3237
-/
theorem integral_cauchyPDFReal_eq_inv_pi_mul_im_integral
    (μ : Measure ℝ) [IsFiniteMeasure μ] (y : ℝ) (γ : NNReal) (hγ : γ ≠ 0) :
    (∫ x : ℝ, cauchyPDFReal x γ y ∂μ) = Real.pi⁻¹ *
      (∫ x : ℝ, ((x : ℂ) - ((y : ℂ) + (γ : ℝ) * I))⁻¹ ∂μ).im := by
  have hz : 0 < ((y : ℂ) + (γ : ℝ) * I).im := by
    simpa using (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ))
  calc
    _ = ∫ x : ℝ, Real.pi⁻¹ *
        (((x : ℂ) - ((y : ℂ) + (γ : ℝ) * I))⁻¹).im ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall
        (fun x => cauchyPDFReal_eq_inv_pi_mul_im x y γ))
    _ = Real.pi⁻¹ * (∫ x : ℝ,
        (((x : ℂ) - ((y : ℂ) + (γ : ℝ) * I))⁻¹).im ∂μ) := integral_const_mul _ _
    _ = _ := congrArg (fun r : ℝ => Real.pi⁻¹ * r)
      (integral_im (integrable_real_cauchyKernel μ hz))

end Complex
namespace MeasureTheory

/-- Finite positive real measures with the same upper-half-plane
Stieltjes transform are equal. No support or moment premise is required.
Source: the scalar uniqueness bridge in Ajanki--Erdos--Kruger, Proposition 2.1.
This theorem supplies the scalar foundation component.
atlas: matrix-dyson-stieltjes-representation (partial)
@isnad1 id=eq.1h2v.s6.7e62eecaab45 from=translated src=- shape=f2492fbc vocab=9f8a710d
-/
theorem measure_eq_of_integral_real_cauchyKernel_eq (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ z : ℂ, 0 < z.im →
      (∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂μ) = ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂ν) :
    μ = ν := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let γ (n : ℕ) : NNReal := ⟨1 / ((n : ℝ) + 1), by positivity⟩
  have hγne (n : ℕ) : γ n ≠ 0 := by
    apply NNReal.coe_ne_zero.mp
    change 1 / ((n : ℝ) + 1) ≠ 0
    positivity
  have hγ : Tendsto (fun n => (γ n : ℝ)) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
  have he (n : ℕ) (y : ℝ) : (∫ x : ℝ, cauchyPDFReal x (γ n) y ∂μ) =
      ∫ x : ℝ, cauchyPDFReal x (γ n) y ∂ν := by
    rw [Complex.integral_cauchyPDFReal_eq_inv_pi_mul_im_integral μ y _ (hγne n),
      Complex.integral_cauchyPDFReal_eq_inv_pi_mul_im_integral ν y _ (hγne n), h]
    simpa using (show 0 < (γ n : ℝ) from NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (hγne n)))
  have htest : (fun n => ∫ y : ℝ, f y * (∫ x : ℝ, cauchyPDFReal x (γ n) y ∂μ)) =
      fun n => ∫ y : ℝ, f y * (∫ x : ℝ, cauchyPDFReal x (γ n) y ∂ν) := by
    funext n
    simp only [he]
  exact tendsto_nhds_unique (tendsto_integral_cauchyRegularization μ f hγne hγ)
    (htest ▸ tendsto_integral_cauchyRegularization ν f hγne hγ)

end MeasureTheory
