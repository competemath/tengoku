module

public import Tengoku.Seed.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Tengoku.Seed.Analysis.Complex.Trigonometric
public import Tengoku.Seed.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! Determining finite real measures from their cosine and sine integrals. -/
noncomputable section
open MeasureTheory
namespace Paper

/--
@isnad1 id=integrab.0h2v.s6.ee08b8a82640 from=translated src=- shape=2f37729e vocab=16c4e25f
-/
theorem integrable_fourier_exponential (μ : Measure ℝ) [IsFiniteMeasure μ] (ξ : ℝ) :
    Integrable (fun x : ℝ => Complex.exp ((ξ * x : ℝ) * Complex.I)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
  · fun_prop
  · filter_upwards [] with x
    exact (Complex.norm_exp_ofReal_mul_I (ξ * x)).le

/-- Finite real measures are determined by their cosine and sine integrals.
@isnad1 id=eq.2h2v.s7.0b7c729a6f37 from=translated src=- shape=ab8032a8 vocab=c02c2b8b
-/
theorem measure_eq_of_cos_sin_integrals
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hc : ∀ ξ : ℝ, (∫ x, Real.cos (ξ * x) ∂μ) = ∫ x, Real.cos (ξ * x) ∂ν)
    (hs : ∀ ξ : ℝ, (∫ x, Real.sin (ξ * x) ∂μ) = ∫ x, Real.sin (ξ * x) ∂ν) : μ = ν := by
  apply Measure.ext_of_charFun
  funext ξ
  apply Complex.ext
  · have hμ := integral_re (integrable_fourier_exponential μ ξ)
    have hν := integral_re (integrable_fourier_exponential ν ξ)
    change (∫ x, (Complex.exp ((ξ * x : ℝ) * Complex.I)).re ∂μ) =
      (∫ x, Complex.exp ((ξ * x : ℝ) * Complex.I) ∂μ).re at hμ
    change (∫ x, (Complex.exp ((ξ * x : ℝ) * Complex.I)).re ∂ν) =
      (∫ x, Complex.exp ((ξ * x : ℝ) * Complex.I) ∂ν).re at hν
    simp only [Complex.exp_ofReal_mul_I_re] at hμ hν
    rw [charFun_apply_real, charFun_apply_real]
    simpa only [← Complex.ofReal_mul] using hμ.symm.trans ((hc ξ).trans hν)
  · have hμ := integral_im (integrable_fourier_exponential μ ξ)
    have hν := integral_im (integrable_fourier_exponential ν ξ)
    change (∫ x, (Complex.exp ((ξ * x : ℝ) * Complex.I)).im ∂μ) =
      (∫ x, Complex.exp ((ξ * x : ℝ) * Complex.I) ∂μ).im at hμ
    change (∫ x, (Complex.exp ((ξ * x : ℝ) * Complex.I)).im ∂ν) =
      (∫ x, Complex.exp ((ξ * x : ℝ) * Complex.I) ∂ν).im at hν
    simp only [Complex.exp_ofReal_mul_I_im] at hμ hν
    rw [charFun_apply_real, charFun_apply_real]
    simpa only [← Complex.ofReal_mul] using hμ.symm.trans ((hs ξ).trans hν)

end Paper
