import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_TateLocalZeta
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchPlace
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchEpsilon
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Tengoku.Seed.Analysis.Fourier.FourierTransformDeriv
import Tengoku.Seed.Analysis.Complex.RealDeriv
import Tengoku.Seed.Analysis.InnerProductSpace.Calculus
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Complex
import Tengoku.Seed.LinearAlgebra.Complex.FiniteDimensional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_ArchPlace_tateFourier_psiComplex_complexTestFun.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_ArchPlace_tateFourier_psiComplex_complexTestFun

set_option autoImplicit false

open Real Complex Filter Function MeasureTheory Set
open scoped ENNReal NNReal FourierTransform RealInnerProductSpace

noncomputable section

namespace GaussianHermiteFourier

private def tateGaussianℝ : ℝ → ℂ := fun t => (Real.exp (-(π * t ^ 2)) : ℂ)

private def tateGaussianℂRadial : ℝ → ℂ := fun r => (Real.exp (-(2 * π * r ^ 2)) : ℂ)

section Toolkit

end Toolkit

section SgnComponent

private def tateSgnGaussianℝ : ℝ → ℂ := fun x => (x : ℂ) * tateGaussianℝ x

end SgnComponent

section Definitions

private def hermiteGaussianℂ (a : ℕ) : ℂ → ℂ :=
  fun z => z ^ a * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)

private theorem hermiteGaussianℂ_apply (a : ℕ) (z : ℂ) :
    hermiteGaussianℂ a z = z ^ a * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2) := rfl

private def tateHermiteℂ (a : ℕ) : ℂ → ℂ := fun z => (π : ℂ)⁻¹ * z ^ a * tateGaussianℂRadial ‖z‖

private def tateHermiteHatℂ (a : ℕ) : ℂ → ℂ :=
  fun z => (π : ℂ)⁻¹ * (-Complex.I * (starRingEnd ℂ) z) ^ a * tateGaussianℂRadial ‖z‖

private def tateFourierIntegralℂ (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  ∫ z : ℂ, f z * Complex.exp (-(2 * (π : ℂ) * Complex.I) * (z * w + (starRingEnd ℂ) (z * w)))
    ∂((2 : ℝ≥0∞) • volume)

private theorem tateFourierIntegralℂ_def (f : ℂ → ℂ) (w : ℂ) :
    tateFourierIntegralℂ f w
      = ∫ z : ℂ, f z
          * Complex.exp (-(2 * (π : ℂ) * Complex.I) * (z * w + (starRingEnd ℂ) (z * w)))
          ∂((2 : ℝ≥0∞) • volume) := rfl

end Definitions

section Toolkit

private lemma pi_pos' : (0 : ℝ) < π := Real.pi_pos

private lemma gaussian_norm_eq (z : ℂ) :
    ‖Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)‖ = Real.exp (-(2 * π) * ‖z‖ ^ 2) := by
  have h : (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2) = ((-(2 * π) * ‖z‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h, Complex.norm_exp, Complex.ofReal_re]

private lemma hermiteGaussianℂ_norm (a : ℕ) (z : ℂ) :
    ‖hermiteGaussianℂ a z‖ = ‖z‖ ^ a * Real.exp (-(2 * π) * ‖z‖ ^ 2) := by
  rw [hermiteGaussianℂ_apply, norm_mul, norm_pow, gaussian_norm_eq]

end Toolkit

section Integrability

private lemma integrable_rexp_neg_pi_norm_sq :
    Integrable (fun z : ℂ => Real.exp (-π * ‖z‖ ^ 2)) := by
  have h0 : Integrable (fun v : ℂ =>
      Complex.exp (-(π : ℂ) * (‖v‖ : ℂ) ^ 2 + (0 : ℂ) * (⟪(0 : ℂ), v⟫ : ℝ))) :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa using pi_pos') 0 (0 : ℂ)
  have h1 := h0.norm
  refine h1.congr (Filter.Eventually.of_forall fun z => ?_)
  show ‖Complex.exp (-(π : ℂ) * (‖z‖ : ℂ) ^ 2 + (0 : ℂ) * (⟪(0 : ℂ), z⟫ : ℝ))‖
      = Real.exp (-π * ‖z‖ ^ 2)
  have h2 : (-(π : ℂ) * (‖z‖ : ℂ) ^ 2 + (0 : ℂ) * (⟪(0 : ℂ), z⟫ : ℝ))
      = ((-π * ‖z‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h2, Complex.norm_exp, Complex.ofReal_re]

private lemma pow_mul_gaussian_le (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    r ^ k * Real.exp (-(2 * π) * r ^ 2)
      ≤ (1 + (k.factorial : ℝ) * (π⁻¹) ^ k) * Real.exp (-π * r ^ 2) := by
  have hπ : (0 : ℝ) < π := pi_pos'
  have hexp_pos : (0 : ℝ) < Real.exp (-(2 * π) * r ^ 2) := Real.exp_pos _
  have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos k

  have h1 : r ^ k ≤ 1 + r ^ (2 * k) := by
    rcases le_total r 1 with h | h
    · have : r ^ k ≤ 1 := pow_le_one₀ hr h
      nlinarith [pow_nonneg hr (2 * k)]
    · have : r ^ k ≤ r ^ (2 * k) := pow_le_pow_right₀ h (by omega)
      nlinarith

  have h2 : r ^ (2 * k) ≤ (k.factorial : ℝ) * (π⁻¹) ^ k * Real.exp (π * r ^ 2) := by
    have hx : (0 : ℝ) ≤ π * r ^ 2 := by positivity
    have hb := Real.pow_div_factorial_le_exp (x := π * r ^ 2) hx k
    have hb' : (π * r ^ 2) ^ k ≤ (k.factorial : ℝ) * Real.exp (π * r ^ 2) := by
      rw [div_le_iff₀ hfac_pos] at hb
      linarith
    have hexpand : (π * r ^ 2) ^ k = π ^ k * r ^ (2 * k) := by
      rw [mul_pow, ← pow_mul]
    rw [hexpand] at hb'
    have hπk : (0 : ℝ) < π ^ k := pow_pos hπ k
    calc r ^ (2 * k) = (π ^ k * r ^ (2 * k)) / π ^ k := by field_simp
      _ ≤ ((k.factorial : ℝ) * Real.exp (π * r ^ 2)) / π ^ k := by gcongr
      _ = (k.factorial : ℝ) * (π⁻¹) ^ k * Real.exp (π * r ^ 2) := by
          rw [inv_pow]
          ring

  have hsplit : Real.exp (π * r ^ 2) * Real.exp (-(2 * π) * r ^ 2)
      = Real.exp (-π * r ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmono : Real.exp (-(2 * π) * r ^ 2) ≤ Real.exp (-π * r ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg r]
  calc r ^ k * Real.exp (-(2 * π) * r ^ 2)
      ≤ (1 + r ^ (2 * k)) * Real.exp (-(2 * π) * r ^ 2) := by
        apply mul_le_mul_of_nonneg_right h1 hexp_pos.le
    _ = Real.exp (-(2 * π) * r ^ 2) + r ^ (2 * k) * Real.exp (-(2 * π) * r ^ 2) := by ring
    _ ≤ Real.exp (-π * r ^ 2)
          + ((k.factorial : ℝ) * (π⁻¹) ^ k * Real.exp (π * r ^ 2))
            * Real.exp (-(2 * π) * r ^ 2) := by
        gcongr
    _ = Real.exp (-π * r ^ 2)
          + (k.factorial : ℝ) * (π⁻¹) ^ k
            * (Real.exp (π * r ^ 2) * Real.exp (-(2 * π) * r ^ 2)) := by ring
    _ = Real.exp (-π * r ^ 2)
          + (k.factorial : ℝ) * (π⁻¹) ^ k * Real.exp (-π * r ^ 2) := by rw [hsplit]
    _ = (1 + (k.factorial : ℝ) * (π⁻¹) ^ k) * Real.exp (-π * r ^ 2) := by ring

private theorem integrable_norm_pow_mul_gaussianℂ (k : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ k * Real.exp (-(2 * π) * ‖z‖ ^ 2)) := by
  have hcont : Continuous (fun z : ℂ => ‖z‖ ^ k * Real.exp (-(2 * π) * ‖z‖ ^ 2)) := by
    fun_prop
  refine Integrable.mono'
    ((integrable_rexp_neg_pi_norm_sq).const_mul (1 + (k.factorial : ℝ) * (π⁻¹) ^ k))
    hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  have hnonneg : (0 : ℝ) ≤ ‖z‖ ^ k * Real.exp (-(2 * π) * ‖z‖ ^ 2) := by positivity
  rw [Real.norm_of_nonneg hnonneg]
  exact pow_mul_gaussian_le k (norm_nonneg z)

private theorem integrable_hermiteGaussianℂ (a : ℕ) : Integrable (hermiteGaussianℂ a) := by
  have hcont : Continuous (hermiteGaussianℂ a) := by
    unfold hermiteGaussianℂ
    fun_prop
  refine Integrable.mono' (integrable_norm_pow_mul_gaussianℂ a)
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  rw [hermiteGaussianℂ_norm]

end Integrability

section Wirtinger

private lemma hasFDerivAt_coe_norm_sq (z : ℂ) :
    HasFDerivAt (fun w : ℂ => ((‖w‖ ^ 2 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (2 • (innerSL ℝ z))) z := by
  exact Complex.ofRealCLM.hasFDerivAt.comp z (hasStrictFDerivAt_norm_sq z).hasFDerivAt

private lemma hasFDerivAt_gaussian_factor (z : ℂ) :
    HasFDerivAt (fun w : ℂ => Complex.exp (-(2 * (π : ℂ)) * ((‖w‖ : ℂ)) ^ 2))
      (Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)
        • ((-(2 * (π : ℂ))) • (Complex.ofRealCLM.comp (2 • (innerSL ℝ z))))) z := by
  have hfun : (fun w : ℂ => Complex.exp (-(2 * (π : ℂ)) * ((‖w‖ : ℂ)) ^ 2))
      = fun w : ℂ => Complex.exp (-(2 * (π : ℂ)) * ((‖w‖ ^ 2 : ℝ) : ℂ)) := by
    funext w
    congr 1
    push_cast
    ring
  have hinner : HasFDerivAt (fun w : ℂ => -(2 * (π : ℂ)) * ((‖w‖ ^ 2 : ℝ) : ℂ))
      ((-(2 * (π : ℂ))) • (Complex.ofRealCLM.comp (2 • (innerSL ℝ z)))) z :=
    (hasFDerivAt_coe_norm_sq z).const_mul (-(2 * (π : ℂ)))
  have h := hinner.cexp
  rw [hfun]
  convert h using 2 <;> first | rfl | (simp only [Complex.ofReal_pow]; done) | (push_cast; ring_nf)

private lemma hasFDerivAt_hermiteGaussianℂ (a : ℕ) (z : ℂ) :
    HasFDerivAt (hermiteGaussianℂ a)
      ((z ^ a) • (Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)
          • ((-(2 * (π : ℂ))) • (Complex.ofRealCLM.comp (2 • (innerSL ℝ z)))))
        + (Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2))
            • (((a : ℂ) * z ^ (a - 1)) • (1 : ℂ →L[ℝ] ℂ))) z := by
  have hpow : HasFDerivAt (fun w : ℂ => w ^ a)
      (((a : ℂ) * z ^ (a - 1)) • (1 : ℂ →L[ℝ] ℂ)) z :=
    (hasDerivAt_pow a z).complexToReal_fderiv
  exact hpow.mul (hasFDerivAt_gaussian_factor z)

private theorem differentiable_hermiteGaussianℂ (a : ℕ) : Differentiable ℝ (hermiteGaussianℂ a) :=
  fun z => (hasFDerivAt_hermiteGaussianℂ a z).differentiableAt

private lemma fderiv_hermiteGaussianℂ_apply_one (a : ℕ) (z : ℂ) :
    (fderiv ℝ (hermiteGaussianℂ a) z) 1
      = (a : ℂ) * z ^ (a - 1) * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)
        - (4 * (π : ℂ)) * (z.re : ℂ) * z ^ a
            * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2) := by
  rw [(hasFDerivAt_hermiteGaussianℂ a z).fderiv]
  have hinner1 : (innerSL ℝ z) (1 : ℂ) = z.re := by
    simp [innerSL_apply_apply, Complex.inner]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply,
    one_apply_eq_self, hinner1, Complex.ofRealCLM_apply, smul_eq_mul]
  push_cast
  ring

private lemma fderiv_hermiteGaussianℂ_apply_I (a : ℕ) (z : ℂ) :
    (fderiv ℝ (hermiteGaussianℂ a) z) Complex.I
      = (a : ℂ) * z ^ (a - 1) * Complex.I * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)
        - (4 * (π : ℂ)) * (z.im : ℂ) * z ^ a
            * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2) := by
  rw [(hasFDerivAt_hermiteGaussianℂ a z).fderiv]
  have hinnerI : (innerSL ℝ z) Complex.I = z.im := by
    simp [innerSL_apply_apply, Complex.inner]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply,
    one_apply_eq_self, hinnerI, Complex.ofRealCLM_apply, smul_eq_mul]
  push_cast
  ring

private theorem wirtinger_hermiteGaussianℂ (a : ℕ) (z : ℂ) :
    (fderiv ℝ (hermiteGaussianℂ a) z) 1 + Complex.I * ((fderiv ℝ (hermiteGaussianℂ a) z) Complex.I)
      = -(4 * (π : ℂ)) * hermiteGaussianℂ (a + 1) z := by
  rw [fderiv_hermiteGaussianℂ_apply_one, fderiv_hermiteGaussianℂ_apply_I,
    hermiteGaussianℂ_apply]
  have hz : (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := by
    rw [mul_comm]
    exact Complex.re_add_im z
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  calc ((a : ℂ) * z ^ (a - 1) * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)
          - (4 * (π : ℂ)) * (z.re : ℂ) * z ^ a
              * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2))
        + Complex.I * ((a : ℂ) * z ^ (a - 1) * Complex.I
              * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)
          - (4 * (π : ℂ)) * (z.im : ℂ) * z ^ a
              * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2))
      = (1 + Complex.I * Complex.I) * ((a : ℂ) * z ^ (a - 1)
            * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2))
        - (4 * (π : ℂ)) * ((z.re : ℂ) + Complex.I * (z.im : ℂ)) * z ^ a
            * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2) := by ring
    _ = -(4 * (π : ℂ)) * (z * z ^ a * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)) := by
        rw [hI2, hz]
        ring
    _ = -(4 * (π : ℂ)) * (z ^ (a + 1) * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)) := by
        rw [pow_succ]
        ring

private theorem integrable_fderiv_hermiteGaussianℂ (a : ℕ) :
    Integrable (fderiv ℝ (hermiteGaussianℂ a)) := by

  have hcd : ContDiff ℝ 1 (hermiteGaussianℂ a) := by
    unfold hermiteGaussianℂ
    have h1 : ContDiff ℝ 1 (fun z : ℂ => z ^ a) := contDiff_id.pow a
    have h2 : ContDiff ℝ 1 (fun z : ℂ => Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)) := by
      have hbody : ContDiff ℝ 1 (fun z : ℂ => -(2 * (π : ℂ)) * ((‖z‖ ^ 2 : ℝ) : ℂ)) := by
        have hns : ContDiff ℝ 1 (fun z : ℂ => (‖z‖ ^ 2 : ℝ)) := contDiff_norm_sq ℝ
        exact (Complex.ofRealCLM.contDiff.comp hns).const_smul (-(2 * (π : ℂ)))
      have hbody' : (fun z : ℂ => Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2))
          = fun z : ℂ => Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ ^ 2 : ℝ) : ℂ)) := by
        funext w
        congr 1
        push_cast
        ring
      rw [hbody']
      exact hbody.cexp
    exact h1.mul h2
  have hmeas : AEStronglyMeasurable (fderiv ℝ (hermiteGaussianℂ a)) volume :=
    (hcd.continuous_fderiv one_ne_zero).aestronglyMeasurable

  have hdom : Integrable (fun z : ℂ =>
      (a : ℝ) * (‖z‖ ^ (a - 1) * Real.exp (-(2 * π) * ‖z‖ ^ 2))
        + 8 * π * (‖z‖ ^ (a + 1) * Real.exp (-(2 * π) * ‖z‖ ^ 2))) := by
    exact ((integrable_norm_pow_mul_gaussianℂ (a - 1)).const_mul (a : ℝ)).add
      ((integrable_norm_pow_mul_gaussianℂ (a + 1)).const_mul (8 * π))
  refine Integrable.mono' hdom hmeas (Filter.Eventually.of_forall fun z => ?_)

  rw [(hasFDerivAt_hermiteGaussianℂ a z).fderiv]
  have hgauss_norm : ‖Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)‖
      = Real.exp (-(2 * π) * ‖z‖ ^ 2) := gaussian_norm_eq z
  have hexp_le_one' : Real.exp (-(2 * π) * ‖z‖ ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg ‖z‖, pi_pos']
  have hb1 : ‖(z ^ a) • (Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)
      • ((-(2 * (π : ℂ))) • (Complex.ofRealCLM.comp (2 • (innerSL ℝ z)))))‖
      ≤ ‖z‖ ^ a * (Real.exp (-(2 * π) * ‖z‖ ^ 2) * (2 * π * (2 * ‖z‖))) := by
    rw [norm_smul, norm_smul, norm_smul]
    have hcomp : ‖Complex.ofRealCLM.comp (2 • (innerSL ℝ z))‖ ≤ 2 * ‖z‖ := by
      have h2eq : (2 • (innerSL ℝ z) : ℂ →L[ℝ] ℝ) = (2 : ℝ) • (innerSL ℝ z) := by
        module
      rw [h2eq]
      calc ‖Complex.ofRealCLM.comp ((2 : ℝ) • (innerSL ℝ z))‖
          ≤ ‖(Complex.ofRealCLM : ℝ →L[ℝ] ℂ)‖ * ‖(2 : ℝ) • (innerSL ℝ z)‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * (2 * ‖z‖) := by
            apply mul_le_mul
            · exact Complex.ofRealCLM.opNorm_le_bound zero_le_one
                (fun x => by simp [Complex.ofRealCLM_apply])
            · rw [norm_smul]
              simp only [Real.norm_ofNat]
              have := innerSL_apply_norm (𝕜 := ℝ) z
              calc (2 : ℝ) * ‖innerSL ℝ z‖ = 2 * ‖z‖ := by rw [this]
                _ ≤ 2 * ‖z‖ := le_rfl
            · positivity
            · norm_num
        _ = 2 * ‖z‖ := by ring
    have hnegtwo : ‖(-(2 * (π : ℂ)))‖ = 2 * π := by
      rw [norm_neg]
      have : (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [norm_pow, hgauss_norm, hnegtwo]
    have hz2 : (0 : ℝ) ≤ 2 * ‖z‖ := by positivity
    gcongr
  have hb2 : ‖(Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2))
      • (((a : ℂ) * z ^ (a - 1)) • (1 : ℂ →L[ℝ] ℂ))‖
      ≤ Real.exp (-(2 * π) * ‖z‖ ^ 2) * ((a : ℝ) * ‖z‖ ^ (a - 1)) := by
    rw [norm_smul, norm_smul, hgauss_norm]
    have h1le : ‖(1 : ℂ →L[ℝ] ℂ)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hca : ‖(a : ℂ) * z ^ (a - 1)‖ = (a : ℝ) * ‖z‖ ^ (a - 1) := by
      rw [norm_mul, norm_pow, Complex.norm_natCast]
    calc Real.exp (-(2 * π) * ‖z‖ ^ 2) * (‖(a : ℂ) * z ^ (a - 1)‖ * ‖(1 : ℂ →L[ℝ] ℂ)‖)
        ≤ Real.exp (-(2 * π) * ‖z‖ ^ 2) * (‖(a : ℂ) * z ^ (a - 1)‖ * 1) := by
          gcongr
        _ = Real.exp (-(2 * π) * ‖z‖ ^ 2) * ((a : ℝ) * ‖z‖ ^ (a - 1)) := by
          rw [mul_one, hca]
  calc ‖(z ^ a) • (Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)
          • ((-(2 * (π : ℂ))) • (Complex.ofRealCLM.comp (2 • (innerSL ℝ z)))))
        + (Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2))
            • (((a : ℂ) * z ^ (a - 1)) • (1 : ℂ →L[ℝ] ℂ))‖
      ≤ ‖z‖ ^ a * (Real.exp (-(2 * π) * ‖z‖ ^ 2) * (2 * π * (2 * ‖z‖)))
        + Real.exp (-(2 * π) * ‖z‖ ^ 2) * ((a : ℝ) * ‖z‖ ^ (a - 1)) :=
        (norm_add_le _ _).trans (add_le_add hb1 hb2)
    _ ≤ (a : ℝ) * (‖z‖ ^ (a - 1) * Real.exp (-(2 * π) * ‖z‖ ^ 2))
        + 8 * π * (‖z‖ ^ (a + 1) * Real.exp (-(2 * π) * ‖z‖ ^ 2)) := by
        have h1 : ‖z‖ ^ a * (Real.exp (-(2 * π) * ‖z‖ ^ 2) * (2 * π * (2 * ‖z‖)))
            = 4 * π * (‖z‖ ^ (a + 1) * Real.exp (-(2 * π) * ‖z‖ ^ 2)) := by
          rw [pow_succ]
          ring
        have h2 : Real.exp (-(2 * π) * ‖z‖ ^ 2) * ((a : ℝ) * ‖z‖ ^ (a - 1))
            = (a : ℝ) * (‖z‖ ^ (a - 1) * Real.exp (-(2 * π) * ‖z‖ ^ 2)) := by ring
        rw [h1, h2]
        have hpos : (0 : ℝ) ≤ ‖z‖ ^ (a + 1) * Real.exp (-(2 * π) * ‖z‖ ^ 2) := by positivity
        nlinarith [pi_pos']

end Wirtinger

section CoreComputation

private lemma fourierℂ_const_mul (r : ℂ) (f : ℂ → ℂ) (ξ : ℂ) :
    𝓕 (fun z : ℂ => r * f z) ξ = r * 𝓕 f ξ := by
  rw [Real.fourier_eq, Real.fourier_eq, ← MeasureTheory.integral_const_mul]
  congr 1
  funext v
  simp only [Circle.smul_def]
  ring

private lemma fourierℂ_gaussian_base (ξ : ℂ) :
    𝓕 (hermiteGaussianℂ 0) ξ
      = (2 : ℂ)⁻¹ * Complex.exp (-((π : ℂ) / 2) * ((‖ξ‖ : ℂ)) ^ 2) := by
  have h2π : (0 : ℝ) < (2 * (π : ℂ)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    simpa using pi_pos'
  have hfun : hermiteGaussianℂ 0 = fun z : ℂ => Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2) := by
    funext z
    rw [hermiteGaussianℂ_apply, pow_zero, one_mul]
  have hmain := fourier_gaussian_innerProductSpace (V := ℂ) (b := 2 * (π : ℂ)) h2π ξ
  rw [hfun]
  have hdim : (Module.finrank ℝ ℂ : ℂ) / 2 = 1 := by
    rw [Complex.finrank_real_complex]
    norm_num
  rw [hmain]
  have hexp : -(π : ℂ) ^ 2 * ((‖ξ‖ : ℂ)) ^ 2 / (2 * (π : ℂ)) = -((π : ℂ) / 2) * ((‖ξ‖ : ℂ)) ^ 2 := by
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  have hcoef : ((π : ℂ) / (2 * (π : ℂ))) ^ ((Module.finrank ℝ ℂ : ℂ) / 2) = (2 : ℂ)⁻¹ := by
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hbase : (π : ℂ) / (2 * (π : ℂ)) = (2 : ℂ)⁻¹ := by
      field_simp
    rw [hbase, hdim, Complex.cpow_one]
  rw [hcoef, hexp]

private lemma fourierℂ_hermite_succ (a : ℕ) (ξ : ℂ) :
    𝓕 (hermiteGaussianℂ (a + 1)) ξ = (-Complex.I / 2) * ξ * 𝓕 (hermiteGaussianℂ a) ξ := by

  have hkey := Real.fourier_fderiv (V := ℂ) (integrable_hermiteGaussianℂ a)
    (differentiable_hermiteGaussianℂ a) (integrable_fderiv_hermiteGaussianℂ a)

  have happly : ∀ y : ℂ, 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) y) ξ
      = (2 * (π : ℂ) * Complex.I * (⟪ξ, y⟫ : ℝ)) * 𝓕 (hermiteGaussianℂ a) ξ := by
    intro y
    have h1 : 𝓕 (fderiv ℝ (hermiteGaussianℂ a)) ξ y
        = 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) y) ξ :=
      Real.fourier_continuousLinearMap_apply (integrable_fderiv_hermiteGaussianℂ a)
    have h2 : 𝓕 (fderiv ℝ (hermiteGaussianℂ a)) ξ y
        = -(2 * (π : ℂ) * Complex.I) * ((-(⟪ξ, y⟫ : ℝ)) • 𝓕 (hermiteGaussianℂ a) ξ) := by
      rw [hkey]
      rfl
    rw [← h1, h2, Complex.real_smul]
    push_cast
    ring

  have hinner1 : (⟪ξ, (1 : ℂ)⟫ : ℝ) = ξ.re := by
    simp [Complex.inner]
  have hinnerI : (⟪ξ, Complex.I⟫ : ℝ) = ξ.im := by
    simp [Complex.inner]

  have hint1 : Integrable (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) 1) :=
    (integrable_fderiv_hermiteGaussianℂ a).apply_continuousLinearMap 1
  have hintI : Integrable (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) Complex.I) :=
    (integrable_fderiv_hermiteGaussianℂ a).apply_continuousLinearMap Complex.I

  have hcombine : 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) 1
        + Complex.I * ((fderiv ℝ (hermiteGaussianℂ a) z) Complex.I)) ξ
      = 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) 1) ξ
        + Complex.I * 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) Complex.I) ξ := by
    have hsum : 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) 1
          + Complex.I * ((fderiv ℝ (hermiteGaussianℂ a) z) Complex.I)) ξ
        = ∫ v : ℂ, (𝐞 (-⟪v, ξ⟫) : ℂ) * ((fderiv ℝ (hermiteGaussianℂ a) v) 1
            + Complex.I * ((fderiv ℝ (hermiteGaussianℂ a) v) Complex.I)) := by
      rw [Real.fourier_eq]
      congr 1
    have hsplit : ∀ v : ℂ, (𝐞 (-⟪v, ξ⟫) : ℂ) * ((fderiv ℝ (hermiteGaussianℂ a) v) 1
          + Complex.I * ((fderiv ℝ (hermiteGaussianℂ a) v) Complex.I))
        = (𝐞 (-⟪v, ξ⟫) : ℂ) * ((fderiv ℝ (hermiteGaussianℂ a) v) 1)
          + Complex.I * ((𝐞 (-⟪v, ξ⟫) : ℂ) * ((fderiv ℝ (hermiteGaussianℂ a) v) Complex.I)) := by
      intro v
      ring
    have hint1' : Integrable (fun v : ℂ =>
        (𝐞 (-⟪v, ξ⟫) : ℂ) * ((fderiv ℝ (hermiteGaussianℂ a) v) 1)) := by
      have := (Real.fourierIntegral_convergent_iff (f := fun z : ℂ =>
        (fderiv ℝ (hermiteGaussianℂ a) z) 1) ξ).mpr hint1
      refine this.congr (Filter.Eventually.of_forall fun v => ?_)
      simp only [Circle.smul_def]
      ring
    have hintI' : Integrable (fun v : ℂ =>
        Complex.I * ((𝐞 (-⟪v, ξ⟫) : ℂ) * ((fderiv ℝ (hermiteGaussianℂ a) v) Complex.I))) := by
      have := (Real.fourierIntegral_convergent_iff (f := fun z : ℂ =>
        (fderiv ℝ (hermiteGaussianℂ a) z) Complex.I) ξ).mpr hintI
      have h2 := this.const_mul Complex.I
      refine h2.congr (Filter.Eventually.of_forall fun v => ?_)
      simp only [Circle.smul_def]
      ring
    rw [hsum]
    calc ∫ v : ℂ, (𝐞 (-⟪v, ξ⟫) : ℂ) * ((fderiv ℝ (hermiteGaussianℂ a) v) 1
            + Complex.I * ((fderiv ℝ (hermiteGaussianℂ a) v) Complex.I))
        = ∫ v : ℂ, ((𝐞 (-⟪v, ξ⟫) : ℂ) * ((fderiv ℝ (hermiteGaussianℂ a) v) 1)
            + Complex.I * ((𝐞 (-⟪v, ξ⟫) : ℂ)
              * ((fderiv ℝ (hermiteGaussianℂ a) v) Complex.I))) := by
          congr 1
          funext v
          exact hsplit v
      _ = (∫ v : ℂ, (𝐞 (-⟪v, ξ⟫) : ℂ) * ((fderiv ℝ (hermiteGaussianℂ a) v) 1))
            + ∫ v : ℂ, Complex.I * ((𝐞 (-⟪v, ξ⟫) : ℂ)
              * ((fderiv ℝ (hermiteGaussianℂ a) v) Complex.I)) :=
          integral_add hint1' hintI'
      _ = 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) 1) ξ
            + Complex.I * 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) Complex.I) ξ := by
          rw [Real.fourier_eq, MeasureTheory.integral_const_mul, Real.fourier_eq]
          congr 2

  have hwirt : 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) 1
        + Complex.I * ((fderiv ℝ (hermiteGaussianℂ a) z) Complex.I)) ξ
      = -(4 * (π : ℂ)) * 𝓕 (hermiteGaussianℂ (a + 1)) ξ := by
    have hfun : (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) 1
          + Complex.I * ((fderiv ℝ (hermiteGaussianℂ a) z) Complex.I))
        = fun z : ℂ => -(4 * (π : ℂ)) * hermiteGaussianℂ (a + 1) z := by
      funext z
      exact wirtinger_hermiteGaussianℂ a z
    rw [hfun, fourierℂ_const_mul]

  have hξ : (ξ.re : ℂ) + Complex.I * (ξ.im : ℂ) = ξ := by
    rw [mul_comm]
    exact Complex.re_add_im ξ
  have hmain : -(4 * (π : ℂ)) * 𝓕 (hermiteGaussianℂ (a + 1)) ξ
      = (2 * (π : ℂ) * Complex.I * ξ) * 𝓕 (hermiteGaussianℂ a) ξ := by
    calc -(4 * (π : ℂ)) * 𝓕 (hermiteGaussianℂ (a + 1)) ξ
        = 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) 1
            + Complex.I * ((fderiv ℝ (hermiteGaussianℂ a) z) Complex.I)) ξ := hwirt.symm
      _ = 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) 1) ξ
            + Complex.I * 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) Complex.I) ξ :=
          hcombine
      _ = (2 * (π : ℂ) * Complex.I * (ξ.re : ℂ)) * 𝓕 (hermiteGaussianℂ a) ξ
            + Complex.I * ((2 * (π : ℂ) * Complex.I * (ξ.im : ℂ))
              * 𝓕 (hermiteGaussianℂ a) ξ) := by
          rw [happly 1, happly Complex.I, hinner1, hinnerI]
      _ = (2 * (π : ℂ) * Complex.I * ((ξ.re : ℂ) + Complex.I * (ξ.im : ℂ)))
            * 𝓕 (hermiteGaussianℂ a) ξ := by ring
      _ = (2 * (π : ℂ) * Complex.I * ξ) * 𝓕 (hermiteGaussianℂ a) ξ := by rw [hξ]
  have h4π : (-(4 * (π : ℂ))) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero

  have hgoal : (-(4 * (π : ℂ))) * 𝓕 (hermiteGaussianℂ (a + 1)) ξ
      = (-(4 * (π : ℂ))) * ((-Complex.I / 2) * ξ * 𝓕 (hermiteGaussianℂ a) ξ) := by
    rw [hmain]
    ring
  exact mul_left_cancel₀ h4π hgoal

private theorem fourierℂ_pow_mul_gaussian (a : ℕ) (ξ : ℂ) :
    𝓕 (hermiteGaussianℂ a) ξ
      = (2 : ℂ)⁻¹ * (-Complex.I / 2) ^ a * ξ ^ a
          * Complex.exp (-((π : ℂ) / 2) * ((‖ξ‖ : ℂ)) ^ 2) := by
  induction a with
  | zero =>
      rw [fourierℂ_gaussian_base]
      simp
  | succ a ih =>
      rw [fourierℂ_hermite_succ a ξ, ih]
      rw [pow_succ, pow_succ]
      ring

end CoreComputation

section TateBridge

private lemma tate_kernel_eq (z w : ℂ) :
    Complex.exp (-(2 * (π : ℂ) * Complex.I) * (z * w + (starRingEnd ℂ) (z * w)))
      = Complex.exp ((↑(-2 * π * (⟪z, 2 * (starRingEnd ℂ) w⟫ : ℝ)) * Complex.I)) := by
  congr 1
  have hadd : z * w + (starRingEnd ℂ) (z * w) = ((2 * (z * w).re : ℝ) : ℂ) := by
    rw [Complex.add_conj]
  have hinner : (⟪z, 2 * (starRingEnd ℂ) w⟫ : ℝ) = 2 * (z * w).re := by
    rw [Complex.inner]
    have hconj : (2 : ℂ) * (starRingEnd ℂ) w * (starRingEnd ℂ) z
        = (starRingEnd ℂ) (z * w + z * w) := by
      simp only [map_add, map_mul]
      ring
    rw [hconj, Complex.conj_re, Complex.add_re]
    ring
  rw [hadd, hinner]
  push_cast
  ring

private theorem tateFourierIntegralℂ_eq_fourier (f : ℂ → ℂ) (w : ℂ) :
    tateFourierIntegralℂ f w = 2 * 𝓕 f (2 * (starRingEnd ℂ) w) := by
  rw [tateFourierIntegralℂ_def, Real.fourier_eq']
  rw [MeasureTheory.integral_smul_measure]
  have hpt : ∀ z : ℂ,
      f z * Complex.exp (-(2 * (π : ℂ) * Complex.I) * (z * w + (starRingEnd ℂ) (z * w)))
        = Complex.exp ((↑(-2 * π * (⟪z, 2 * (starRingEnd ℂ) w⟫ : ℝ)) * Complex.I)) • f z := by
    intro z
    rw [tate_kernel_eq z w, smul_eq_mul]
    ring
  have hint : (∫ z : ℂ,
      f z * Complex.exp (-(2 * (π : ℂ) * Complex.I) * (z * w + (starRingEnd ℂ) (z * w))))
      = ∫ z : ℂ, Complex.exp ((↑(-2 * π * (⟪z, 2 * (starRingEnd ℂ) w⟫ : ℝ)) * Complex.I)) • f z := by
    congr 1
    funext z
    exact hpt z
  rw [hint]
  simp only [ENNReal.toReal_ofNat, Complex.real_smul, Complex.ofReal_ofNat]

private theorem tateFourierIntegralℂ_pow_mul_gaussian (a : ℕ) (w : ℂ) :
    tateFourierIntegralℂ (hermiteGaussianℂ a) w
      = (-Complex.I * (starRingEnd ℂ) w) ^ a
          * Complex.exp (-(2 * (π : ℂ)) * ((‖w‖ : ℂ)) ^ 2) := by
  rw [tateFourierIntegralℂ_eq_fourier, fourierℂ_pow_mul_gaussian]
  have hnorm : ((‖2 * (starRingEnd ℂ) w‖ : ℝ) : ℂ) ^ 2 = 4 * ((‖w‖ : ℂ)) ^ 2 := by
    have h2 : ‖(2 : ℂ) * (starRingEnd ℂ) w‖ = 2 * ‖w‖ := by
      rw [norm_mul, RCLike.norm_conj]
      simp
    rw [h2]
    push_cast
    ring
  rw [hnorm]
  have hexp : -((π : ℂ) / 2) * (4 * ((‖w‖ : ℂ)) ^ 2) = -(2 * (π : ℂ)) * ((‖w‖ : ℂ)) ^ 2 := by
    ring
  rw [hexp]
  have hpow : ((2 : ℂ) * (starRingEnd ℂ) w) ^ a = 2 ^ a * ((starRingEnd ℂ) w) ^ a := by
    rw [mul_pow]
  have hcoef : (2 : ℂ) * ((2 : ℂ)⁻¹ * (-Complex.I / 2) ^ a * (2 * (starRingEnd ℂ) w) ^ a)
      = (-Complex.I * (starRingEnd ℂ) w) ^ a := by
    rw [hpow]
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    rw [div_pow, mul_pow]
    field_simp
  calc (2 : ℂ) * ((2 : ℂ)⁻¹ * (-Complex.I / 2) ^ a * (2 * (starRingEnd ℂ) w) ^ a
          * Complex.exp (-(2 * (π : ℂ)) * ((‖w‖ : ℂ)) ^ 2))
      = ((2 : ℂ) * ((2 : ℂ)⁻¹ * (-Complex.I / 2) ^ a * (2 * (starRingEnd ℂ) w) ^ a))
          * Complex.exp (-(2 * (π : ℂ)) * ((‖w‖ : ℂ)) ^ 2) := by ring
    _ = (-Complex.I * (starRingEnd ℂ) w) ^ a
          * Complex.exp (-(2 * (π : ℂ)) * ((‖w‖ : ℂ)) ^ 2) := by rw [hcoef]

end TateBridge

private theorem tateFourierIntegralℂ_comp_conj (f : ℂ → ℂ) (w : ℂ) :
    tateFourierIntegralℂ (fun z => f ((starRingEnd ℂ) z)) w
      = tateFourierIntegralℂ f ((starRingEnd ℂ) w) := by
  rw [tateFourierIntegralℂ_eq_fourier, tateFourierIntegralℂ_eq_fourier]
  congr 1
  have hcomp : (fun z : ℂ => f ((starRingEnd ℂ) z)) = f ∘ ⇑Complex.conjLIE := by
    funext z
    simp [Complex.conjLIE_apply]
  rw [hcomp, Real.fourier_comp_linearIsometry]
  rw [Complex.conjLIE_apply, Complex.conj_conj]
  rw [show (2 : ℂ) * (starRingEnd ℂ) w = (starRingEnd ℂ) (w + w) by rw [map_add]; ring]
  rw [Complex.conj_conj]
  ring_nf

section ArchPlaceObjects

open LanglandsTunnell LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace

private theorem complexTestFun_neg_natCast (a : ℕ) : complexTestFun (-(a : ℤ)) = hermiteGaussianℂ a := by
  funext z
  rw [hermiteGaussianℂ_apply, neg_mul]
  unfold complexTestFun
  simp

private theorem complexTestFun_natCast (a : ℕ) :
    complexTestFun (a : ℤ) = fun z => hermiteGaussianℂ a ((starRingEnd ℂ) z) := by
  funext z
  rw [hermiteGaussianℂ_apply, neg_mul, RCLike.norm_conj]
  unfold complexTestFun
  simp

private theorem tateFourier_psiComplex_eq (f : ℂ → ℂ) (w : ℂ) :
    tateFourier psiComplex ((2 : ℝ≥0∞) • volume) f w = tateFourierIntegralℂ f w := by
  unfold tateFourier tateFourierIntegralℂ
  simp only [psiComplex_apply, neg_mul]

private theorem tateFourier_psiComplex_complexTestFun (k : ℤ) (w : ℂ) :
    tateFourier psiComplex ((2 : ℝ≥0∞) • volume) (complexTestFun k) w
      = (-Complex.I) ^ k.natAbs * complexTestFun (-k) w := by
  rw [tateFourier_psiComplex_eq]
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [complexTestFun_natCast, tateFourierIntegralℂ_comp_conj, tateFourierIntegralℂ_pow_mul_gaussian,
      complexTestFun_neg_natCast, hermiteGaussianℂ_apply, Complex.conj_conj, RCLike.norm_conj, Int.natAbs_natCast,
      mul_pow]
    ring
  · rw [complexTestFun_neg_natCast, tateFourierIntegralℂ_pow_mul_gaussian, neg_neg, complexTestFun_natCast]
    dsimp only
    rw [hermiteGaussianℂ_apply, Int.natAbs_neg, Int.natAbs_natCast, RCLike.norm_conj, mul_pow]
    ring

end ArchPlaceObjects

end GaussianHermiteFourier

open MeasureTheory LanglandsTunnell LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped ENNReal

/--
@isnad1 id=eq.0h2v.s7.4b5052cbc870 from=translated src=- shape=86f0c6cf vocab=3ab6d1d9
-/
theorem solution (k : ℤ) (w : ℂ) :
    tateFourier psiComplex ((2 : ℝ≥0∞) • volume) (complexTestFun k) w
      = (-Complex.I) ^ k.natAbs * complexTestFun (-k) w := by
  exact GaussianHermiteFourier.tateFourier_psiComplex_complexTestFun k w
