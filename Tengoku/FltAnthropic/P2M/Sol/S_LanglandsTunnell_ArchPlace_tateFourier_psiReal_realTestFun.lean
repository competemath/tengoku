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

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_ArchPlace_tateFourier_psiReal_realTestFun.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_ArchPlace_tateFourier_psiReal_realTestFun

set_option autoImplicit false

open Real Complex Filter Function MeasureTheory Set
open scoped ENNReal NNReal FourierTransform RealInnerProductSpace

noncomputable section

namespace GaussianHermiteFourier

private def tateGaussianℝ : ℝ → ℂ := fun t => (Real.exp (-(π * t ^ 2)) : ℂ)

private def tateGaussianℂRadial : ℝ → ℂ := fun r => (Real.exp (-(2 * π * r ^ 2)) : ℂ)

section Toolkit

private lemma tateGaussianℝ_apply_cexp (x : ℝ) :
    tateGaussianℝ x = Complex.exp (-(π : ℂ) * (x : ℂ) ^ 2) := by
  show (Real.exp (-(π * x ^ 2)) : ℂ) = _
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

private lemma tateGaussianℝ_eq_cexp_fun :
    tateGaussianℝ = fun x : ℝ => Complex.exp (-(π : ℂ) * (x : ℂ) ^ 2) :=
  funext tateGaussianℝ_apply_cexp

private lemma pi_complex_re_pos : (0 : ℝ) < ((π : ℂ)).re := by
  simpa using Real.pi_pos

private lemma integrable_tateGaussianℝ : Integrable tateGaussianℝ := by
  rw [tateGaussianℝ_eq_cexp_fun]
  exact integrable_cexp_neg_mul_sq pi_complex_re_pos

private lemma fourier_tateGaussianℝ_selfdual : 𝓕 tateGaussianℝ = tateGaussianℝ := by
  rw [tateGaussianℝ_eq_cexp_fun]
  have h := fourier_gaussian_pi (b := 1) (by norm_num)
  simpa using h

private lemma fourier_const_mul (r : ℂ) (f : ℝ → ℂ) (w : ℝ) :
    𝓕 (fun x : ℝ => r * f x) w = r * 𝓕 f w := by
  rw [Real.fourier_eq, Real.fourier_eq, ← MeasureTheory.integral_const_mul]
  congr 1
  funext v
  simp only [Circle.smul_def]
  ring

end Toolkit

section SgnComponent

private def tateSgnGaussianℝ : ℝ → ℂ := fun x => (x : ℂ) * tateGaussianℝ x

private theorem tateSgnGaussianℝ_apply (x : ℝ) : tateSgnGaussianℝ x = (x : ℂ) * tateGaussianℝ x := rfl

private lemma hasDerivAt_tateGaussianℝ (ξ : ℝ) :
    HasDerivAt tateGaussianℝ (-(2 * (π : ℂ)) * tateSgnGaussianℝ ξ) ξ := by
  have h1 : HasDerivAt (fun w : ℂ => -(π : ℂ) * w ^ 2) (-(π : ℂ) * (2 * (ξ : ℂ))) (ξ : ℂ) := by
    simpa using (hasDerivAt_pow 2 ((ξ : ℂ))).const_mul (-(π : ℂ))
  have h2 := (h1.cexp).comp_ofReal (z := ξ)
  rw [tateGaussianℝ_eq_cexp_fun, tateSgnGaussianℝ_apply, tateGaussianℝ_apply_cexp]
  convert h2 using 1
  ring

private lemma deriv_tateGaussianℝ_eq :
    deriv tateGaussianℝ = fun x : ℝ => -(2 * (π : ℂ)) * tateSgnGaussianℝ x := by
  funext x
  exact (hasDerivAt_tateGaussianℝ x).deriv

private lemma differentiable_tateGaussianℝ : Differentiable ℝ tateGaussianℝ :=
  fun x => (hasDerivAt_tateGaussianℝ x).differentiableAt

private lemma integrable_tateSgnGaussianℝ : Integrable tateSgnGaussianℝ := by
  have h := integrable_mul_cexp_neg_mul_sq (b := (π : ℂ)) pi_complex_re_pos
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  rw [tateSgnGaussianℝ_apply, tateGaussianℝ_apply_cexp]

private lemma integrable_deriv_tateGaussianℝ : Integrable (deriv tateGaussianℝ) := by
  rw [deriv_tateGaussianℝ_eq]
  exact integrable_tateSgnGaussianℝ.const_mul _

private theorem fourier_tateSgnGaussianℝ :
    𝓕 tateSgnGaussianℝ = fun ξ : ℝ => -Complex.I * tateSgnGaussianℝ ξ := by
  have key := Real.fourier_deriv integrable_tateGaussianℝ differentiable_tateGaussianℝ
    integrable_deriv_tateGaussianℝ
  rw [deriv_tateGaussianℝ_eq, fourier_tateGaussianℝ_selfdual] at key
  have hL : 𝓕 (fun x : ℝ => -(2 * (π : ℂ)) * tateSgnGaussianℝ x)
      = fun ξ : ℝ => -(2 * (π : ℂ)) * 𝓕 tateSgnGaussianℝ ξ := by
    funext ξ
    exact fourier_const_mul _ _ ξ
  rw [hL] at key
  funext ξ
  have hξ := congrFun key ξ
  have h2π : (-(2 * (π : ℂ))) ≠ 0 := by
    simp [Real.pi_ne_zero]
  apply mul_left_cancel₀ h2π
  rw [hξ, smul_eq_mul, tateSgnGaussianℝ_apply]
  ring

end SgnComponent

section Definitions

private def hermiteGaussianℂ (a : ℕ) : ℂ → ℂ :=
  fun z => z ^ a * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)

private def tateHermiteℂ (a : ℕ) : ℂ → ℂ := fun z => (π : ℂ)⁻¹ * z ^ a * tateGaussianℂRadial ‖z‖

private def tateHermiteHatℂ (a : ℕ) : ℂ → ℂ :=
  fun z => (π : ℂ)⁻¹ * (-Complex.I * (starRingEnd ℂ) z) ^ a * tateGaussianℂRadial ‖z‖

private def tateFourierIntegralℂ (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  ∫ z : ℂ, f z * Complex.exp (-(2 * (π : ℂ) * Complex.I) * (z * w + (starRingEnd ℂ) (z * w)))
    ∂((2 : ℝ≥0∞) • volume)

end Definitions

section Toolkit

end Toolkit

section Integrability

end Integrability

section Wirtinger

end Wirtinger

section CoreComputation

end CoreComputation

section TateBridge

end TateBridge

section ArchPlaceObjects

open LanglandsTunnell LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace

private theorem realTestFun_zero_eq : realTestFun 0 = tateGaussianℝ := by
  funext x
  rw [realTestFun_zero_apply, tateGaussianℝ_apply_cexp, neg_mul]

private theorem realTestFun_one_eq : realTestFun 1 = tateSgnGaussianℝ := by
  funext x
  have hv : ((1 : ZMod 2)).val = 1 := by decide
  unfold realTestFun
  rw [hv, pow_one, tateSgnGaussianℝ_apply, tateGaussianℝ_apply_cexp, neg_mul]

private theorem tateFourier_psiReal_eq (f : ℝ → ℂ) (y : ℝ) : tateFourier psiReal volume f y = 𝓕 f y := by
  rw [Real.fourier_real_eq]
  unfold tateFourier
  congr 1
  funext x
  rw [Circle.smul_def, smul_eq_mul, psiReal_apply, Real.fourierChar_apply, mul_comm]
  congr 1
  push_cast
  ring_nf

private theorem tateFourier_psiReal_realTestFun (a : ZMod 2) (y : ℝ) :
    tateFourier psiReal volume (realTestFun a) y = (-Complex.I) ^ a.val * realTestFun a y := by
  rw [tateFourier_psiReal_eq]
  by_cases h : a = 0
  · subst h
    rw [realTestFun_zero_eq, fourier_tateGaussianℝ_selfdual, ZMod.val_zero, pow_zero, one_mul]
  · have h01 : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    have h1 : a = 1 := (h01 a).resolve_left h
    subst h1
    have hv : ((1 : ZMod 2)).val = 1 := by decide
    rw [realTestFun_one_eq, fourier_tateSgnGaussianℝ, hv, pow_one]

end ArchPlaceObjects

end GaussianHermiteFourier

open MeasureTheory LanglandsTunnell LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace

/--
@isnad1 id=eq.0h2v.s5.5bc77c218bea from=translated src=- shape=f78acf6a vocab=d2747fcc
-/
theorem solution (a : ZMod 2) (y : ℝ) :
    tateFourier psiReal volume (realTestFun a) y = (-Complex.I) ^ a.val * realTestFun a y := by
  exact GaussianHermiteFourier.tateFourier_psiReal_realTestFun a y
