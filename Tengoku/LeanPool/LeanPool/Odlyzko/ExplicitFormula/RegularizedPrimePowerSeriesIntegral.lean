/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.DedekindZeta.PrimePowerExpansion
public import Tengoku.LeanPool.LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouQuadraticDecay
import Tengoku.LeanPool.LeanPool.Odlyzko.DedekindZeta.PrimeIdealEulerProduct
public import Tengoku

/-!
# Regularized Prime Power Series Integral

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

section

open Complex MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace

namespace NumberField.Odlyzko

/--
@isnad1 id=le.1h4v.s6.f9b5caabd3b5 from=translated src=- shape=07a53558 vocab=cdda9d3e
-/
theorem norm_fourier_regularizedPoitouVerticalProfile_le_integral
    {δ : ℝ} (_hδ : 0 < δ) (y σ w : ℝ) :
    ‖𝓕 (regularizedPoitouVerticalProfile y δ σ) w‖ ≤
      ∫ x : ℝ, ‖regularizedPoitouVerticalProfile y δ σ x‖ := by
  rw [Real.fourier_real_eq]
  calc
    ‖∫ x : ℝ, 𝐞 (-(x * w)) •
        regularizedPoitouVerticalProfile y δ σ x‖ ≤
      ∫ x : ℝ, ‖𝐞 (-(x * w)) •
        regularizedPoitouVerticalProfile y δ σ x‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by simp

/--
@isnad1 id=le.1h4v.s6.c8065ff7724e from=translated src=- shape=c9e84f49 vocab=ad50d3d0
-/
theorem sq_mul_norm_fourier_regularizedPoitouVerticalProfile_le_integral
    {δ : ℝ} (hδ : 0 < δ) (y σ w : ℝ) :
    w ^ 2 * ‖𝓕 (regularizedPoitouVerticalProfile y δ σ) w‖ ≤
      ∫ x : ℝ,
        ‖poitouVerticalProfileSecondDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ)
          (regularizedScaledTartarSecondDerivative y δ) σ x‖ := by
  let q : ℂ := (2 * Real.pi : ℂ) * I * (w : ℂ)
  have hfourier :=
    fourier_poitouVerticalProfileSecondDerivative_regularized_eq_sq
      hδ y σ w
  have hfactor :
      ‖q ^ 2‖ = (2 * Real.pi) ^ 2 * w ^ 2 := by
    dsimp [q]
    rw [norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs]
    norm_num
    grind
  have hscale : w ^ 2 ≤ (2 * Real.pi) ^ 2 * w ^ 2 := by
    have hp : 1 ≤ (2 * Real.pi) ^ 2 := by
      nlinarith [Real.pi_gt_three]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hp (sq_nonneg w)
  calc
    w ^ 2 * ‖𝓕 (regularizedPoitouVerticalProfile y δ σ) w‖ ≤
        ((2 * Real.pi) ^ 2 * w ^ 2) *
          ‖𝓕 (regularizedPoitouVerticalProfile y δ σ) w‖ :=
      mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
    _ =
        ‖𝓕 (poitouVerticalProfileSecondDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ)
          (regularizedScaledTartarSecondDerivative y δ) σ) w‖ := by
      rw [hfourier, norm_smul, hfactor]
    _ ≤ _ := by
      rw [Real.fourier_real_eq]
      calc
        ‖∫ v : ℝ, 𝐞 (-(v * w)) •
            poitouVerticalProfileSecondDerivative
              (regularizedScaledTartar y δ)
              (regularizedScaledTartarDerivative y δ)
              (regularizedScaledTartarSecondDerivative y δ) σ v‖ ≤
          ∫ v : ℝ, ‖𝐞 (-(v * w)) •
            poitouVerticalProfileSecondDerivative
              (regularizedScaledTartar y δ)
              (regularizedScaledTartarDerivative y δ)
              (regularizedScaledTartarSecondDerivative y δ) σ v‖ :=
            norm_integral_le_integral_norm _
        _ = _ := by simp

/--
@isnad1 id=integrab.1h3v.s6.b4160b0f4aea from=translated src=- shape=2dbceda0 vocab=f81fc04c
-/
theorem fourier_regularizedPoitouVerticalProfile_integrable
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ) :
    Integrable (𝓕 (regularizedPoitouVerticalProfile y δ σ)) := by
  let M : ℝ :=
    ∫ x : ℝ, ‖regularizedPoitouVerticalProfile y δ σ x‖
  let N : ℝ :=
    ∫ x : ℝ,
      ‖poitouVerticalProfileSecondDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ)
        (regularizedScaledTartarSecondDerivative y δ) σ x‖
  have hmajor :
      Integrable (fun w : ℝ ↦ (M + N) * (1 + w ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (M + N)
  apply hmajor.mono'
  · exact
      (VectorFourier.fourierIntegral_continuous
        Real.continuous_fourierChar (innerSL ℝ).continuous₂
        (regularizedPoitouVerticalProfile_integrable hδ σ))
        |>.aestronglyMeasurable
  · filter_upwards [] with w
    have hzero :
        ‖𝓕 (regularizedPoitouVerticalProfile y δ σ) w‖ ≤ M :=
      norm_fourier_regularizedPoitouVerticalProfile_le_integral
        hδ y σ w
    have htwo :
        w ^ 2 * ‖𝓕 (regularizedPoitouVerticalProfile y δ σ) w‖ ≤ N :=
      sq_mul_norm_fourier_regularizedPoitouVerticalProfile_le_integral
        hδ y σ w
    rw [← div_eq_mul_inv,
      le_div_iff₀ (by positivity : 0 < 1 + w ^ 2)]
    nlinarith

/--
@isnad1 id=integrab.1h3v.s6.14f1ebf2e262 from=translated src=- shape=b40fd536 vocab=3a88ee09
-/
theorem poitouTransform_regularizedScaledTartar_vertical_integrable
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ) :
    Integrable (fun t : ℝ ↦
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I)) := by
  let F : ℝ → ℂ := 𝓕 (regularizedPoitouVerticalProfile y δ σ)
  have hF : Integrable F :=
    fourier_regularizedPoitouVerticalProfile_integrable hδ y σ
  have hscale : (-1 / (2 * Real.pi) : ℝ) ≠ 0 := by
    positivity
  have hcomp : Integrable (fun t : ℝ ↦
      F ((-1 / (2 * Real.pi)) * t)) :=
    hF.comp_mul_left' hscale
  apply (integrable_congr (ae_of_all _ fun t ↦ ?_)).mpr hcomp
  rw [poitouTransform_regularizedScaledTartar_eq_fourier]
  grind

end NumberField.Odlyzko

end

section

open Complex MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace

namespace NumberField.Odlyzko

/--
@isnad1 id=eq.1h3v.s6.20d0c28aa966 from=translated src=- shape=ba1c5f1a vocab=4fa0d72f
-/
theorem integral_fourier_regularizedPoitouVerticalProfile
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ) :
    (∫ w : ℝ, 𝓕 (regularizedPoitouVerticalProfile y δ σ) w) =
      regularizedPoitouVerticalProfile y δ σ 0 := by
  have hinv :=
    (regularizedPoitouVerticalProfile_integrable hδ σ).fourierInv_fourier_eq
      (fourier_regularizedPoitouVerticalProfile_integrable hδ y σ)
      (differentiable_regularizedPoitouVerticalProfile y δ σ 0
        |>.continuousAt)
  simpa [Real.fourierInv_eq] using hinv

/--
@isnad1 id=eq.1h3v.s6.c26604a5825a from=translated src=- shape=8abc27aa vocab=508abe32
-/
theorem integral_poitouTransform_regularized_vertical
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ) :
    (∫ t : ℝ,
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I)) =
      (2 * Real.pi : ℂ) := by
  let F : ℝ → ℂ := 𝓕 (regularizedPoitouVerticalProfile y δ σ)
  have hscale := Measure.integral_comp_mul_left
    F (-1 / (2 * Real.pi))
  have harg :
      (fun t : ℝ ↦
        poitouTransform (regularizedScaledTartar y δ) (σ + t * I)) =
      fun t : ℝ ↦ F ((-1 / (2 * Real.pi)) * t) := by
    funext t
    rw [poitouTransform_regularizedScaledTartar_eq_fourier]
    grind
  rw [harg, hscale,
    integral_fourier_regularizedPoitouVerticalProfile hδ y σ]
  have habs :
      |(-1 / (2 * Real.pi))⁻¹| = 2 * Real.pi := by
    rw [inv_div, div_neg, div_one, abs_neg,
      abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  rw [habs]
  unfold regularizedPoitouVerticalProfile poitouKernel
  simp

end NumberField.Odlyzko

end

section

open Complex MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace

namespace NumberField.Odlyzko

/--
@isnad1 id=eq.1h4v.s6.88bc93e54b29 from=translated src=- shape=603a528b vocab=bb328cb3
-/
theorem integral_fourier_mul_cexp_regularizedPoitouVerticalProfile
    {δ : ℝ} (hδ : 0 < δ) (y σ a : ℝ) :
    (∫ w : ℝ,
      Complex.exp (2 * Real.pi * I * w * a) *
        𝓕 (regularizedPoitouVerticalProfile y δ σ) w) =
      regularizedPoitouVerticalProfile y δ σ a := by
  have hinv :=
    (regularizedPoitouVerticalProfile_integrable hδ σ).fourierInv_fourier_eq
      (fourier_regularizedPoitouVerticalProfile_integrable hδ y σ)
      (differentiable_regularizedPoitouVerticalProfile y δ σ a
        |>.continuousAt)
  rw [Real.fourierInv_eq'] at hinv
  convert hinv using 1
  apply integral_congr_ae
  filter_upwards [] with w
  rw [smul_eq_mul]
  congr 2
  norm_num
  ring

/--
@isnad1 id=eq.1h4v.s7.a12ec6110d2f from=translated src=- shape=6772f261 vocab=97c11c28
-/
theorem integral_poitouTransform_regularized_mul_exp_neg
    {δ : ℝ} (hδ : 0 < δ) (y σ a : ℝ) :
    (∫ t : ℝ,
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        Complex.exp (-a * (σ + t * I))) =
      (2 * Real.pi *
        (poitouKernel (regularizedScaledTartar y δ) a : ℂ) *
          Complex.exp (-a / 2)) := by
  let F : ℝ → ℂ := 𝓕 (regularizedPoitouVerticalProfile y δ σ)
  let Q : ℝ → ℂ := fun w ↦
    Complex.exp (2 * Real.pi * I * w * a) * F w *
      Complex.exp (-a * σ)
  have hscale := Measure.integral_comp_mul_left
    Q (-1 / (2 * Real.pi))
  have harg :
      (fun t : ℝ ↦
        poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
          Complex.exp (-a * (σ + t * I))) =
      fun t : ℝ ↦ Q ((-1 / (2 * Real.pi)) * t) := by
    funext t
    rw [poitouTransform_regularizedScaledTartar_eq_fourier]
    dsimp [F, Q]
    have hexp :
      Complex.exp (-a * (σ + t * I)) =
          Complex.exp
              (2 * Real.pi * I *
                (((-1 / (2 * Real.pi)) * t : ℝ) : ℂ) * (a : ℂ)) *
            Complex.exp (-a * σ) := by
      rw [← Complex.exp_add]
      push_cast
      field_simp [Real.pi_ne_zero]
      ring_nf
    grind
  have habs :
      |(-1 / (2 * Real.pi))⁻¹| = 2 * Real.pi := by
    rw [inv_div, div_neg, div_one, abs_neg,
      abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  rw [harg, hscale, habs]
  rw [show (∫ w : ℝ, Q w) =
      (∫ w : ℝ,
        Complex.exp (2 * Real.pi * I * w * a) * F w) *
          Complex.exp (-a * σ) by
    dsimp [Q]
    rw [integral_mul_const]]
  rw [show (∫ w : ℝ,
      Complex.exp (2 * Real.pi * I * w * a) * F w) =
        regularizedPoitouVerticalProfile y δ σ a by
    dsimp [F]
    exact
      integral_fourier_mul_cexp_regularizedPoitouVerticalProfile
        hδ y σ a]
  unfold regularizedPoitouVerticalProfile
  rw [Complex.real_smul]
  push_cast
  calc
    (2 * Real.pi : ℂ) *
          ((poitouKernel (regularizedScaledTartar y δ) a : ℂ) *
            Complex.exp ((σ - 1 / 2) * a) *
            Complex.exp (-a * σ)) =
        (2 * Real.pi : ℂ) *
          (poitouKernel (regularizedScaledTartar y δ) a : ℂ) *
          (Complex.exp ((σ - 1 / 2) * a) *
            Complex.exp (-a * σ)) := by
      ring
    _ = _ := by
      rw [← Complex.exp_add]
      grind

end NumberField.Odlyzko

end

section

open Complex Ideal IsDedekindDomain MeasureTheory Real

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- A prime power location used in the Odlyzko-bound argument. -/
noncomputable def primePowerLocation
    (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) : ℝ :=
  (e + 1 : ℕ) * Real.log (primeIdealNorm K P)

/-- A regularized prime power poitou weight used in the Odlyzko-bound argument. -/
noncomputable def regularizedPrimePowerPoitouWeight
    (y δ : ℝ) (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) : ℝ :=
  Real.log (primeIdealNorm K P) *
    poitouKernel (regularizedScaledTartar y δ)
      (primePowerLocation K P e) *
    Real.exp (-(primePowerLocation K P e) / 2)

/--
@isnad1 id=le.0h5v.s5.d527710f5f09 from=translated src=- shape=9a3f6bff vocab=8294a867
-/
theorem regularizedPrimePowerPoitouWeight_nonneg
    (y δ : ℝ)
    (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    0 ≤ regularizedPrimePowerPoitouWeight K y δ P e := by
  unfold regularizedPrimePowerPoitouWeight
  apply mul_nonneg
  · apply mul_nonneg
    · exact Real.log_nonneg (by
        exact_mod_cast (Nat.le_of_lt (one_lt_primeIdealNorm K P)))
    · unfold poitouKernel
      exact div_nonneg
        (regularizedScaledTartar_nonneg y δ _)
        (Real.cosh_pos _).le
  · exact (Real.exp_pos _).le

/--
@isnad1 id=eq.1h6v.s7.1c809f38d437 from=translated src=- shape=e2dd8f1d vocab=2c2b3b4f
-/
theorem integral_poitouTransform_regularized_mul_primePowerLogTerm
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ)
    (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    (∫ t : ℝ,
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        primePowerLogTerm K P e (σ + t * I)) =
      ((2 * Real.pi *
        regularizedPrimePowerPoitouWeight K y δ P e : ℝ) : ℂ) := by
  simp_rw [primePowerLogTerm_eq_log_mul_cexp_neg]
  rw [show
      (fun t : ℝ ↦
        poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
          ((Real.log (primeIdealNorm K P) : ℂ) *
            Complex.exp
              (-(((e + 1 : ℕ) : ℝ) *
                Real.log (primeIdealNorm K P)) * (σ + t * I)))) =
        fun t : ℝ ↦
          (Real.log (primeIdealNorm K P) : ℂ) *
            (poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
              Complex.exp
                (-(((e + 1 : ℕ) : ℝ) *
                  Real.log (primeIdealNorm K P)) * (σ + t * I))) by
    grind,
    integral_const_mul]
  have h :=
    integral_poitouTransform_regularized_mul_exp_neg
      hδ y σ ((e + 1 : ℕ) * Real.log (primeIdealNorm K P))
  have hinner :
      (∫ t : ℝ,
        poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
          Complex.exp
            (-(((e + 1 : ℕ) : ℝ) *
              Real.log (primeIdealNorm K P)) * (σ + t * I))) =
        2 * Real.pi *
          (poitouKernel (regularizedScaledTartar y δ)
            (((e + 1 : ℕ) : ℝ) *
              Real.log (primeIdealNorm K P)) : ℂ) *
          Complex.exp
            (-((((e + 1 : ℕ) : ℝ) *
              Real.log (primeIdealNorm K P))) / 2) := by simp_all
  rw [hinner]
  unfold regularizedPrimePowerPoitouWeight primePowerLocation
  push_cast
  ring

end NumberField.Odlyzko

end

section

open Complex Ideal IsDedekindDomain MeasureTheory Real

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/--
@isnad1 id=hassum.2h4v.s8.dab8f96ffa2c from=translated src=- shape=ea484985 vocab=215b2f18
-/
theorem hasSum_integral_poitouTransform_regularized_mul_primePowerLogTerm
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    HasSum
      (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
        ∫ t : ℝ,
          poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
            primePowerLogTerm K pe.1 pe.2 (σ + t * I))
      (∫ t : ℝ,
        ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
          poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
            primePowerLogTerm K pe.1 pe.2 (σ + t * I)) := by
  let Φ : ℝ → ℂ := fun t ↦
    poitouTransform (regularizedScaledTartar y δ) (σ + t * I)
  let b : HeightOneSpectrum (𝓞 K) × ℕ → ℝ := fun pe ↦
    ‖primePowerLogTerm K pe.1 pe.2 (σ : ℂ)‖
  have hΦ : Integrable Φ :=
    poitouTransform_regularizedScaledTartar_vertical_integrable hδ y σ
  have hb : Summable b :=
    summable_norm_primePowerLogTerm K
      (s := (σ : ℂ)) (by simpa using hσ)
  apply hasSum_integral_of_dominated_convergence
    (fun pe t ↦ ‖Φ t‖ * b pe)
  · intro pe
    apply hΦ.aestronglyMeasurable.mul
    have heq :
        (fun t : ℝ ↦ primePowerLogTerm K pe.1 pe.2 (σ + t * I)) =
          fun t : ℝ ↦
            (Real.log (primeIdealNorm K pe.1) : ℂ) *
              Complex.exp
                (-(((pe.2 + 1 : ℕ) : ℝ) *
                  Real.log (primeIdealNorm K pe.1)) * (σ + t * I)) := by
      funext t
      exact primePowerLogTerm_eq_log_mul_cexp_neg K pe.1 pe.2 _
    rw [heq]
    fun_prop
  · intro pe
    filter_upwards [] with t
    rw [norm_mul]
    dsimp only [Φ]
    dsimp only [b]
    rw [norm_primePowerLogTerm, norm_primePowerLogTerm]
    simp
  · filter_upwards [] with t
    exact hb.mul_left ‖Φ t‖
  · have hnorm : Integrable (fun t ↦ ‖Φ t‖) := hΦ.norm
    convert hnorm.const_mul (∑' pe, b pe) using 1
    funext t
    rw [tsum_mul_left]
    ring
  · filter_upwards [] with t
    have hst : 1 < (σ + t * I : ℂ).re := by simpa using hσ
    exact
      (((summable_norm_primePowerLogTerm K hst).of_norm.mul_left (Φ t)).hasSum)

/--
@isnad1 id=eq.2h4v.s7.e37e36fcd1a6 from=translated src=- shape=145ce605 vocab=ee049247
-/
theorem integral_poitouTransform_regularized_mul_neg_logDeriv_dedekindZeta_eq_tsum
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    (∫ t : ℝ,
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        (-logDeriv (dedekindZeta K) (σ + t * I))) =
      ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
        ((2 * Real.pi *
          regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2 : ℝ) : ℂ) := by
  calc
    _ = ∫ t : ℝ,
        ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
          poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
            primePowerLogTerm K pe.1 pe.2 (σ + t * I) := by
      apply integral_congr_ae
      filter_upwards [] with t
      have hst : 1 < (σ + t * I : ℂ).re := by simpa using hσ
      rw [neg_logDeriv_dedekindZeta_eq_tsum_primePower K hst,
        tsum_mul_left]
    _ = ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
        ∫ t : ℝ,
          poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
            primePowerLogTerm K pe.1 pe.2 (σ + t * I) :=
      (hasSum_integral_poitouTransform_regularized_mul_primePowerLogTerm
        K hδ y hσ).tsum_eq.symm
    _ = _ := by
      congr 1
      funext pe
      exact integral_poitouTransform_regularized_mul_primePowerLogTerm
        K hδ y σ pe.1 pe.2

/--
@isnad1 id=summable.2h4v.s6.dca6105993bb from=translated src=- shape=d24780f2 vocab=908ef407
-/
theorem summable_regularizedPrimePowerPoitouWeight
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
      regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2) := by
  have hs :
      Summable (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
        ((2 * Real.pi *
          regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2 : ℝ) : ℂ)) := by
    apply
      (hasSum_integral_poitouTransform_regularized_mul_primePowerLogTerm
        K hδ y hσ).summable.congr
    intro pe
    exact integral_poitouTransform_regularized_mul_primePowerLogTerm
      K hδ y σ pe.1 pe.2
  have hsReal :
      Summable (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
        2 * Real.pi *
          regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2) :=
    Complex.summable_ofReal.mp hs
  exact (summable_mul_left_iff (mul_ne_zero (by norm_num) Real.pi_ne_zero)).mp hsReal

/--
@isnad1 id=le.0h3v.s6.8c45ce0f8eef from=translated src=- shape=0a0675bd vocab=eea6c0d3
-/
theorem tsum_regularizedPrimePowerPoitouWeight_nonneg
    (y δ : ℝ) :
    0 ≤ ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
      regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2 :=
  tsum_nonneg fun pe ↦
    regularizedPrimePowerPoitouWeight_nonneg K y δ pe.1 pe.2

end NumberField.Odlyzko

end
