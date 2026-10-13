/-
Copyright (c) 2024 Sidharth Hariharan and 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Sidharth Hariharan, Gareth Ma, Dean Cureton
-/

module

public import Tengoku

/-!
# Foundations

Foundational test functions and the first saddle-point estimates.
-/

namespace CohnElkies

section

open Filter MeasureTheory
open scoped FourierTransform SchwartzMap Topology

/-- The Euclidean space used in ambient dimension `d`. -/
public
noncomputable abbrev Euclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Complex Schwartz test functions in ambient dimension `d`. -/
public
noncomputable abbrev TestFunction (d : ℕ) := 𝓢(Euclidean d, ℂ)

private noncomputable def IsRealValued {d : ℕ} (f : TestFunction d) : Prop :=
  ∀ x : Euclidean d, (f x).im = 0

private noncomputable def IsRadial {d : ℕ} (f : TestFunction d) : Prop :=
  ∀ x y : Euclidean d, ‖x‖ = ‖y‖ → f x = f y

private structure Admissible (d : ℕ) where
  function : TestFunction d
  real : IsRealValued function
  radial : IsRadial function
  fourier_real : IsRealValued (𝓕 function)
  fourier_nonneg : ∀ ξ : Euclidean d, 0 ≤ ((𝓕 function) ξ).re
  fourier_zero_pos : 0 < ((𝓕 function) (0 : Euclidean d)).re
  outside_nonpos :
    ∀ x : Euclidean d, 1 ≤ ‖x‖ → (function x).re ≤ 0

/-- The analytic formula for the volume of the unit ball in dimension `d`. -/
public
noncomputable def unitBallVolume (d : ℕ) : ℝ :=
  Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)

private noncomputable def quotient {d : ℕ} (f : Admissible d) : ℝ :=
  (f.function (0 : Euclidean d)).re /
    ((𝓕 f.function) (0 : Euclidean d)).re

private noncomputable def quotientSet (d : ℕ) : Set ℝ :=
  Set.range (quotient (d := d))

private noncomputable def linearProgram (d : ℕ) : ℝ :=
  unitBallVolume d / (2 : ℝ) ^ d * sInf (quotientSet d)

private noncomputable def normalizedCost {d : ℕ} (f : Admissible d) : ℝ :=
  quotient f ^ ((d : ℝ)⁻¹) / Real.sqrt (d : ℝ)

private noncomputable def normalizedProgram (d : ℕ) : ℝ :=
  sInf (Set.range (normalizedCost (d := d)))

private noncomputable def criticalPackingBase : ℝ :=
  Real.sqrt (Real.exp 1 / (2 * Real.pi))

private noncomputable def criticalBinaryExponent : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1)

private noncomputable def SharpQuotientAsymptotic : Prop :=
  Tendsto normalizedProgram atTop (nhds Real.pi⁻¹)

private noncomputable def SharpLogAsymptotic : Prop :=
  Tendsto (fun d : ℕ => Real.log (linearProgram d) / (d : ℝ))
    atTop (nhds ((1 / 2 : ℝ) * Real.log (Real.exp 1 / (2 * Real.pi))))

private noncomputable def SharpPackingRootAsymptotic : Prop :=
  Tendsto (fun d : ℕ => (linearProgram d) ^ ((d : ℝ)⁻¹))
    atTop (nhds criticalPackingBase)

end

section

private noncomputable def shellWeight (ε : ℝ) : ℝ :=
  Real.exp (-(3 : ℝ) * ε * (ε⁻¹ ^ 3) / 8)

private noncomputable def plusPolynomial (ε : ℝ) (z : ℂ) : ℂ :=
  1 + z ^ 2 + ((ε / 4 : ℝ) : ℂ) + Complex.I * z * (1 + z ^ 2)

private noncomputable def minusPolynomial (ε : ℝ) (z : ℂ) : ℂ :=
  1 + z ^ 2 + ((ε / 4 : ℝ) : ℂ) - Complex.I * z * (1 + z ^ 2)

end

section

open MeasureTheory
open scoped FourierTransform

private noncomputable def mellinFrequency (ℓ : ℝ) (profile : ℝ → ℂ) (t : ℝ) : ℂ :=
  mellin profile ((ℓ : ℂ) - Complex.I * (t : ℂ))

private noncomputable def mellinMultiplier (ℓ t : ℝ) : ℂ :=
  Complex.exp
      (Complex.I * (t : ℂ) * (Real.log Real.pi : ℂ)) *
    Complex.Gamma (((ℓ : ℂ) - Complex.I * (t : ℂ)) / 2) /
    Complex.Gamma (((ℓ : ℂ) + Complex.I * (t : ℂ)) / 2)

end

section

open Filter MeasureTheory
open scoped FourierTransform SchwartzMap

private noncomputable def IsEven {d : ℕ} (f : TestFunction d) : Prop :=
  ∀ x : Euclidean d, f (-x) = f x

private theorem IsRadial.even {d : ℕ} {f : TestFunction d}
    (hf : IsRadial f) : IsEven f := by
  intro x
  exact hf (-x) x (by simp only [norm_neg])

private theorem fourierInv_apply_zero {d : ℕ} (f : TestFunction d) :
    (𝓕⁻ f : TestFunction d) (0 : Euclidean d) =
      ∫ x : Euclidean d, f x := by
  calc
    (𝓕⁻ f : TestFunction d) (0 : Euclidean d) =
        (𝓕⁻ (f : Euclidean d → ℂ)) (0 : Euclidean d) :=
      congrFun (SchwartzMap.fourierInv_coe f) 0
    _ = ∫ x : Euclidean d, f x := by
      rw [Real.fourierInv_eq]
      simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul]

private theorem admissible_zero_pos {d : ℕ} (f : Admissible d) :
    0 < (f.function (0 : Euclidean d)).re := by
  have hpositive : 0 < ∫ x : Euclidean d, ((𝓕 f.function) x).re := by
    exact integral_pos_of_integrable_nonneg_nonzero
      (Complex.continuous_re.comp (𝓕 f.function).continuous)
      (𝓕 f.function).integrable.re
      f.fourier_nonneg f.fourier_zero_pos.ne'
  have hinversion :
      (∫ x : Euclidean d, (𝓕 f.function) x) =
        f.function (0 : Euclidean d) := by
    have h := congrArg (fun g : TestFunction d => g (0 : Euclidean d))
      (show (𝓕⁻ (𝓕 f.function) : TestFunction d) = f.function from
        FourierTransform.fourierInv_fourier_eq f.function)
    simpa only [fourierInv_apply_zero] using! h
  calc
    (0 : ℝ) < (∫ x : Euclidean d, ((𝓕 f.function) x).re) := hpositive
    _ = (∫ x : Euclidean d, (𝓕 f.function) x).re :=
      integral_re (𝓕 f.function).integrable
    _ = (f.function (0 : Euclidean d)).re :=
      congrArg Complex.re hinversion

private theorem fourier_sq_apply {d : ℕ} (f : TestFunction d) (x : Euclidean d) :
    ((𝓕 (𝓕 f) : TestFunction d) x) = f (-x) := by
  have hinv := congrArg (fun g : TestFunction d => g (-x))
    (show (𝓕⁻ (𝓕 f) : TestFunction d) = f from
      FourierTransform.fourierInv_fourier_eq f)
  have hchange :
      ((𝓕⁻ (𝓕 f) : TestFunction d) (-x)) =
        ((𝓕 (𝓕 f) : TestFunction d) x) := by
    calc
      ((𝓕⁻ (𝓕 f) : TestFunction d) (-x)) =
          (𝓕⁻ ((𝓕 f : TestFunction d) : Euclidean d → ℂ)) (-x) :=
        congrFun (SchwartzMap.fourierInv_coe (𝓕 f)) (-x)
      _ = (𝓕 ((𝓕 f : TestFunction d) : Euclidean d → ℂ)) x := by
        rw [Real.fourierInv_eq_fourier_neg]
        simp only [neg_neg]
      _ = ((𝓕 (𝓕 f) : TestFunction d) x) :=
        (congrFun (SchwartzMap.fourier_coe (𝓕 f)) x).symm
  exact hchange ▸ hinv

private theorem fourier_sq_of_radial {d : ℕ} (f : TestFunction d)
    (hf : IsRadial f) : (𝓕 (𝓕 f) : TestFunction d) = f := by
  ext x
  rw [fourier_sq_apply]
  exact hf.even x

private noncomputable def antiFourierPart {d : ℕ} (f : TestFunction d) : TestFunction d :=
  𝓕 f - f

private theorem fourier_antiFourierPart {d : ℕ} (f : TestFunction d)
    (hf : IsRadial f) :
    (𝓕 (antiFourierPart f) : TestFunction d) = -antiFourierPart f := by
  rw [antiFourierPart, sub_eq_add_neg, FourierTransform.fourier_add,
    FourierTransform.fourier_neg, fourier_sq_of_radial f hf]
  simp only [neg_add_rev, neg_neg]

private theorem antiFourierPart_zero {d : ℕ} (f : TestFunction d)
    (hbalance : (𝓕 f : TestFunction d) (0 : Euclidean d) = f 0) :
    antiFourierPart f (0 : Euclidean d) = 0 := by
  change (𝓕 f : TestFunction d) 0 - f 0 = 0
  exact sub_eq_zero.mpr hbalance

private theorem antiFourierPart_nonneg_of_signs {d : ℕ}
    (f : TestFunction d) (R : ℝ)
    (hfourier : ∀ x : Euclidean d, 0 ≤ ((𝓕 f) x).re)
    (houtside : ∀ x : Euclidean d, R ≤ ‖x‖ → (f x).re ≤ 0)
    (x : Euclidean d) (hx : R ≤ ‖x‖) :
    0 ≤ (antiFourierPart f x).re := by
  change 0 ≤ ((𝓕 f) x).re - (f x).re
  linarith [hfourier x, houtside x hx]

private structure AntiFourierWitness (d : ℕ) (R : ℝ) where
  function : TestFunction d
  real : IsRealValued function
  radial : IsRadial function
  nonzero : function ≠ 0
  anti_fourier : (𝓕 function : TestFunction d) = -function
  zero_value : function (0 : Euclidean d) = 0
  eventually_nonneg :
    ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ (function x).re

private noncomputable def UniformAntiFourierSignRadius : Prop :=
  ∀ c : ℝ, 0 < c → c < Real.pi⁻¹ →
    ∀ᶠ d : ℕ in atTop,
      IsEmpty (AntiFourierWitness d (c * Real.sqrt (d : ℝ)))

end

section

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology RealInnerProductSpace ENNReal NNReal

private noncomputable def dilationEquiv (d : ℕ) (a : ℝ) (ha : a ≠ 0) :
    Euclidean d ≃L[ℝ] Euclidean d :=
  (LinearEquiv.smulOfNeZero ℝ (Euclidean d) a ha).toContinuousLinearEquiv

@[simp] private theorem dilationEquiv_apply (d : ℕ) (a : ℝ) (ha : a ≠ 0)
    (x : Euclidean d) : dilationEquiv d a ha x = a • x := by
  rfl

private noncomputable def dilate {d : ℕ} (f : TestFunction d) (a : ℝ) (ha : 0 < a) :
    TestFunction d :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (dilationEquiv d a ha.ne') f

@[simp] private theorem dilate_apply {d : ℕ} (f : TestFunction d)
    (a : ℝ) (ha : 0 < a) (x : Euclidean d) :
    dilate f a ha x = f (a • x) := by
  rfl

private theorem dilate_zero {d : ℕ} (f : TestFunction d)
    (a : ℝ) (ha : 0 < a) :
    dilate f a ha (0 : Euclidean d) = f 0 := by
  simp only [dilate_apply, smul_zero]

private theorem IsRealValued.dilate {d : ℕ} {f : TestFunction d}
    (hf : IsRealValued f) (a : ℝ) (ha : 0 < a) :
    IsRealValued (dilate f a ha) := by
  intro x
  exact hf (a • x)

private theorem IsRadial.dilate {d : ℕ} {f : TestFunction d}
    (hf : IsRadial f) (a : ℝ) (ha : 0 < a) :
    IsRadial (dilate f a ha) := by
  intro x y hxy
  apply hf
  simp only [ContinuousLinearEquiv.coe_coe, dilationEquiv_apply, norm_smul, Real.norm_eq_abs, hxy]

private theorem fourier_dilate_apply {d : ℕ} (f : TestFunction d)
    (a : ℝ) (ha : 0 < a) (ξ : Euclidean d) :
    ((𝓕 (dilate f a ha) : TestFunction d) ξ) =
      (a ^ d)⁻¹ • ((𝓕 f : TestFunction d) (a⁻¹ • ξ)) := by
  have hinner (x : Euclidean d) :
      @inner ℝ (Euclidean d) _ (a • x) (a⁻¹ • ξ) =
        @inner ℝ (Euclidean d) _ x ξ := by
    rw [real_inner_smul_left, real_inner_smul_right]
    field_simp
  calc
    ((𝓕 (dilate f a ha) : TestFunction d) ξ) =
        (𝓕 ((dilate f a ha : TestFunction d) : Euclidean d → ℂ)) ξ :=
      congrFun (SchwartzMap.fourier_coe (dilate f a ha)) ξ
    _ = ∫ x : Euclidean d,
          Complex.exp
            ((↑(-2 * Real.pi * @inner ℝ (Euclidean d) _ x ξ) : ℂ) * Complex.I) •
              f (a • x) := by
      rw [Real.fourier_eq']
      rfl
    _ = ∫ x : Euclidean d,
          (fun y : Euclidean d =>
            Complex.exp
              ((↑(-2 * Real.pi *
                @inner ℝ (Euclidean d) _ y (a⁻¹ • ξ)) : ℂ) * Complex.I) • f y)
            (a • x) := by
      congr 1
      funext x
      simp only [hinner x]
    _ = (a ^ d)⁻¹ •
          ∫ y : Euclidean d,
            Complex.exp
              ((↑(-2 * Real.pi *
                @inner ℝ (Euclidean d) _ y (a⁻¹ • ξ)) : ℂ) * Complex.I) • f y := by
      simpa only [neg_mul, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat,
        smul_eq_mul,
        Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow, finrank_euclideanSpace,
          Fintype.card_fin] using!
        (MeasureTheory.Measure.integral_comp_smul_of_nonneg
          (volume : Measure (Euclidean d))
          (fun y : Euclidean d =>
            Complex.exp
              ((↑(-2 * Real.pi *
                @inner ℝ (Euclidean d) _ y (a⁻¹ • ξ)) : ℂ) * Complex.I) • f y)
          a (hR := ha.le))
    _ = (a ^ d)⁻¹ • ((𝓕 f : TestFunction d) (a⁻¹ • ξ)) := by
      rw [← Real.fourier_eq']
      rw [SchwartzMap.fourier_coe]

private theorem fourier_dilate_zero {d : ℕ} (f : TestFunction d)
    (a : ℝ) (ha : 0 < a) :
    ((𝓕 (dilate f a ha) : TestFunction d) (0 : Euclidean d)) =
      (a ^ d)⁻¹ • ((𝓕 f : TestFunction d) (0 : Euclidean d)) := by
  simpa only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow,
    smul_zero] using! fourier_dilate_apply f a ha 0

private noncomputable def balancingScale {d : ℕ} (f : Admissible d) : ℝ :=
  (((𝓕 f.function : TestFunction d) (0 : Euclidean d)).re /
      (f.function (0 : Euclidean d)).re) ^ ((d : ℝ)⁻¹)

private theorem balancingScale_pos {d : ℕ} (f : Admissible d) :
    0 < balancingScale f := by
  unfold balancingScale
  exact Real.rpow_pos_of_pos
    (div_pos f.fourier_zero_pos (admissible_zero_pos f)) _

private theorem balancingScale_pow {d : ℕ} (f : Admissible d) (hd : 0 < d) :
    balancingScale f ^ d =
      ((𝓕 f.function : TestFunction d) (0 : Euclidean d)).re /
        (f.function (0 : Euclidean d)).re := by
  unfold balancingScale
  exact Real.rpow_inv_natCast_pow
    (div_pos f.fourier_zero_pos (admissible_zero_pos f)).le
    (Nat.ne_of_gt hd)

private noncomputable def balancedFunction {d : ℕ} (f : Admissible d) : TestFunction d :=
  dilate f.function (balancingScale f) (balancingScale_pos f)

@[simp] private theorem balancedFunction_apply {d : ℕ} (f : Admissible d)
    (x : Euclidean d) :
    balancedFunction f x = f.function (balancingScale f • x) := by
  rfl

private theorem balancedFunction_real {d : ℕ} (f : Admissible d) :
    IsRealValued (balancedFunction f) :=
  f.real.dilate (balancingScale f) (balancingScale_pos f)

private theorem balancedFunction_radial {d : ℕ} (f : Admissible d) :
    IsRadial (balancedFunction f) :=
  f.radial.dilate (balancingScale f) (balancingScale_pos f)

private theorem balancedFunction_fourier_real {d : ℕ} (f : Admissible d) :
    IsRealValued (𝓕 (balancedFunction f) : TestFunction d) := by
  intro ξ
  unfold balancedFunction
  rw [fourier_dilate_apply, Complex.smul_im,
    f.fourier_real ((balancingScale f)⁻¹ • ξ)]
  simp only [smul_eq_mul, mul_zero]

private theorem balancedFunction_fourier_nonneg {d : ℕ} (f : Admissible d)
    (ξ : Euclidean d) :
    0 ≤ ((𝓕 (balancedFunction f) : TestFunction d) ξ).re := by
  unfold balancedFunction
  rw [fourier_dilate_apply, Complex.smul_re]
  simpa only [smul_eq_mul] using!
    mul_nonneg
      (inv_nonneg.mpr (pow_nonneg (balancingScale_pos f).le d))
      (f.fourier_nonneg ((balancingScale f)⁻¹ • ξ))

private theorem balancedFunction_fourier_radial {d : ℕ} (f : Admissible d) :
    IsRadial (𝓕 (balancedFunction f) : TestFunction d) := by
  intro x y hxy
  let A : Euclidean d ≃ₗᵢ[ℝ] Euclidean d :=
    Submodule.reflection (ℝ ∙ (x - y))ᗮ
  have hA : A x = y := Submodule.reflection_sub hxy
  have hcomp :
      (balancedFunction f : Euclidean d → ℂ) ∘ A = balancedFunction f := by
    funext z
    exact balancedFunction_radial f (A z) z (A.norm_map z)
  change (𝓕 (balancedFunction f : Euclidean d → ℂ)) x =
    (𝓕 (balancedFunction f : Euclidean d → ℂ)) y
  calc
    (𝓕 (balancedFunction f : Euclidean d → ℂ)) x =
        (𝓕 ((balancedFunction f : Euclidean d → ℂ) ∘ A)) x := by
      rw [hcomp]
    _ = (𝓕 (balancedFunction f : Euclidean d → ℂ)) (A x) :=
      Real.fourier_comp_linearIsometry A
        (balancedFunction f : Euclidean d → ℂ) x
    _ = (𝓕 (balancedFunction f : Euclidean d → ℂ)) y := by rw [hA]

private theorem balancedFunction_fourier_zero {d : ℕ} (f : Admissible d)
    (hd : 0 < d) :
    ((𝓕 (balancedFunction f) : TestFunction d)
      (0 : Euclidean d)) = balancedFunction f 0 := by
  unfold balancedFunction
  rw [fourier_dilate_zero, balancingScale_pow f hd, dilate_zero]
  apply Complex.ext
  · rw [Complex.smul_re]
    change
      (((𝓕 f.function : TestFunction d) (0 : Euclidean d)).re /
        (f.function (0 : Euclidean d)).re)⁻¹ *
          ((𝓕 f.function : TestFunction d) (0 : Euclidean d)).re =
        (f.function (0 : Euclidean d)).re
    field_simp [f.fourier_zero_pos.ne', (admissible_zero_pos f).ne']
  · rw [Complex.smul_im]
    change
      (((𝓕 f.function : TestFunction d) (0 : Euclidean d)).re /
        (f.function (0 : Euclidean d)).re)⁻¹ *
          ((𝓕 f.function : TestFunction d) (0 : Euclidean d)).im =
        (f.function (0 : Euclidean d)).im
    rw [f.fourier_real, f.real]
    simp only [inv_div, mul_zero]

private theorem balancedFunction_outside_nonpos {d : ℕ} (f : Admissible d)
    (x : Euclidean d) (hx : (balancingScale f)⁻¹ ≤ ‖x‖) :
    (balancedFunction f x).re ≤ 0 := by
  apply f.outside_nonpos (balancingScale f • x)
  have h := mul_le_mul_of_nonneg_left hx (balancingScale_pos f).le
  rw [mul_inv_cancel₀ (balancingScale_pos f).ne'] at h
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (balancingScale_pos f), ge_iff_le] using! h

private noncomputable def balancedAntiFourierPart {d : ℕ} (f : Admissible d) : TestFunction d :=
  antiFourierPart (balancedFunction f)

private theorem fourier_balancedAntiFourierPart {d : ℕ} (f : Admissible d) :
    (𝓕 (balancedAntiFourierPart f) : TestFunction d) =
      -balancedAntiFourierPart f := by
  exact fourier_antiFourierPart (balancedFunction f)
    (balancedFunction_radial f)

private theorem balancedAntiFourierPart_zero {d : ℕ} (f : Admissible d)
    (hd : 0 < d) :
    balancedAntiFourierPart f (0 : Euclidean d) = 0 := by
  exact antiFourierPart_zero (balancedFunction f)
    (balancedFunction_fourier_zero f hd)

private theorem balancedAntiFourierPart_real {d : ℕ} (f : Admissible d) :
    IsRealValued (balancedAntiFourierPart f) := by
  intro x
  change (((𝓕 (balancedFunction f) : TestFunction d) x) -
    balancedFunction f x).im = 0
  rw [Complex.sub_im, balancedFunction_fourier_real f x,
    balancedFunction_real f x]
  norm_num

private theorem balancedAntiFourierPart_radial {d : ℕ} (f : Admissible d) :
    IsRadial (balancedAntiFourierPart f) := by
  intro x y hxy
  change
    ((𝓕 (balancedFunction f) : TestFunction d) x) -
        balancedFunction f x =
      ((𝓕 (balancedFunction f) : TestFunction d) y) -
        balancedFunction f y
  rw [balancedFunction_fourier_radial f x y hxy,
    balancedFunction_radial f x y hxy]

private theorem balancedAntiFourierPart_nonneg {d : ℕ} (f : Admissible d)
    (x : Euclidean d) (hx : (balancingScale f)⁻¹ ≤ ‖x‖) :
    0 ≤ (balancedAntiFourierPart f x).re := by
  exact antiFourierPart_nonneg_of_signs
    (balancedFunction f) ((balancingScale f)⁻¹)
    (balancedFunction_fourier_nonneg f)
    (balancedFunction_outside_nonpos f) x hx

private theorem balancedAntiFourierPart_eq_zero_iff {d : ℕ} (f : Admissible d) :
    balancedAntiFourierPart f = 0 ↔
      (𝓕 (balancedFunction f) : TestFunction d) = balancedFunction f := by
  change (𝓕 (balancedFunction f) : TestFunction d) -
    balancedFunction f = 0 ↔ _
  exact sub_eq_zero

private theorem balancedFunction_support_subset_of_anti_zero {d : ℕ}
    (f : Admissible d) (hzero : balancedAntiFourierPart f = 0) :
    Function.support (balancedFunction f : Euclidean d → ℂ) ⊆
      Metric.closedBall (0 : Euclidean d) (balancingScale f)⁻¹ := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hnot
  have hlarge : (balancingScale f)⁻¹ < ‖x‖ := lt_of_not_ge hnot
  have hself := (balancedAntiFourierPart_eq_zero_iff f).mp hzero
  have hnonneg : 0 ≤ (balancedFunction f x).re := by
    have hpoint :
        ((𝓕 (balancedFunction f) : TestFunction d) x) =
          balancedFunction f x :=
      congrArg (fun g : TestFunction d => g x) hself
    calc
      0 ≤ ((𝓕 (balancedFunction f) : TestFunction d) x).re :=
        balancedFunction_fourier_nonneg f x
      _ = (balancedFunction f x).re := congrArg Complex.re hpoint
  have hnonpos : (balancedFunction f x).re ≤ 0 :=
    balancedFunction_outside_nonpos f x hlarge.le
  have hre : (balancedFunction f x).re = 0 :=
    le_antisymm hnonpos hnonneg
  apply hx
  apply Complex.ext
  · simpa only [balancedFunction_apply, Complex.zero_re] using! hre
  · simpa only [balancedFunction_apply, Complex.zero_im] using! balancedFunction_real f x

private theorem balancedFunction_hasCompactSupport_of_anti_zero {d : ℕ}
    (f : Admissible d) (hzero : balancedAntiFourierPart f = 0) :
    HasCompactSupport (balancedFunction f : Euclidean d → ℂ) := by
  exact HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Euclidean d) (balancingScale f)⁻¹)
    (balancedFunction_support_subset_of_anti_zero f hzero)

private noncomputable def nonnegativeSchwartzDensity {d : ℕ} (g : TestFunction d)
    (hg : ∀ x : Euclidean d, 0 ≤ (g x).re) :
    Euclidean d → ℝ≥0 :=
  fun x => ⟨(g x).re, hg x⟩

private theorem nonnegativeSchwartzDensity_continuous {d : ℕ}
    (g : TestFunction d) (hg : ∀ x : Euclidean d, 0 ≤ (g x).re) :
    Continuous (nonnegativeSchwartzDensity g hg) := by
  exact (Complex.continuous_re.comp g.continuous).subtype_mk hg

private noncomputable def nonnegativeSchwartzMeasure {d : ℕ} (g : TestFunction d)
    (hg : ∀ x : Euclidean d, 0 ≤ (g x).re) :
    Measure (Euclidean d) :=
  (volume : Measure (Euclidean d)).withDensity
    (fun x => (nonnegativeSchwartzDensity g hg x : ℝ≥0∞))

private theorem integrableExpSet_nonnegativeSchwartzMeasure_eq_univ {d : ℕ}
    (g : TestFunction d) (hg : ∀ x : Euclidean d, 0 ≤ (g x).re)
    (hcompact : HasCompactSupport (g : Euclidean d → ℂ))
    (X : Euclidean d → ℝ) (hX : Continuous X) :
    ProbabilityTheory.integrableExpSet X
      (nonnegativeSchwartzMeasure g hg) = Set.univ := by
  ext t
  simp only [ProbabilityTheory.integrableExpSet, Set.mem_ofPred_eq,
    Set.mem_univ, iff_true]
  unfold nonnegativeSchwartzMeasure
  rw [integrable_withDensity_iff_integrable_smul
    (nonnegativeSchwartzDensity_continuous g hg).measurable]
  simp_rw [NNReal.smul_def, smul_eq_mul]
  have hrealcompact :
      HasCompactSupport (fun x : Euclidean d => (g x).re) := by
    change HasCompactSupport (Complex.re ∘
      (g : Euclidean d → ℂ))
    exact hcompact.comp_left (by simp only [Complex.zero_re])
  have hcontinuous :
      Continuous (fun x : Euclidean d =>
        (g x).re * Real.exp (t * X x)) := by
    exact (Complex.continuous_re.comp g.continuous).mul
      (Real.continuous_exp.comp (continuous_const.mul hX))
  exact hcontinuous.integrable_of_hasCompactSupport
    hrealcompact.mul_right

private theorem nonnegativeSchwartz_complexMGF_analytic {d : ℕ}
    (g : TestFunction d) (hg : ∀ x : Euclidean d, 0 ≤ (g x).re)
    (hcompact : HasCompactSupport (g : Euclidean d → ℂ))
    (X : Euclidean d → ℝ) (hX : Continuous X) :
    AnalyticOnNhd ℂ
      (ProbabilityTheory.complexMGF X
        (nonnegativeSchwartzMeasure g hg)) Set.univ := by
  have hset := integrableExpSet_nonnegativeSchwartzMeasure_eq_univ
    g hg hcompact X hX
  simpa only [hset, interior_univ, mem_univ, ofPred_true] using!
    (ProbabilityTheory.analyticOnNhd_complexMGF
      (X := X) (μ := nonnegativeSchwartzMeasure g hg))

private theorem nonnegativeSchwartz_complexMGF_mul_I {d : ℕ}
    (g : TestFunction d) (hreal : IsRealValued g)
    (hg : ∀ x : Euclidean d, 0 ≤ (g x).re)
    (e : Euclidean d) (t : ℝ) :
    ProbabilityTheory.complexMGF
        (fun x : Euclidean d =>
          -2 * Real.pi * @inner ℝ (Euclidean d) _ x e)
        (nonnegativeSchwartzMeasure g hg)
        ((t : ℂ) * Complex.I) =
      ((𝓕 g : TestFunction d) (t • e)) := by
  calc
    ProbabilityTheory.complexMGF
        (fun x : Euclidean d =>
          -2 * Real.pi * @inner ℝ (Euclidean d) _ x e)
        (nonnegativeSchwartzMeasure g hg)
        ((t : ℂ) * Complex.I) =
      ∫ x : Euclidean d,
        nonnegativeSchwartzDensity g hg x •
          Complex.exp
            (((t : ℂ) * Complex.I) *
              (↑(-2 * Real.pi *
                @inner ℝ (Euclidean d) _ x e) : ℂ)) := by
        unfold ProbabilityTheory.complexMGF nonnegativeSchwartzMeasure
        rw [integral_withDensity_eq_integral_smul
          (nonnegativeSchwartzDensity_continuous g hg).measurable]
    _ = (𝓕 (g : Euclidean d → ℂ)) (t • e) := by
      rw [Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards [] with x
      have hvalue : (↑((g x).re) : ℂ) = g x := by
        apply Complex.ext
        · simp only [Complex.ofReal_re]
        · simpa only [Complex.ofReal_im] using! (hreal x).symm
      have hexponent :
          ((t : ℂ) * Complex.I) *
              (↑(-2 * Real.pi *
                @inner ℝ (Euclidean d) _ x e) : ℂ) =
            (↑(-2 * Real.pi *
              @inner ℝ (Euclidean d) _ x (t • e)) : ℂ) *
                Complex.I := by
        rw [real_inner_smul_right]
        push_cast
        ring
      rw [NNReal.smul_def, Complex.real_smul, hexponent]
      change (↑((g x).re) : ℂ) * _ = _ * g x
      rw [hvalue, mul_comm]
    _ = ((𝓕 g : TestFunction d) (t • e)) :=
      (congrFun (SchwartzMap.fourier_coe g) (t • e)).symm

private theorem analytic_eq_zero_of_imaginary_ray
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F Set.univ)
    (T : ℝ)
    (hvanish : ∀ t : ℝ, T < t → F ((t : ℂ) * Complex.I) = 0) :
    F = 0 := by
  let t₀ : ℝ := T + 1
  let z₀ : ℂ := (t₀ : ℂ) * Complex.I
  have hclosure :
      z₀ ∈ closure ({z : ℂ | F z = 0} \ {z₀}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let u : ℝ := t₀ + ε / 2
    let z : ℂ := (u : ℂ) * Complex.I
    refine ⟨z, ⟨?_, ?_⟩, ?_⟩
    · apply hvanish u
      try dsimp [u, t₀]
      linarith
    · intro hz
      have hu : u = t₀ := by
        have him := congrArg Complex.im hz
        simpa [z, z₀] using! him
      try dsimp [u] at hu
      linarith
    · dsimp [z₀, z, u]
      rw [dist_eq_norm, ← sub_mul, ← Complex.ofReal_sub, norm_mul,
        Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
      rw [show t₀ - (t₀ + ε / 2) = -(ε / 2) by ring,
        abs_neg, abs_of_pos (half_pos hε)]
      exact half_lt_self hε
  have heq :=
    hF.eqOn_zero_of_preconnected_of_mem_closure
      isPreconnected_univ (Set.mem_univ z₀) hclosure
  funext z
  exact heq (Set.mem_univ z)

private theorem nonnegative_compact_fourier_fixed_eq_zero {d : ℕ}
    (hd : 0 < d) (g : TestFunction d)
    (hreal : IsRealValued g)
    (hg : ∀ x : Euclidean d, 0 ≤ (g x).re)
    (hcompact : HasCompactSupport (g : Euclidean d → ℂ))
    (hfixed : (𝓕 g : TestFunction d) = g) :
    g = 0 := by
  classical
  let : Nontrivial (Euclidean d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (M := Euclidean d)
      (by simpa only [finrank_euclideanSpace, Fintype.card_fin] using! hd)
  obtain ⟨e, he⟩ :=
    exists_norm_eq (Euclidean d) (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨R, hR⟩ :=
    hcompact.isBounded.subset_closedBall (0 : Euclidean d)
  let X : Euclidean d → ℝ :=
    fun x => -2 * Real.pi * @inner ℝ (Euclidean d) _ x e
  have hX : Continuous X := by
    try dsimp [X]
    fun_prop
  let μ : Measure (Euclidean d) := nonnegativeSchwartzMeasure g hg
  let F : ℂ → ℂ := ProbabilityTheory.complexMGF X μ
  have hanalytic : AnalyticOnNhd ℂ F Set.univ := by
    try dsimp [F, μ]
    exact nonnegativeSchwartz_complexMGF_analytic g hg hcompact X hX
  have hvanish :
      ∀ t : ℝ, max R 0 < t → F ((t : ℂ) * Complex.I) = 0 := by
    intro t ht
    change
      ProbabilityTheory.complexMGF
          (fun x : Euclidean d =>
            -2 * Real.pi * @inner ℝ (Euclidean d) _ x e)
          (nonnegativeSchwartzMeasure g hg)
          ((t : ℂ) * Complex.I) = 0
    rw [nonnegativeSchwartz_complexMGF_mul_I g hreal hg e t,
      hfixed]
    by_contra hnonzero
    have hsupp :
        t • e ∈ Function.support (g : Euclidean d → ℂ) := by
      exact hnonzero
    have hbound : ‖t • e‖ ≤ R := by
      have hball := hR
        (subset_tsupport (g : Euclidean d → ℂ) hsupp)
      simpa only [Metric.mem_closedBall, dist_zero_right] using! hball
    have htpos : 0 < t := (le_max_right R 0).trans_lt ht
    have hnorm : ‖t • e‖ = t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, he, mul_one]
    rw [hnorm] at hbound
    exact (not_le_of_gt ((le_max_left R 0).trans_lt ht)) hbound
  have hFzero : F = 0 :=
    analytic_eq_zero_of_imaginary_ray F hanalytic (max R 0) hvanish
  have hFzero_at_zero : F 0 = 0 := by
    simpa only [Pi.zero_apply] using! congrFun hFzero (0 : ℂ)
  have hfourierzero :
      ((𝓕 g : TestFunction d) (0 : Euclidean d)) = 0 := by
    have hmomentzero :
        ProbabilityTheory.complexMGF
          (fun x : Euclidean d =>
            -2 * Real.pi * @inner ℝ (Euclidean d) _ x e)
          (nonnegativeSchwartzMeasure g hg) 0 = 0 := by
      exact hFzero_at_zero
    calc
      ((𝓕 g : TestFunction d) (0 : Euclidean d)) =
          ProbabilityTheory.complexMGF
            (fun x : Euclidean d =>
              -2 * Real.pi * @inner ℝ (Euclidean d) _ x e)
            (nonnegativeSchwartzMeasure g hg)
            ((0 : ℂ) * Complex.I) := by
        simpa only [neg_mul, zero_mul, zero_smul, Complex.ofReal_zero] using!
          (nonnegativeSchwartz_complexMGF_mul_I g hreal hg e 0).symm
      _ = 0 := by simpa only [neg_mul, zero_mul] using! hmomentzero
  have hfourier_integral :
      ((𝓕 g : TestFunction d) (0 : Euclidean d)) =
        ∫ x : Euclidean d, g x := by
    change (𝓕 (g : Euclidean d → ℂ)) 0 = _
    rw [Real.fourier_eq']
    simp only [neg_mul, inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, smul_eq_mul,
      one_mul]
  have hintegral :
      (∫ x : Euclidean d, (g x).re) = 0 := by
    calc
      (∫ x : Euclidean d, (g x).re) =
          (∫ x : Euclidean d, g x).re :=
        integral_re g.integrable
      _ = ((𝓕 g : TestFunction d) (0 : Euclidean d)).re := by
        rw [hfourier_integral]
      _ = 0 := by rw [hfourierzero]; rfl
  by_contra hnonzero
  have hreal_nonzero :
      (fun x : Euclidean d => (g x).re) ≠ 0 := by
    intro hzero
    apply hnonzero
    ext x
    apply Complex.ext
    · simpa only [zero_apply, Complex.zero_re, Pi.zero_apply] using! congrFun hzero x
    · simpa only [zero_apply, Complex.zero_im] using! hreal x
  obtain ⟨x, hx⟩ :
      ∃ x : Euclidean d, (g x).re ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hreal_nonzero
    funext x
    simpa only [Pi.zero_apply] using! hnone x
  have hpositive :
      0 < ∫ x : Euclidean d, (g x).re :=
    integral_pos_of_integrable_nonneg_nonzero
      (Complex.continuous_re.comp g.continuous)
      g.integrable.re hg hx
  exact (ne_of_gt hpositive) hintegral

private theorem balancedAntiFourierPart_ne_zero {d : ℕ}
    (f : Admissible d) (hd : 0 < d) :
    balancedAntiFourierPart f ≠ 0 := by
  intro hzero
  have hself := (balancedAntiFourierPart_eq_zero_iff f).mp hzero
  have hcompact := balancedFunction_hasCompactSupport_of_anti_zero f hzero
  have hnonneg :
      ∀ x : Euclidean d, 0 ≤ (balancedFunction f x).re := by
    intro x
    rw [← hself]
    exact balancedFunction_fourier_nonneg f x
  have hvanish :=
    nonnegative_compact_fourier_fixed_eq_zero hd
      (balancedFunction f) (balancedFunction_real f)
      hnonneg hcompact hself
  have horigin := congrArg
    (fun g : TestFunction d => (g (0 : Euclidean d)).re) hvanish
  have hpos : 0 < (balancedFunction f (0 : Euclidean d)).re := by
    simpa only [balancedFunction_apply, smul_zero] using! admissible_zero_pos f
  simpa only  using! hpos.ne' horigin

private noncomputable def AntiFourierWitness.monoRadius {d : ℕ} {R S : ℝ}
    (w : AntiFourierWitness d R) (hRS : R ≤ S) :
    AntiFourierWitness d S where
  function := w.function
  real := w.real
  radial := w.radial
  nonzero := w.nonzero
  anti_fourier := w.anti_fourier
  zero_value := w.zero_value
  eventually_nonneg := fun x hx =>
    w.eventually_nonneg x (hRS.trans hx)

private noncomputable def balancedAntiFourierWitness {d : ℕ} (f : Admissible d)
    (hd : 0 < d) :
    AntiFourierWitness d (balancingScale f)⁻¹ where
  function := balancedAntiFourierPart f
  real := balancedAntiFourierPart_real f
  radial := balancedAntiFourierPart_radial f
  nonzero := balancedAntiFourierPart_ne_zero f hd
  anti_fourier := fourier_balancedAntiFourierPart f
  zero_value := balancedAntiFourierPart_zero f hd
  eventually_nonneg := balancedAntiFourierPart_nonneg f

end

section

open MeasureTheory Metric
open scoped ENNReal

end

section

open Filter MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal

private noncomputable def radialUnitDirection {d : ℕ} (hd : 0 < d) : Euclidean d :=
  (EuclideanSpace.basisFun (Fin d) ℝ) ⟨0, hd⟩

private theorem norm_radialUnitDirection {d : ℕ} (hd : 0 < d) :
    ‖radialUnitDirection hd‖ = 1 := by
  unfold radialUnitDirection
  exact (EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one _

private noncomputable def radialProfile {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (r : ℝ) : ℂ :=
  f (r • radialUnitDirection hd)

@[simp] private theorem radialProfile_zero {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) :
    radialProfile hd f 0 = f (0 : Euclidean d) := by
  simp only [radialProfile, zero_smul]

private noncomputable def radialSurfaceArea (d : ℕ) : ℝ :=
  (d : ℝ) * unitBallVolume d

private noncomputable def radialMellinFrequency {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (t : ℝ) : ℂ :=
  mellinFrequency ((d : ℝ) / 2) (radialProfile hd f) t

end

section

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology RealInnerProductSpace

private noncomputable def gaussianMellinWeight (d : ℕ) (a : ℝ) (x : Euclidean d) : ℂ :=
  Complex.exp (-((a : ℂ) * (‖x‖ : ℂ) ^ 2))

private noncomputable def gaussianMellinMixture {d : ℕ}
    (f : TestFunction d) (b : ℂ)
    (x : Euclidean d) (a : ℝ) : ℂ :=
  f x *
    ((a : ℂ) ^ (b - 1) *
      Complex.exp (-((‖x‖ : ℂ) ^ 2 * (a : ℂ))))

private noncomputable def gaussianMellinPairingProfile {d : ℕ}
    (f : TestFunction d) (a : ℝ) : ℂ :=
  ∫ x : Euclidean d, f x * gaussianMellinWeight d a x

end

section

open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology

private noncomputable def shellOscillation (B T : ℝ) : ℝ :=
  ∫ a in B..B + 1, (1 - Real.cos (a * T))

private noncomputable def positiveShellDensity (ε a : ℝ) : ℝ :=
  shellWeight ε / Real.cosh a

private noncomputable def positiveShellDamping (ε ℓ δ T : ℝ) : ℝ :=
  ℓ * ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    positiveShellDensity ε a * Real.cosh ((1 + δ) * a) *
      (1 - Real.cos (a * T))

private noncomputable def positiveShellRadiusContribution (ε : ℝ) : ℝ :=
  ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    positiveShellDensity ε a * a *
      Real.sinh ((1 + ε / 4) * a)

private noncomputable def shortShellDensity (ε a : ℝ) : ℝ :=
  -((1 - 10 * ε * (1 + a)) * Real.exp (-2 * a) /
    (2 * a ^ 2 * Real.cosh a))

private noncomputable def mellinShellPhase (ε : ℝ) (z : ℂ) : ℂ :=
  (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    (shortShellDensity ε a : ℂ) *
      (Complex.cos ((a : ℂ) * z) - 1)) +
  (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    (positiveShellDensity ε a : ℂ) *
      (Complex.cos ((a : ℂ) * z) - 1))

private noncomputable def realOscillatoryShellPhase (ε t : ℝ) : ℝ :=
  (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    shortShellDensity ε a * (Real.cos (a * t) - 1)) +
  (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    positiveShellDensity ε a * (Real.cos (a * t) - 1))

private noncomputable def realHyperbolicShellPhase (ε u : ℝ) : ℝ :=
  (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    shortShellDensity ε a * (Real.cosh (a * u) - 1)) +
  (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    positiveShellDensity ε a * (Real.cosh (a * u) - 1))

private noncomputable def saddleShellTotalVariation (ε : ℝ) : ℝ :=
  (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    |shortShellDensity ε a|) +
  (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    |positiveShellDensity ε a|)

private noncomputable def saddleEnvelope (ε ℓ t : ℝ) : ℂ :=
  Complex.exp
      (Complex.I * (t : ℂ) * (Real.log Real.pi : ℂ) / 2) *
    Complex.Gamma (((ℓ : ℂ) - Complex.I * (t : ℂ)) / 2) *
    Complex.exp ((ℓ : ℂ) *
      mellinShellPhase ε ((t : ℂ) / (ℓ : ℂ)))

private noncomputable def plusSaddleSpectrum (ε ℓ t : ℝ) : ℂ :=
  saddleEnvelope ε ℓ t *
    plusPolynomial ε ((t : ℂ) / (ℓ : ℂ))

private noncomputable def minusSaddleSpectrum (ε ℓ t : ℝ) : ℂ :=
  saddleEnvelope ε ℓ t *
    minusPolynomial ε ((t : ℂ) / (ℓ : ℂ))

private noncomputable def saddleOriginValue (ε ℓ : ℝ) : ℝ :=
  2 * Real.pi ^ (ℓ / 2) *
    Real.exp (ℓ * realHyperbolicShellPhase ε 1) * (ε / 4)

private noncomputable def saddleMellinEnvelope (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp
      (((ℓ : ℂ) - z) * (Real.log Real.pi : ℂ) / 2) *
    Complex.Gamma (z / 2) *
    Complex.exp ((ℓ : ℂ) *
      mellinShellPhase ε
        (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)))

private noncomputable def plusSaddleMellinData (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  saddleMellinEnvelope ε ℓ z *
    plusPolynomial ε
      (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ))

private noncomputable def minusSaddleMellinData (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  saddleMellinEnvelope ε ℓ z *
    minusPolynomial ε
      (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ))

private noncomputable def saddleRegularMellinFactor (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp
      (((ℓ : ℂ) - z) * (Real.log Real.pi : ℂ) / 2) *
    Complex.exp ((ℓ : ℂ) *
      mellinShellPhase ε
        (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)))

private noncomputable def plusSaddleRegularMellinFactor (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  saddleRegularMellinFactor ε ℓ z *
    plusPolynomial ε
      (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ))

private noncomputable def minusSaddleRegularMellinFactor (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  saddleRegularMellinFactor ε ℓ z *
    minusPolynomial ε
      (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ))

private noncomputable def saddlePoleStrip (n : ℕ) : Set ℂ :=
  {z : ℂ |
    -(2 * ((n : ℝ) + 1)) < z.re ∧
      z.re < -(2 * (n : ℝ)) + 1}

private noncomputable def saddlePoleLowerProduct (n : ℕ) (z : ℂ) : ℂ :=
  ∏ j ∈ Finset.range n, (z / 2 + (j : ℂ))

private noncomputable def saddleNthGammaPoleNumerator (n : ℕ) (z : ℂ) : ℂ :=
  (2 : ℂ) *
    Complex.Gamma (z / 2 + ((n + 1 : ℕ) : ℂ)) /
      saddlePoleLowerProduct n z

private noncomputable def plusSaddleNthPoleNumerator
    (ε ℓ : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  saddleNthGammaPoleNumerator n z *
    plusSaddleRegularMellinFactor ε ℓ z

private noncomputable def minusSaddleNthPoleNumerator
    (ε ℓ : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  saddleNthGammaPoleNumerator n z *
    minusSaddleRegularMellinFactor ε ℓ z

private noncomputable def plusSaddlePoleResidue (ε ℓ : ℝ) (n : ℕ) : ℂ :=
  (2 : ℂ) * (-1 : ℂ) ^ n / (n.factorial : ℂ) *
    plusSaddleRegularMellinFactor ε ℓ
      (-((2 * n : ℕ) : ℂ))

private noncomputable def minusSaddlePoleResidue (ε ℓ : ℝ) (n : ℕ) : ℂ :=
  (2 : ℂ) * (-1 : ℂ) ^ n / (n.factorial : ℂ) *
    minusSaddleRegularMellinFactor ε ℓ
      (-((2 * n : ℕ) : ℂ))

private noncomputable def plusSaddleNthPoleRegularPart
    (ε ℓ : ℝ) (n : ℕ) : ℂ → ℂ :=
  dslope (plusSaddleNthPoleNumerator ε ℓ n)
    (-((2 * n : ℕ) : ℂ))

private noncomputable def minusSaddleNthPoleRegularPart
    (ε ℓ : ℝ) (n : ℕ) : ℂ → ℂ :=
  dslope (minusSaddleNthPoleNumerator ε ℓ n)
    (-((2 * n : ℕ) : ℂ))

private noncomputable def saddleFinitePoleHalfPlane (N : ℕ) : Set ℂ :=
  {z : ℂ | -(2 * ((N : ℝ) + 1)) < z.re}

private noncomputable def plusSaddleFinitePoleSubtraction
    (ε ℓ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  plusSaddleMellinData ε ℓ z -
    ∑ n ∈ Finset.range (N + 1),
      plusSaddlePoleResidue ε ℓ n /
        (z + ((2 * n : ℕ) : ℂ))

private noncomputable def minusSaddleFinitePoleSubtraction
    (ε ℓ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  minusSaddleMellinData ε ℓ z -
    ∑ n ∈ Finset.range (N + 1),
      minusSaddlePoleResidue ε ℓ n /
        (z + ((2 * n : ℕ) : ℂ))

private noncomputable def plusSaddleFinitePoleRegularPart
    (ε ℓ : ℝ) (N : ℕ) : ℂ → ℂ :=
  toMeromorphicNFOn
    (plusSaddleFinitePoleSubtraction ε ℓ N)
      (saddleFinitePoleHalfPlane N)

private noncomputable def minusSaddleFinitePoleRegularPart
    (ε ℓ : ℝ) (N : ℕ) : ℂ → ℂ :=
  toMeromorphicNFOn
    (minusSaddleFinitePoleSubtraction ε ℓ N)
      (saddleFinitePoleHalfPlane N)

private noncomputable def plusSaddleFinitePoleRemaining
    (ε ℓ : ℝ) (N n : ℕ) (z : ℂ) : ℂ :=
  ∑ m ∈ (Finset.range (N + 1)).erase n,
    plusSaddlePoleResidue ε ℓ m /
      (z + ((2 * m : ℕ) : ℂ))

private noncomputable def minusSaddleFinitePoleRemaining
    (ε ℓ : ℝ) (N n : ℕ) (z : ℂ) : ℂ :=
  ∑ m ∈ (Finset.range (N + 1)).erase n,
    minusSaddlePoleResidue ε ℓ m /
      (z + ((2 * m : ℕ) : ℂ))

private noncomputable def saddleMellinInversePower (r : ℝ) (z : ℂ) : ℂ :=
  (r : ℂ) ^ (-z)

private noncomputable def saddleGaussianPoleSlope (z : ℂ) : ℂ :=
  dslope (fun w : ℂ => Complex.exp (w ^ 2)) 0 z

private noncomputable def saddleGaussianPoleRepresentative
    (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp ((z + ((2 * n : ℕ) : ℂ)) ^ 2) /
    (z + ((2 * n : ℕ) : ℂ))

private noncomputable def plusSaddleFiniteRapidPoleSubtraction
    (ε ℓ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  plusSaddleMellinData ε ℓ z -
    ∑ n ∈ Finset.range (N + 1),
      plusSaddlePoleResidue ε ℓ n *
        saddleGaussianPoleRepresentative n z

private noncomputable def minusSaddleFiniteRapidPoleSubtraction
    (ε ℓ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  minusSaddleMellinData ε ℓ z -
    ∑ n ∈ Finset.range (N + 1),
      minusSaddlePoleResidue ε ℓ n *
        saddleGaussianPoleRepresentative n z

private noncomputable def plusSaddleFiniteRapidPoleRegularPart
    (ε ℓ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  plusSaddleFinitePoleRegularPart ε ℓ N z -
    ∑ n ∈ Finset.range (N + 1),
      plusSaddlePoleResidue ε ℓ n *
        saddleGaussianPoleSlope
          (z + ((2 * n : ℕ) : ℂ))

private noncomputable def minusSaddleFiniteRapidPoleRegularPart
    (ε ℓ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  minusSaddleFinitePoleRegularPart ε ℓ N z -
    ∑ n ∈ Finset.range (N + 1),
      minusSaddlePoleResidue ε ℓ n *
        saddleGaussianPoleSlope
          (z + ((2 * n : ℕ) : ℂ))

private noncomputable def plusSaddleFiniteRapidContourIntegrand
    (ε ℓ : ℝ) (N : ℕ) (r : ℝ) (z : ℂ) : ℂ :=
  saddleMellinInversePower r z *
    plusSaddleFiniteRapidPoleRegularPart ε ℓ N z

private noncomputable def minusSaddleFiniteRapidContourIntegrand
    (ε ℓ : ℝ) (N : ℕ) (r : ℝ) (z : ℂ) : ℂ :=
  saddleMellinInversePower r z *
    minusSaddleFiniteRapidPoleRegularPart ε ℓ N z

private noncomputable def plusSaddleProfile (ε ℓ r : ℝ) : ℂ :=
  if r = 0 then (saddleOriginValue ε ℓ : ℂ)
  else mellinInv ℓ (plusSaddleMellinData ε ℓ) r

private noncomputable def minusSaddleProfile (ε ℓ r : ℝ) : ℂ :=
  if r = 0 then (saddleOriginValue ε ℓ : ℂ)
  else mellinInv ℓ (minusSaddleMellinData ε ℓ) r

private noncomputable def plusSaddleFunction (ε : ℝ) (d : ℕ) (x : Euclidean d) : ℂ :=
  plusSaddleProfile ε ((d : ℝ) / 2) ‖x‖

private noncomputable def minusSaddleFunction (ε : ℝ) (d : ℕ) (x : Euclidean d) : ℂ :=
  minusSaddleProfile ε ((d : ℝ) / 2) ‖x‖

@[simp] private theorem plusSaddleFunction_zero (ε : ℝ) (d : ℕ) :
    plusSaddleFunction ε d (0 : Euclidean d) =
      (saddleOriginValue ε ((d : ℝ) / 2) : ℂ) := by
  simp only [plusSaddleFunction, plusSaddleProfile, norm_zero, ↓reduceIte]

@[simp] private theorem minusSaddleFunction_zero (ε : ℝ) (d : ℕ) :
    minusSaddleFunction ε d (0 : Euclidean d) =
      (saddleOriginValue ε ((d : ℝ) / 2) : ℂ) := by
  simp only [minusSaddleFunction, minusSaddleProfile, norm_zero, ↓reduceIte]

private noncomputable def saddleHorizontalShellVariation (ε H : ℝ) : ℝ :=
  (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    |shortShellDensity ε a| * (Real.cosh (a * H) + 1)) +
  (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    |positiveShellDensity ε a| * (Real.cosh (a * H) + 1))

private noncomputable def saddleShiftedLineMajorant
    (ε ℓ a : ℝ) (k m : ℕ) : ℝ :=
  ((1 + |(ε / 4)|) *
      (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3) *
    ((2 : ℝ) ^ (k + (m + 3)) *
      Real.Gamma
        (a / 2 + ((k + (m + 3) : ℕ) : ℝ))) *
    Real.exp ((ℓ - a) * Real.log Real.pi / 2) *
    Real.exp
      (ℓ * saddleHorizontalShellVariation ε
        |(a - ℓ) / ℓ|)

private noncomputable def saddleHorizontalStripHeight (ℓ A B : ℝ) : ℝ :=
  max |(A - ℓ) / ℓ| |(B - ℓ) / ℓ|

private noncomputable def saddleFixedStripMajorant
    (ε ℓ H a : ℝ) (k m : ℕ) : ℝ :=
  ((1 + |(ε / 4)|) *
      (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3) *
    ((2 : ℝ) ^ (k + (m + 3)) *
      Real.Gamma
        (a / 2 + ((k + (m + 3) : ℕ) : ℝ))) *
    Real.exp ((ℓ - a) * Real.log Real.pi / 2) *
    Real.exp
      (ℓ * saddleHorizontalShellVariation ε H)

private noncomputable def saddleCauchyPolePrimitive (a t : ℝ) : ℂ :=
  (Real.arctan (t / a) : ℂ) -
    ((Real.log (a ^ 2 + t ^ 2) / 2 : ℝ) : ℂ) *
      Complex.I

private noncomputable def plusSaddleFourierData (ε ℓ y : ℝ) : ℂ :=
  plusSaddleSpectrum ε ℓ (-(2 * Real.pi * y))

private noncomputable def minusSaddleFourierData (ε ℓ y : ℝ) : ℂ :=
  minusSaddleSpectrum ε ℓ (-(2 * Real.pi * y))

end
end CohnElkies
