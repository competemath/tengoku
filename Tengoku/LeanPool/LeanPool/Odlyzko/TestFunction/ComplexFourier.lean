/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.Odlyzko.TestFunction.Basic
import Tengoku.LeanPool.LeanPool.Odlyzko.TestFunction.Amplitude
import Tengoku.LeanPool.LeanPool.Odlyzko.TestFunction.Bounds
import Tengoku.LeanPool.LeanPool.Odlyzko.TestFunction.Fourier

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

section

open MeasureTheory

namespace NumberField.Odlyzko

/-- A cosine transform used in the Odlyzko-bound argument. -/
def Poitou.cosineTransform (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, f x * Real.cos (t * x)

/-- Conditions on a test function used in Poitou's explicit formula. -/
structure Poitou.Admissible (f : ℝ → ℝ) : Prop where
  continuous : Continuous f
  even : ∀ x, f (-x) = f x
  value_zero : f 0 = 1
  nonnegative : ∀ x, 0 ≤ f x
  integrable : Integrable f
  cosineTransform_nonnegative : ∀ t, 0 ≤ Poitou.cosineTransform f t

end NumberField.Odlyzko

end

section

open Filter
open scoped Topology

namespace NumberField.Odlyzko

/--
@isnad1 id=tendsto.0h0v.s6.49457444de57 from=translated src=- shape=28ae9a25 vocab=de07e499
-/
theorem tendsto_sin_sub_mul_cos_div_pow_three :
    Tendsto (fun x : ℝ ↦ (Real.sin x - x * Real.cos x) / x ^ 3)
      (𝓝[≠] 0) (𝓝 (1 / 3 : ℝ)) := by
  apply HasDerivAt.lhopital_zero_nhdsNE
      (f' := fun x : ℝ ↦ Real.sin x * x) (g' := fun x : ℝ ↦ 3 * x ^ 2)
  · filter_upwards with x
    exact ((Real.hasDerivAt_sin x).sub
      ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x))).congr_deriv (by
        grind)
  · filter_upwards with x
    exact (hasDerivAt_pow 3 x).congr_deriv (by norm_num)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simp_all
  · apply tendsto_nhdsWithin_of_tendsto_nhds
    change Tendsto (Real.sin - id * Real.cos) (𝓝 0) (𝓝 0)
    -- Stated at the Pi-algebra type so `tendsto` lands there; at v4.32 `simpa`
    -- no longer bridges the pointwise spelling on its own.
    have h : Continuous (Real.sin - id * Real.cos) :=
      Real.continuous_sin.sub (continuous_id.mul Real.continuous_cos)
    simpa using h.tendsto 0
  · apply tendsto_nhdsWithin_of_tendsto_nhds
    have h : Continuous (fun x : ℝ ↦ x ^ 3) := by fun_prop
    simpa using h.tendsto 0
  · have hsinc : Tendsto Real.sinc (𝓝[≠] 0) (𝓝 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by
        simpa using Real.continuous_sinc.tendsto 0)
    have h : Tendsto (fun x : ℝ ↦ Real.sin x * x / (3 * x ^ 2))
        (𝓝[≠] 0) (𝓝 (1 / 3)) := (hsinc.div_const 3).congr' (by
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [Real.sinc_of_ne_zero hx]
      grind)
    simp_all

/--
@isnad1 id=tendsto.0h0v.s5.8d410042d63a from=translated src=- shape=2b280528 vocab=c90dc0a4
-/
theorem tendsto_tartarAmplitude_punctured_zero :
    Tendsto Tartar.amplitude (𝓝[≠] 0) (𝓝 1) := by
  convert (tendsto_sin_sub_mul_cos_div_pow_three.const_mul 3).congr' ?_ using 1
  · norm_num
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [tartarAmplitude_eq_of_ne hx]
  ring

/--
@isnad1 id=continuo.0h0v.s4.99e1410f9545 from=translated src=- shape=5446e38f vocab=c4f8d332
-/
theorem tartarAmplitude_continuousAt_zero :
    ContinuousAt Tartar.amplitude 0 := by
  rw [continuousAt_iff_punctured_nhds, tartarAmplitude_zero]
  exact tendsto_tartarAmplitude_punctured_zero

/--
@isnad1 id=continuo.0h0v.s3.a294a4f4973f from=translated src=- shape=e3d48bcb vocab=f8c5614b
-/
@[fun_prop]
theorem tartarAmplitude_continuous : Continuous Tartar.amplitude := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · simpa [hx] using tartarAmplitude_continuousAt_zero
  · exact tartarAmplitude_continuousAt_of_ne hx

/--
@isnad1 id=continuo.0h0v.s3.9995aa52296a from=translated src=- shape=e3d48bcb vocab=5b200433
-/
@[fun_prop]
theorem tartarTestFunction_continuous : Continuous Tartar.testFunction := by
  unfold Tartar.testFunction
  fun_prop

end NumberField.Odlyzko

end

section

open MeasureTheory
open scoped ComplexConjugate Convolution FourierTransform RealInnerProductSpace

namespace NumberField.Odlyzko

/-- A complex tartar weight used in the Odlyzko-bound argument. -/
noncomputable def complexTartarWeight (x : ℝ) : ℂ :=
  Tartar.weight x

/--
@isnad1 id=integrab.0h0v.s5.592be11e469a from=translated src=- shape=c57f8401 vocab=44fda468
-/
theorem complexTartarWeight_integrable : Integrable complexTartarWeight := by
  exact tartarWeight_integrable.ofReal

/--
@isnad1 id=eq.0h1v.s5.4e04ce71cc31 from=translated src=- shape=6f09202f vocab=da5146ae
-/
theorem integral_tartarWeight_mul_sin (a : ℝ) :
    ∫ x : ℝ, Tartar.weight x * Real.sin (a * x) = 0 := by
  let f : ℝ → ℝ := fun x ↦ Tartar.weight x * Real.sin (a * x)
  have hodd (x : ℝ) : f (-x) = -f x := by
    simp [f, tartarWeight_neg]
  have h :
      (∫ x : ℝ, f x) = -(∫ x : ℝ, f x) := by
    calc
      (∫ x : ℝ, f x) = ∫ x : ℝ, f (-x) :=
        (integral_neg_eq_self f (volume : Measure ℝ)).symm
      _ = ∫ x : ℝ, -f x := by simp_all
      _ = -(∫ x : ℝ, f x) := integral_neg f
  grind

/--
@isnad1 id=eq.0h1v.s6.49c6d1eafcf0 from=translated src=- shape=47b5a340 vocab=9b5656ee
-/
theorem fourier_complexTartarWeight (ξ : ℝ) :
    𝓕 complexTartarWeight ξ =
      ((4 / 3 : ℝ) * Tartar.amplitude (2 * Real.pi * ξ) : ℂ) := by
  rw [tartarAmplitude_eq_cosineTransform]
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hint :
      Integrable (fun v : ℝ ↦
        Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) • complexTartarWeight v) := by
    constructor
    · exact (by fun_prop : Continuous (fun v : ℝ ↦
        Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I))).aestronglyMeasurable.smul
          complexTartarWeight_integrable.aestronglyMeasurable
    · apply complexTartarWeight_integrable.2.congr'
      filter_upwards [] with v
      rw [norm_smul, Complex.norm_exp]
      simp [Complex.mul_re]
  apply Complex.ext
  · rw [← RCLike.re_eq_complex_re, ← integral_re]
    · simp only [RCLike.re_eq_complex_re, smul_eq_mul, Complex.exp_mul_I,
        complexTartarWeight, Complex.mul_re,
        Complex.add_re, Complex.cos_ofReal_re,
        Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one, sub_zero,
        ]
      ring_nf
      apply integral_congr_ae
      filter_upwards [] with x
      rw [mul_comm]
      ring_nf
      simp
    · simp_all
  · rw [← RCLike.im_eq_complex_im, ← integral_im]
    · simp only [RCLike.im_eq_complex_im, smul_eq_mul, Complex.exp_mul_I,
        complexTartarWeight, Complex.mul_im,
        Complex.add_im, Complex.cos_ofReal_im,
        Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one, add_zero,
        ]
      simp only [zero_add, zero_mul]
      calc
        (∫ x : ℝ, Real.sin (-2 * Real.pi * x * ξ) * Tartar.weight x)
            = -(∫ x : ℝ, Tartar.weight x * Real.sin ((2 * Real.pi * ξ) * x)) := by
              rw [← integral_neg]
              apply integral_congr_ae
              filter_upwards [] with x
              rw [show -2 * Real.pi * x * ξ = -(2 * Real.pi * ξ * x) by ring,
                Real.sin_neg]
              ring
        _ = 0 := by rw [integral_tartarWeight_mul_sin, neg_zero]
    · simp_all

/-- A tartar weight convolution used in the Odlyzko-bound argument. -/
noncomputable def tartarWeightConvolution (x : ℝ) : ℝ :=
  ∫ t : ℝ, Tartar.weight t * Tartar.weight (x - t)

/--
@isnad1 id=le.0h1v.s3.cd617b945bb9 from=translated src=- shape=8a62b088 vocab=e63c0fd6
-/
theorem tartarWeightConvolution_nonneg (x : ℝ) :
    0 ≤ tartarWeightConvolution x := by
  apply integral_nonneg
  intro t
  exact mul_nonneg (tartarWeight_nonneg t) (tartarWeight_nonneg (x - t))

/--
@isnad1 id=eq.0h1v.s6.bb52b22d9b96 from=translated src=- shape=aee1ae8c vocab=50b42aff
-/
theorem complexTartarWeight_convolution_eq (x : ℝ) :
    (complexTartarWeight ⋆[ContinuousLinearMap.mul ℂ ℂ] complexTartarWeight) x =
      tartarWeightConvolution x := by
  rw [MeasureTheory.convolution, tartarWeightConvolution, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [] with t
  simp [complexTartarWeight]

/--
@isnad1 id=integrab.0h0v.s6.195a74f2cc2d from=translated src=- shape=5e57f4d4 vocab=edf87af8
-/
theorem complexTartarWeight_convolution_integrable :
    Integrable (complexTartarWeight ⋆[ContinuousLinearMap.mul ℂ ℂ] complexTartarWeight) :=
  complexTartarWeight_integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
    complexTartarWeight_integrable

/--
@isnad1 id=continuo.0h0v.s6.d920da8198f4 from=translated src=- shape=9a037d99 vocab=a2eba745
-/
theorem complexTartarWeight_convolution_continuous :
    Continuous (complexTartarWeight ⋆[ContinuousLinearMap.mul ℂ ℂ] complexTartarWeight) := by
  have hc : HasCompactSupport complexTartarWeight := by
    change HasCompactSupport (Complex.ofRealCLM ∘ Tartar.weight)
    exact tartarWeight_hasCompactSupport.comp_left rfl
  apply hc.continuous_convolution_right
    (ContinuousLinearMap.mul ℂ ℂ)
    complexTartarWeight_integrable.locallyIntegrable
  exact RCLike.continuous_ofReal.comp tartarWeight_continuous

/--
@isnad1 id=eq.0h1v.s7.809e03d982f0 from=translated src=- shape=e9dbc340 vocab=8e3f9b98
-/
theorem fourier_complexTartarWeight_convolution (ξ : ℝ) :
    𝓕 (complexTartarWeight ⋆[ContinuousLinearMap.mul ℂ ℂ] complexTartarWeight) ξ =
      ((16 / 9 : ℝ) * Tartar.testFunction (2 * Real.pi * ξ) : ℂ) := by
  -- v4.32's `fourier_mul_convolution_eq` also asks for continuity of both
  -- factors; v4.33 dropped those hypotheses.
  rw [Real.fourier_mul_convolution_eq complexTartarWeight_integrable
    complexTartarWeight_integrable ξ,
    fourier_complexTartarWeight]
  simp only [Tartar.testFunction, Complex.ofReal_pow]
  push_cast
  ring

/--
@isnad1 id=integrab.0h0v.s7.92ed1ce158fe from=translated src=- shape=c936fae7 vocab=40a2a7a3
-/
theorem fourier_complexTartarWeight_convolution_integrable :
    Integrable (𝓕
      (complexTartarWeight ⋆[ContinuousLinearMap.mul ℂ ℂ] complexTartarWeight)) := by
  have hscale :
      Integrable (fun ξ : ℝ ↦ Tartar.testFunction (2 * Real.pi * ξ)) :=
    tartarTestFunction_integrable.comp_mul_left'
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hcomplex := hscale.ofReal.const_mul ((16 / 9 : ℝ) : ℂ)
  apply hcomplex.congr
  filter_upwards [] with ξ
  rw [fourier_complexTartarWeight_convolution]
  simp

/--
@isnad1 id=eq.0h0v.s7.4a4f4c0d693f from=translated src=- shape=9536559c vocab=9b66cc8d
-/
theorem fourierInv_fourier_complexTartarWeight_convolution :
    𝓕⁻ (𝓕 (complexTartarWeight ⋆[ContinuousLinearMap.mul ℂ ℂ] complexTartarWeight)) =
      (complexTartarWeight ⋆[ContinuousLinearMap.mul ℂ ℂ] complexTartarWeight) :=
  complexTartarWeight_convolution_continuous.fourierInv_fourier_eq
    complexTartarWeight_convolution_integrable
    fourier_complexTartarWeight_convolution_integrable

/--
@isnad1 id=eq.0h0v.s6.453c10e26826 from=translated src=- shape=8fab9821 vocab=21c023e3
-/
theorem integral_tartarWeight_sq :
    ∫ x : ℝ, Tartar.weight x ^ 2 = 16 / 15 := by
  rw [tartarWeight_eq_indicator]
  have hind :
      (fun x : ℝ ↦ ((Set.Icc (-1 : ℝ) 1).indicator (fun u ↦ 1 - u ^ 2) x) ^ 2) =
      (Set.Icc (-1 : ℝ) 1).indicator (fun x ↦ (1 - x ^ 2) ^ 2) := by
    funext x
    simp only [Set.indicator]
    simp
  rw [hind, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have h1 : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume (-1) 1 :=
    (by fun_prop : Continuous (fun _ : ℝ ↦ (1 : ℝ))).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x : ℝ ↦ 2 * x ^ 2) volume (-1) 1 :=
    (by fun_prop : Continuous (fun x : ℝ ↦ 2 * x ^ 2)).intervalIntegrable _ _
  have h4 : IntervalIntegrable (fun x : ℝ ↦ x ^ 4) volume (-1) 1 :=
    (by fun_prop : Continuous (fun x : ℝ ↦ x ^ 4)).intervalIntegrable _ _
  rw [show (fun x : ℝ ↦ (1 - x ^ 2) ^ 2) =
      (fun x : ℝ ↦ 1 - 2 * x ^ 2 + x ^ 4) by grind,
    intervalIntegral.integral_add (h1.sub h2) h4,
    intervalIntegral.integral_sub h1 h2,
    intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul,
    integral_pow, integral_pow]
  norm_num

/--
@isnad1 id=eq.0h0v.s5.ba9df3112fdb from=translated src=- shape=d4f6e56f vocab=47e5e0a8
-/
@[simp]
theorem tartarWeightConvolution_zero :
    tartarWeightConvolution 0 = 16 / 15 := by
  rw [tartarWeightConvolution]
  have h :
      (fun t : ℝ ↦ Tartar.weight t * Tartar.weight (0 - t)) =
        (fun t : ℝ ↦ Tartar.weight t ^ 2) := by
    funext t
    rw [zero_sub, tartarWeight_neg, pow_two]
  rw [h, integral_tartarWeight_sq]

end NumberField.Odlyzko

end
