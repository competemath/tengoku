/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Seed.Analysis.Distribution.SchwartzSpace.Fourier
public import Tengoku.Seed.MeasureTheory.Measure.Haar.NormedSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Normalized dilation of smoothing kernels

The dilation `a^dim • f (a • x)`, for `a > 0`, preserves the one-norm.
Its Fourier transform is `𝓕 f (a⁻¹ • ξ)`, so a fixed Fourier gap scales
linearly while uniform multiplier bounds remain unchanged.
-/

public section

open MeasureTheory
open scoped SchwartzMap FourierTransform ENNReal NNReal

namespace NKBesicovitch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Dilation normalized to preserve the integral and the one-norm of a smoothing kernel.-/
@[expose] noncomputable def normalizedDilation (a : ℝ) (ha : 0 < a)
    (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  (a ^ Module.finrank ℝ E) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (Units.mk0 a ha.ne' • ContinuousLinearEquiv.refl ℝ E) f

/--
@isnad1 id=eq.1h4v.s8.f0a0744e0aea from=translated src=- shape=e2d064e3 vocab=f5525ce5
-/
@[simp] theorem normalizedDilation_apply (a : ℝ) (ha : 0 < a) (f : 𝓢(E, ℂ)) (x : E) :
    normalizedDilation a ha f x = (a ^ Module.finrank ℝ E) • f (a • x) := rfl

/--
@isnad1 id=eq.0h2v.s6.18e9e5325aea from=translated src=- shape=a4e8052b vocab=cda87945
-/
@[simp] theorem normalizedDilation_one (f : 𝓢(E, ℂ)) : normalizedDilation 1 zero_lt_one f = f := by
  ext x
  simp only [normalizedDilation_apply, one_pow, one_smul]

/--
@isnad1 id=eq.1h4v.s8.be46ad11dce0 from=translated src=- shape=5e26e3e6 vocab=ca251045
-/
@[simp] theorem normalizedDilation_sub (a : ℝ) (ha : 0 < a) (f g : 𝓢(E, ℂ)) :
    normalizedDilation a ha (f - g) = normalizedDilation a ha f - normalizedDilation a ha g := by
  ext x
  simp only [normalizedDilation_apply, sub_apply, smul_sub]

/--
@isnad1 id=eq.2h4v.s6.7e12a4d7b0f2 from=translated src=- shape=ccca0f72 vocab=6f4c8977
-/
theorem normalizedDilation_mul (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (f : 𝓢(E, ℂ)) :
    normalizedDilation a ha (normalizedDilation b hb f) =
      normalizedDilation (a * b) (mul_pos ha hb) f := by
  ext x
  simp only [normalizedDilation_apply, smul_smul, mul_pow, mul_comm]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/--
@isnad1 id=eq.1h3v.s8.9f68af773bcd from=translated src=- shape=61af4cb9 vocab=13c1a538
-/
theorem eLpNorm_normalizedDilation_one (a : ℝ) (ha : 0 < a) (f : 𝓢(E, ℂ)) :
    eLpNorm (normalizedDilation a ha f) 1 volume = eLpNorm f 1 volume := by
  simp only [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm (normalizedDilation a ha f).integrable,
    ← ofReal_integral_norm_eq_lintegral_enorm f.integrable]
  congr 1
  simp only [normalizedDilation_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (pow_pos ha _), integral_const_mul]
  rw [Measure.integral_comp_smul_of_nonneg volume (fun x ↦ ‖f x‖) a (hR := ha.le)]
  simp only [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ha.ne'), one_mul]

/--
@isnad1 id=eq.1h4v.s8.618063e72fb1 from=translated src=- shape=5b9e4dca vocab=424c835a
-/
theorem fourier_normalizedDilation (a : ℝ) (ha : 0 < a) (f : 𝓢(E, ℂ)) (ξ : E) :
    𝓕 (normalizedDilation a ha f) ξ = 𝓕 f (a⁻¹ • ξ) := by
  simp only [SchwartzMap.fourier_coe, Real.fourier_eq, normalizedDilation_apply]
  simp_rw [smul_comm _ (a ^ Module.finrank ℝ E), integral_smul]
  rw [← Measure.integral_comp_inv_smul_of_nonneg volume _ ha.le]
  simp only [real_inner_smul_left, real_inner_smul_right, smul_inv_smul₀ ha.ne']

end NKBesicovitch
