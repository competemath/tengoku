/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.PVFourierIdentity
import Tengoku.Seed.Analysis.Fourier.LpSpace
import Tengoku.Seed.Data.Real.Sign
import Tengoku.Seed.MeasureTheory.Function.LpSeminorm.Monotonicity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The ordinary Hilbert transform on `L²`

This file constructs the Fourier-multiplier realization of convolution with
the project's kernel `p.v. (1 / x)`.  Mathlib's Fourier normalization makes
the multiplier `-π i sign(ξ)`, so its `L²` operator norm is at most `π`.
-/

open Filter Function MeasureTheory Set FourierTransform
open scoped ENNReal NNReal SchwartzMap

namespace QuadraticCarleson
namespace HilbertL2Fourier

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

/-- The multiplier dictated by `fourier_principalValueOneDiv`.-/
def ordinaryHilbertMultiplier (ξ : ℝ) : ℂ :=
  -((Real.pi : ℂ) * Complex.I) * (Real.sign ξ : ℂ)

/--
@isnad1 id=measurab.0h0v.s2.a80752595feb from=translated src=- shape=e3d48bcb vocab=5b40c355
-/
theorem measurable_real_sign : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id)
      measurable_const measurable_const)

/--
@isnad1 id=measurab.0h0v.s2.a01f8e96dcb9 from=translated src=- shape=54c8eceb vocab=adca2687
-/
theorem measurable_ordinaryHilbertMultiplier :
    Measurable ordinaryHilbertMultiplier :=
  measurable_const.mul (Complex.measurable_ofReal.comp measurable_real_sign)

/--
@isnad1 id=le.0h1v.s4.52b2faf7ba6c from=translated src=- shape=38becc55 vocab=3a3a0cea
-/
theorem norm_real_sign_le_one (ξ : ℝ) : ‖Real.sign ξ‖ ≤ 1 := by
  rcases Real.sign_apply_eq ξ with h | h | h <;> rw [h] <;> norm_num

/--
@isnad1 id=le.0h1v.s3.34cc5ed5039d from=translated src=- shape=1036feda vocab=dadc4065
-/
theorem norm_ordinaryHilbertMultiplier_le (ξ : ℝ) :
    ‖ordinaryHilbertMultiplier ξ‖ ≤ Real.pi := by
  unfold ordinaryHilbertMultiplier
  rw [norm_mul, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  nlinarith [Real.pi_pos.le, norm_real_sign_le_one ξ,
    norm_nonneg (Real.sign ξ)]

/-- Test-function form of the already-proved distributional identity
`𝓕(p.v. 1/x) = -π i sign`.  This explicitly identifies the pointwise
multiplier used below with the two half-line integrals defining the project's
`signTemperedDistribution`.
@isnad1 id=eq.0h1v.s9.4cb9507b5f23 from=translated src=- shape=57437138 vocab=2b3d0dd3
-/
theorem fourier_principalValueOneDiv_apply_eq_multiplier_halfLines
    (φ : 𝓢(ℝ, ℂ)) :
    (𝓕 principalValueOneDiv) φ =
      (∫ ξ in Ioi (0 : ℝ), ordinaryHilbertMultiplier ξ * φ ξ) +
        ∫ ξ in Iio (0 : ℝ), ordinaryHilbertMultiplier ξ * φ ξ := by
  have hpos : (∫ ξ in Ioi (0 : ℝ), ordinaryHilbertMultiplier ξ * φ ξ) =
      (-((Real.pi : ℂ) * Complex.I)) * ∫ ξ in Ioi (0 : ℝ), φ ξ := by
    calc
      _ = ∫ ξ in Ioi (0 : ℝ),
          (-((Real.pi : ℂ) * Complex.I)) * φ ξ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
        rw [ordinaryHilbertMultiplier, Real.sign_of_pos hξ]
        simp
      _ = _ := integral_const_mul _ _
  have hneg : (∫ ξ in Iio (0 : ℝ), ordinaryHilbertMultiplier ξ * φ ξ) =
      -(-((Real.pi : ℂ) * Complex.I)) * ∫ ξ in Iio (0 : ℝ), φ ξ := by
    calc
      _ = ∫ ξ in Iio (0 : ℝ),
          (-(-((Real.pi : ℂ) * Complex.I))) * φ ξ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Iio] with ξ hξ
        rw [ordinaryHilbertMultiplier, Real.sign_of_neg hξ]
        norm_num
      _ = _ := integral_const_mul _ _
  rw [fourier_principalValueOneDiv]
  change (-((Real.pi : ℂ) * Complex.I)) * signTemperedDistribution φ = _
  rw [signTemperedDistribution_apply, hpos, hneg]
  ring

/-- A fixed measurable representative of the `L²` Fourier transform.-/
def fourierL2Representative (f : Lp (α := ℝ) ℂ 2) : ℝ → ℂ :=
  ⇑(Lp.fourierTransformₗᵢ ℝ ℂ f)

/--
@isnad1 id=memlp.0h1v.s8.62e74958994a from=translated src=- shape=db80459c vocab=94ba6b87
-/
theorem memLp_fourierL2Representative (f : Lp (α := ℝ) ℂ 2) :
    MemLp (fourierL2Representative f) 2 volume :=
  Lp.memLp (Lp.fourierTransformₗᵢ ℝ ℂ f)

def multipliedFourierRepresentative (f : Lp (α := ℝ) ℂ 2) : ℝ → ℂ :=
  fun ξ ↦ ordinaryHilbertMultiplier ξ * fourierL2Representative f ξ

/--
@isnad1 id=memlp.0h1v.s8.50cfc6130083 from=translated src=- shape=db80459c vocab=a1bfbcfb
-/
theorem memLp_ordinaryHilbertMultiplier_mul_fourier
    (f : Lp (α := ℝ) ℂ 2) :
    MemLp (multipliedFourierRepresentative f) 2 volume := by
  apply MemLp.of_le_mul (c := Real.pi) (memLp_fourierL2Representative f)
  · exact measurable_ordinaryHilbertMultiplier.aestronglyMeasurable.mul
      (memLp_fourierL2Representative f).1
  · filter_upwards with ξ
    unfold multipliedFourierRepresentative
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_ordinaryHilbertMultiplier_le ξ)
      (norm_nonneg _)

/-- Fourier-side multiplication by `-π i sign(ξ)`.-/
def ordinaryHilbertMultiplierL2 (f : Lp (α := ℝ) ℂ 2) :
    Lp (α := ℝ) ℂ 2 :=
  MemLp.toLp (μ := volume)
    (multipliedFourierRepresentative f)
    (memLp_ordinaryHilbertMultiplier_mul_fourier f)

/-- The ordinary Hilbert transform on `L²`, obtained by inverse Fourier
transforming the canonical multiplier.-/
def ordinaryHilbertTransformL2 (f : Lp (α := ℝ) ℂ 2) :
    Lp (α := ℝ) ℂ 2 :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm (ordinaryHilbertMultiplierL2 f)

/--
@isnad1 id=le.0h1v.s8.7da8b6c584f1 from=translated src=- shape=77d373db vocab=7dae3851
-/
theorem eLpNorm_multipliedFourierRepresentative_le
    (f : Lp (α := ℝ) ℂ 2) :
    eLpNorm (multipliedFourierRepresentative f) 2 volume ≤
      ENNReal.ofReal Real.pi * eLpNorm (fourierL2Representative f) 2 volume := by
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
  filter_upwards with ξ
  unfold multipliedFourierRepresentative
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_ordinaryHilbertMultiplier_le ξ)
    (norm_nonneg _)

/--
@isnad1 id=eq.0h1v.s8.7810756187a9 from=translated src=- shape=77d373db vocab=74cb68fa
-/
theorem eLpNorm_multipliedFourierRepresentative_eq
    (f : Lp (α := ℝ) ℂ 2 volume) :
    eLpNorm (multipliedFourierRepresentative f) 2 volume =
      ENNReal.ofReal Real.pi * eLpNorm (fourierL2Representative f) 2 volume := by
  have hne : ∀ᵐ ξ : ℝ ∂volume, ξ ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hnorm : ∀ᵐ ξ : ℝ ∂volume,
      ‖multipliedFourierRepresentative f ξ‖ =
        ‖(Real.pi : ℂ) * fourierL2Representative f ξ‖ := by
    filter_upwards [hne] with ξ hξ
    rcases Real.sign_apply_eq_of_ne_zero ξ hξ with hs | hs
    · simp [multipliedFourierRepresentative, ordinaryHilbertMultiplier, hs]
    · simp [multipliedFourierRepresentative, ordinaryHilbertMultiplier, hs]
  calc
    eLpNorm (multipliedFourierRepresentative f) 2 volume =
        eLpNorm (fun ξ ↦ (Real.pi : ℂ) * fourierL2Representative f ξ) 2 volume :=
      eLpNorm_congr_norm_ae hnorm
    _ = ‖(Real.pi : ℂ)‖ₑ * eLpNorm (fourierL2Representative f) 2 volume := by
      change eLpNorm ((Real.pi : ℂ) • fourierL2Representative f) 2 volume = _
      exact eLpNorm_const_smul (Real.pi : ℂ) (fourierL2Representative f) 2 volume
    _ = _ := by
      congr 1
      rw [← ofReal_norm]
      simp [Real.pi_pos.le]

/--
@isnad1 id=le.0h1v.s12.b16d0c448371 from=translated src=- shape=270995b5 vocab=140cc9e0
-/
theorem enorm_ordinaryHilbertMultiplierL2_le (f : Lp (α := ℝ) ℂ 2) :
    ‖ordinaryHilbertMultiplierL2 f‖ₑ ≤
      ENNReal.ofReal Real.pi * ‖f‖ₑ := by
  calc
    ‖ordinaryHilbertMultiplierL2 f‖ₑ =
        eLpNorm (multipliedFourierRepresentative f) 2 volume := by
      exact Lp.enorm_toLp (memLp_ordinaryHilbertMultiplier_mul_fourier f)
    _ ≤ ENNReal.ofReal Real.pi * eLpNorm (fourierL2Representative f) 2 volume :=
      eLpNorm_multipliedFourierRepresentative_le f
    _ = ENNReal.ofReal Real.pi * ‖Lp.fourierTransformₗᵢ ℝ ℂ f‖ₑ := by
      have heq : MemLp.toLp (fourierL2Representative f)
          (memLp_fourierL2Representative f) = Lp.fourierTransformₗᵢ ℝ ℂ f := by
        exact Lp.toLp_coeFn _ _
      rw [← Lp.enorm_toLp (memLp_fourierL2Representative f), heq]
    _ = _ := by simp

/--
@isnad1 id=le.0h1v.s9.ad7589e95b33 from=translated src=- shape=20faaaf2 vocab=ee8b4759
-/
theorem norm_ordinaryHilbertMultiplierL2_le (f : Lp (α := ℝ) ℂ 2) :
    ‖ordinaryHilbertMultiplierL2 f‖ ≤ Real.pi * ‖f‖ := by
  have h := enorm_ordinaryHilbertMultiplierL2_le f
  have hreal := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).2 h
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal Real.pi_pos.le] using hreal

/--
@isnad1 id=eq.0h1v.s9.5eca41c02d67 from=translated src=- shape=47e53e95 vocab=090705a4
-/
theorem norm_ordinaryHilbertMultiplierL2_eq (f : Lp (α := ℝ) ℂ 2 volume) :
    ‖ordinaryHilbertMultiplierL2 f‖ = Real.pi * ‖f‖ := by
  have henorm : ‖ordinaryHilbertMultiplierL2 f‖ₑ =
      ENNReal.ofReal Real.pi * ‖f‖ₑ := by
    calc
      ‖ordinaryHilbertMultiplierL2 f‖ₑ =
          eLpNorm (multipliedFourierRepresentative f) 2 volume :=
        Lp.enorm_toLp (memLp_ordinaryHilbertMultiplier_mul_fourier f)
      _ = ENNReal.ofReal Real.pi * eLpNorm (fourierL2Representative f) 2 volume :=
        eLpNorm_multipliedFourierRepresentative_eq f
      _ = ENNReal.ofReal Real.pi * ‖Lp.fourierTransformₗᵢ ℝ ℂ f‖ₑ := by
        have heq : MemLp.toLp (fourierL2Representative f)
            (memLp_fourierL2Representative f) = Lp.fourierTransformₗᵢ ℝ ℂ f :=
          Lp.toLp_coeFn _ _
        rw [← Lp.enorm_toLp (memLp_fourierL2Representative f), heq]
      _ = _ := by simp
  have hreal := congrArg ENNReal.toReal henorm
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal Real.pi_pos.le] using hreal

/--
@isnad1 id=le.0h1v.s9.289068f1825e from=translated src=- shape=20faaaf2 vocab=0ec1a96d
-/
theorem norm_ordinaryHilbertTransformL2_le (f : Lp (α := ℝ) ℂ 2) :
    ‖ordinaryHilbertTransformL2 f‖ ≤ Real.pi * ‖f‖ := by
  rw [ordinaryHilbertTransformL2]
  change ‖(Lp.fourierTransformₗᵢ ℝ ℂ).symm (ordinaryHilbertMultiplierL2 f)‖ ≤ _
  rw [(Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map]
  exact norm_ordinaryHilbertMultiplierL2_le f

/--
@isnad1 id=eq.0h1v.s9.0d71c826b816 from=translated src=- shape=47e53e95 vocab=c292cc15
-/
theorem norm_ordinaryHilbertTransformL2_eq (f : Lp (α := ℝ) ℂ 2 volume) :
    ‖ordinaryHilbertTransformL2 f‖ = Real.pi * ‖f‖ := by
  rw [ordinaryHilbertTransformL2]
  change ‖(Lp.fourierTransformₗᵢ ℝ ℂ).symm (ordinaryHilbertMultiplierL2 f)‖ = _
  rw [(Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map,
    norm_ordinaryHilbertMultiplierL2_eq]

/--
@isnad1 id=eventual.0h2v.s10.7e351c7b4206 from=translated src=- shape=e3f4d599 vocab=ebfef668
-/
theorem multipliedFourierRepresentative_add_ae
    (f g : Lp (α := ℝ) ℂ 2 volume) :
    multipliedFourierRepresentative (f + g) =ᵐ[volume]
      multipliedFourierRepresentative f + multipliedFourierRepresentative g := by
  have hF : Lp.fourierTransformₗᵢ ℝ ℂ (f + g) =
      Lp.fourierTransformₗᵢ ℝ ℂ f + Lp.fourierTransformₗᵢ ℝ ℂ g :=
    (Lp.fourierTransformₗᵢ ℝ ℂ).map_add f g
  have hcoe := Lp.coeFn_add (Lp.fourierTransformₗᵢ ℝ ℂ f)
    (Lp.fourierTransformₗᵢ ℝ ℂ g)
  filter_upwards [hcoe] with ξ hξ
  unfold multipliedFourierRepresentative fourierL2Representative
  rw [hF]
  change ordinaryHilbertMultiplier ξ *
      ((⇑(Lp.fourierTransformₗᵢ ℝ ℂ f + Lp.fourierTransformₗᵢ ℝ ℂ g)) ξ) = _
  rw [hξ]
  simp only [Pi.add_apply]
  ring

/--
@isnad1 id=eventual.0h2v.s12.9a5ea168463b from=translated src=- shape=96cdcce1 vocab=5d581dcc
-/
theorem multipliedFourierRepresentative_smul_ae
    (c : ℂ) (f : Lp (α := ℝ) ℂ 2 volume) :
    multipliedFourierRepresentative (c • f) =ᵐ[volume]
      c • multipliedFourierRepresentative f := by
  have hF : Lp.fourierTransformₗᵢ ℝ ℂ (c • f) =
      c • Lp.fourierTransformₗᵢ ℝ ℂ f :=
    (Lp.fourierTransformₗᵢ ℝ ℂ).map_smul c f
  have hcoe := Lp.coeFn_smul c (Lp.fourierTransformₗᵢ ℝ ℂ f)
  filter_upwards [hcoe] with ξ hξ
  unfold multipliedFourierRepresentative fourierL2Representative
  rw [hF]
  change ordinaryHilbertMultiplier ξ *
      ((⇑(c • Lp.fourierTransformₗᵢ ℝ ℂ f)) ξ) = _
  rw [hξ]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/--
@isnad1 id=eq.0h2v.s11.d31345fe9279 from=translated src=- shape=b7b3312b vocab=5a291b4e
-/
theorem ordinaryHilbertMultiplierL2_add (f g : Lp (α := ℝ) ℂ 2 volume) :
    ordinaryHilbertMultiplierL2 (f + g) =
      ordinaryHilbertMultiplierL2 f + ordinaryHilbertMultiplierL2 g := by
  calc
    ordinaryHilbertMultiplierL2 (f + g) =
        MemLp.toLp
          (multipliedFourierRepresentative f + multipliedFourierRepresentative g)
          ((memLp_ordinaryHilbertMultiplier_mul_fourier f).add
            (memLp_ordinaryHilbertMultiplier_mul_fourier g)) := by
      exact MemLp.toLp_congr
        (memLp_ordinaryHilbertMultiplier_mul_fourier (f + g))
        ((memLp_ordinaryHilbertMultiplier_mul_fourier f).add
          (memLp_ordinaryHilbertMultiplier_mul_fourier g))
        (multipliedFourierRepresentative_add_ae f g)
    _ = ordinaryHilbertMultiplierL2 f + ordinaryHilbertMultiplierL2 g :=
      MemLp.toLp_add (memLp_ordinaryHilbertMultiplier_mul_fourier f)
        (memLp_ordinaryHilbertMultiplier_mul_fourier g)

/--
@isnad1 id=eq.0h2v.s13.65f73ec2e17f from=translated src=- shape=6076b93c vocab=83b4ec4c
-/
theorem ordinaryHilbertMultiplierL2_smul (c : ℂ)
    (f : Lp (α := ℝ) ℂ 2 volume) :
    ordinaryHilbertMultiplierL2 (c • f) = c • ordinaryHilbertMultiplierL2 f := by
  calc
    ordinaryHilbertMultiplierL2 (c • f) =
        MemLp.toLp (c • multipliedFourierRepresentative f)
          ((memLp_ordinaryHilbertMultiplier_mul_fourier f).const_smul c) := by
      exact MemLp.toLp_congr
        (memLp_ordinaryHilbertMultiplier_mul_fourier (c • f))
        ((memLp_ordinaryHilbertMultiplier_mul_fourier f).const_smul c)
        (multipliedFourierRepresentative_smul_ae c f)
    _ = c • ordinaryHilbertMultiplierL2 f :=
      MemLp.toLp_const_smul c (memLp_ordinaryHilbertMultiplier_mul_fourier f)

/--
@isnad1 id=eq.0h2v.s11.a8e522c5e215 from=translated src=- shape=b7b3312b vocab=51b8a812
-/
theorem ordinaryHilbertTransformL2_add (f g : Lp (α := ℝ) ℂ 2 volume) :
    ordinaryHilbertTransformL2 (f + g) =
      ordinaryHilbertTransformL2 f + ordinaryHilbertTransformL2 g := by
  unfold ordinaryHilbertTransformL2
  rw [ordinaryHilbertMultiplierL2_add, map_add]

/--
@isnad1 id=eq.0h2v.s13.65138dfdf41e from=translated src=- shape=6076b93c vocab=ffd41083
-/
theorem ordinaryHilbertTransformL2_smul (c : ℂ)
    (f : Lp (α := ℝ) ℂ 2 volume) :
    ordinaryHilbertTransformL2 (c • f) = c • ordinaryHilbertTransformL2 f := by
  unfold ordinaryHilbertTransformL2
  rw [ordinaryHilbertMultiplierL2_smul, map_smul]

def ordinaryHilbertTransformL2LinearMap :
    Lp (α := ℝ) ℂ 2 →ₗ[ℂ] Lp (α := ℝ) ℂ 2 where
  toFun := ordinaryHilbertTransformL2
  map_add' := ordinaryHilbertTransformL2_add
  map_smul' := ordinaryHilbertTransformL2_smul

/-- The Fourier realization of `p.v. (1/x)` as a genuine continuous linear
operator on `L²`.-/
def ordinaryHilbertTransformL2CLM :
    Lp (α := ℝ) ℂ 2 →L[ℂ] Lp (α := ℝ) ℂ 2 :=
  ordinaryHilbertTransformL2LinearMap.mkContinuous Real.pi
    norm_ordinaryHilbertTransformL2_le

/--
@isnad1 id=eq.0h1v.s12.fb22b8991bd9 from=translated src=- shape=ff25544a vocab=19b7053a
-/
@[simp] theorem ordinaryHilbertTransformL2CLM_apply
    (f : Lp (α := ℝ) ℂ 2) :
    ordinaryHilbertTransformL2CLM f = ordinaryHilbertTransformL2 f := rfl

/--
@isnad1 id=le.0h0v.s11.eee0e8fbfd64 from=translated src=- shape=248419a8 vocab=9ea6e6c3
-/
theorem norm_ordinaryHilbertTransformL2CLM_le :
    ‖ordinaryHilbertTransformL2CLM‖ ≤ Real.pi :=
  LinearMap.mkContinuous_norm_le (f := ordinaryHilbertTransformL2LinearMap)
    Real.pi_pos.le norm_ordinaryHilbertTransformL2_le

/-- Fourier transforming the constructed Hilbert operator recovers exactly
the canonical multiplier class.
@isnad1 id=eq.0h1v.s12.db8cf54e6c3b from=translated src=- shape=68c8f38a vocab=8d4bd0fe
-/
theorem fourier_ordinaryHilbertTransformL2
    (f : Lp (α := ℝ) ℂ 2 volume) :
    Lp.fourierTransformₗᵢ ℝ ℂ (ordinaryHilbertTransformL2 f) =
      ordinaryHilbertMultiplierL2 f := by
  unfold ordinaryHilbertTransformL2
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply _

/-- Representative-level form of the multiplier identity.
@isnad1 id=eventual.0h1v.s12.30c3d4963b2f from=translated src=- shape=1cfe954c vocab=3e8cfbac
-/
theorem coe_fourier_ordinaryHilbertTransformL2_ae
    (f : Lp (α := ℝ) ℂ 2 volume) :
    (⇑(Lp.fourierTransformₗᵢ ℝ ℂ (ordinaryHilbertTransformL2 f)) : ℝ → ℂ)
      =ᵐ[volume] multipliedFourierRepresentative f := by
  rw [fourier_ordinaryHilbertTransformL2]
  exact MemLp.coeFn_toLp (memLp_ordinaryHilbertMultiplier_mul_fourier f)

/--
@isnad1 id=eq.1h1v.s5.560d1f7def2f from=translated src=- shape=b8145760 vocab=951c1c4f
-/
theorem ordinaryHilbertMultiplier_sq {ξ : ℝ} (hξ : ξ ≠ 0) :
    ordinaryHilbertMultiplier ξ * ordinaryHilbertMultiplier ξ =
      -((Real.pi : ℂ) ^ 2) := by
  rcases Real.sign_apply_eq_of_ne_zero ξ hξ with hs | hs
  · simp only [ordinaryHilbertMultiplier, hs, Complex.ofReal_neg, Complex.ofReal_one,
      mul_neg, mul_one, neg_neg, ← pow_two, mul_pow, Complex.I_sq]
  · simp only [ordinaryHilbertMultiplier, hs, Complex.ofReal_one, mul_one, ← pow_two]
    rw [neg_sq, mul_pow, Complex.I_sq]
    ring

/--
@isnad1 id=eventual.0h1v.s8.bba8773bbef4 from=translated src=- shape=890364dd vocab=d7b1483e
-/
theorem multipliedFourierRepresentative_hilbert_ae
    (f : Lp (α := ℝ) ℂ 2 volume) :
    multipliedFourierRepresentative (ordinaryHilbertTransformL2 f) =ᵐ[volume]
      (-((Real.pi : ℂ) ^ 2)) • fourierL2Representative f := by
  have hne : ∀ᵐ ξ : ℝ ∂volume, ξ ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hF := coe_fourier_ordinaryHilbertTransformL2_ae f
  filter_upwards [hne, hF] with ξ hξ hFξ
  unfold multipliedFourierRepresentative fourierL2Representative
  rw [hFξ]
  unfold multipliedFourierRepresentative
  rw [← mul_assoc, ordinaryHilbertMultiplier_sq hξ]
  simp only [Pi.smul_apply, smul_eq_mul]
  rfl

/--
@isnad1 id=eq.0h1v.s13.a66ebb557a82 from=translated src=- shape=c58bbe5c vocab=3d4fc36c
-/
theorem ordinaryHilbertMultiplierL2_hilbert
    (f : Lp (α := ℝ) ℂ 2 volume) :
    ordinaryHilbertMultiplierL2 (ordinaryHilbertTransformL2 f) =
      (-((Real.pi : ℂ) ^ 2)) • Lp.fourierTransformₗᵢ ℝ ℂ f := by
  calc
    ordinaryHilbertMultiplierL2 (ordinaryHilbertTransformL2 f) =
        MemLp.toLp
          ((-((Real.pi : ℂ) ^ 2)) • fourierL2Representative f)
          ((memLp_fourierL2Representative f).const_smul (-((Real.pi : ℂ) ^ 2))) := by
      exact MemLp.toLp_congr
        (memLp_ordinaryHilbertMultiplier_mul_fourier (ordinaryHilbertTransformL2 f))
        ((memLp_fourierL2Representative f).const_smul (-((Real.pi : ℂ) ^ 2)))
        (multipliedFourierRepresentative_hilbert_ae f)
    _ = (-((Real.pi : ℂ) ^ 2)) •
        MemLp.toLp (fourierL2Representative f) (memLp_fourierL2Representative f) :=
      MemLp.toLp_const_smul _ (memLp_fourierL2Representative f)
    _ = _ := by
      have heq : MemLp.toLp (fourierL2Representative f)
          (memLp_fourierL2Representative f) = Lp.fourierTransformₗᵢ ℝ ℂ f := by
        exact Lp.toLp_coeFn _ _
      rw [heq]

/-- With the project's unnormalized kernel `p.v. (1/x)`, the `L²` Hilbert
operator squares to `-π²` times the identity.
@isnad1 id=eq.0h1v.s12.95444735f761 from=translated src=- shape=ef206381 vocab=42246c21
-/
theorem ordinaryHilbertTransformL2_sq
    (f : Lp (α := ℝ) ℂ 2 volume) :
    ordinaryHilbertTransformL2 (ordinaryHilbertTransformL2 f) =
      (-((Real.pi : ℂ) ^ 2)) • f := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [fourier_ordinaryHilbertTransformL2,
    ordinaryHilbertMultiplierL2_hilbert, map_smul]

end
end HilbertL2Fourier
end QuadraticCarleson
