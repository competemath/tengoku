/-
Copyright (c) 2024 Sidharth Hariharan and 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Sidharth Hariharan, Gareth Ma, Dean Cureton
-/

module

import all Tengoku.LeanPool.LeanPool.SpherePacking.HarmonicAnalysis
public import Tengoku
import Tengoku

/-!
# RadialConstruction

Construction of radial admissible witnesses and sharp asymptotics.
-/

namespace CohnElkies

section

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology

private noncomputable def SaddleSourceSchwartzRealization : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (ε ^ 3) ≤ (10 * Real.log (1 / ε)) →
      ∀ d : ℕ, 0 < d →
        ∃ fminus fplus : TestFunction d,
          (∀ x : Euclidean d,
            fminus x = minusSaddleFunction ε d x) ∧
          (∀ x : Euclidean d,
            fplus x = plusSaddleFunction ε d x)

private noncomputable def SaddleSourceEventualSigns : Prop :=
  ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ᶠ d : ℕ in atTop,
      (∀ x : Euclidean d,
        0 ≤ (plusSaddleFunction ε d x).re) ∧
      (∀ x : Euclidean d,
        saddleSourceRadius ε d ≤ ‖x‖ →
          (minusSaddleFunction ε d x).re ≤ 0)

end

section

open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology

private noncomputable def lowerGammaBoundaryCapped (ℓ R D y : ℝ) : ℝ :=
  if y = 0 then D else min (lowerGammaBoundaryLog ℓ R y) D

private noncomputable def stripRegularizedOuter (ℓ : ℝ) (b : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ y : ℝ,
    stripRegularizedHolomorphicPoissonKernel ℓ z y *
      (b y : ℂ)

private noncomputable def lowerStripCappedGammaOuter
    (ℓ R D : ℝ) (z : ℂ) : ℂ :=
  stripRegularizedOuter ℓ
    (lowerGammaBoundaryCapped ℓ R D) z

end

section

open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology

private noncomputable def horizontalStripRealTraceExtension
    (a b : ℝ) (H : ℂ → ℝ)
    (bottom top : ℝ → ℝ) (z : ℂ) : ℝ :=
  if z.im = a then bottom z.re
  else if z.im = b then top z.re
  else H z

private noncomputable def lowerStripCappedGammaHarmonic
    (d : ℕ) (R D : ℝ) (z : ℂ) : ℝ :=
  horizontalStripRealTraceExtension
    (-((d : ℝ) / 2)) ((d : ℝ) / 2)
    (fun w : ℂ =>
      (lowerStripCappedGammaOuter ((d : ℝ) / 2) R D w).re)
    (lowerGammaBoundaryCapped ((d : ℝ) / 2) R D)
    (fun _ : ℝ => 0) z

end

section

open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology

private noncomputable def stripPoissonWeightedMeasure
    (σ s : ℝ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity
    (fun x : ℝ =>
      ENNReal.ofReal (stripPoissonKernel σ (s - x)))

private noncomputable def lowerGammaScaledCappedClipped
    (d : ℕ) (c D n Y : ℝ) : ℝ :=
  max
    (lowerGammaBoundaryCapped ((d : ℝ) / 2)
      (c * Real.sqrt d) D (((d : ℝ) / 2) * Y) + n)
    0

private noncomputable def lowerGammaScaledCappedLowerClip
    (d : ℕ) (c D n Y : ℝ) : ℝ :=
  max
    (lowerGammaBoundaryCapped ((d : ℝ) / 2)
      (c * Real.sqrt d) D (((d : ℝ) / 2) * Y))
    (-n)

private noncomputable def lowerRiemannErrorMajorant (T : ℝ) : ℝ :=
  3 * |lowerRiemannLog T 0| +
    2 * |lowerRiemannLog T 1| +
      (1 / 2 : ℝ) *
        Real.log (lowerCoth (Real.pi * |T| / 2))

private noncomputable def lowerRiemannPoissonError (σ : ℝ) : ℝ :=
  ∫ T : ℝ,
    stripPoissonKernel σ T * lowerRiemannErrorMajorant T

private noncomputable def stripPoissonCoreMass (σ : ℝ) : ℝ :=
  ∫ T in Icc (-1 : ℝ) 1, stripPoissonKernel σ T

private noncomputable def lowerInverseQuadraticMass : ℝ :=
  ∫ S : ℝ, 1 / (1 + |S|) ^ 2

end

section

open Filter MeasureTheory Set
open scoped ENNReal Interval Topology

end

section

open Set

private noncomputable def quotientRootMap (d : ℕ) (x : ℝ) : ℝ :=
  x ^ ((d : ℝ)⁻¹) / Real.sqrt (d : ℝ)

private noncomputable def packingGeometricRoot (d : ℕ) : ℝ :=
  (unitBallVolume d / (2 : ℝ) ^ d) ^ ((d : ℝ)⁻¹) *
    Real.sqrt (d : ℝ)

end

section

open Filter
open scoped Nat Topology

private noncomputable def normalizedVolumeLog (d : ℕ) : ℝ :=
  Real.log (unitBallVolume d) / (d : ℝ) +
    Real.log (d : ℝ) / 2

private noncomputable def normalizedVolumeRoot (d : ℕ) : ℝ :=
  unitBallVolume d ^ ((d : ℝ)⁻¹) * Real.sqrt (d : ℝ)

end

section

open Filter Function MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology RealInnerProductSpace Pointwise ContDiff

private noncomputable def radialFlatBumpReal (d : ℕ) (x : Euclidean d) : ℝ :=
  expNegInvGlue (1 - 4 * ‖x‖ ^ 2)

private noncomputable def radialFlatBumpFun (d : ℕ) (x : Euclidean d) : ℂ :=
  (radialFlatBumpReal d x : ℂ)

private theorem radialFlatBumpReal_nonneg (d : ℕ) (x : Euclidean d) :
    0 ≤ radialFlatBumpReal d x :=
  expNegInvGlue.nonneg _

private theorem radialFlatBumpReal_zero_pos (d : ℕ) :
    0 < radialFlatBumpReal d (0 : Euclidean d) := by
  unfold radialFlatBumpReal
  simpa only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    sub_zero] using! expNegInvGlue.pos_of_pos (by norm_num : (0 : ℝ) < 1)

private theorem support_radialFlatBumpReal (d : ℕ) :
    Function.support (radialFlatBumpReal d) =
      Metric.ball (0 : Euclidean d) (1 / 2 : ℝ) := by
  ext x
  simp only [Function.mem_support, radialFlatBumpReal,
    Metric.mem_ball, dist_zero_right]
  constructor
  · intro hx
    have hpos : 0 < 1 - 4 * ‖x‖ ^ 2 := by
      exact lt_of_not_ge (fun h => hx (expNegInvGlue.zero_of_nonpos h))
    nlinarith [norm_nonneg x]
  · intro hx
    have hpos : 0 < 1 - 4 * ‖x‖ ^ 2 := by
      nlinarith [norm_nonneg x]
    exact (expNegInvGlue.pos_of_pos hpos).ne'

private theorem support_radialFlatBumpFun (d : ℕ) :
    Function.support (radialFlatBumpFun d) =
      Metric.ball (0 : Euclidean d) (1 / 2 : ℝ) := by
  rw [← support_radialFlatBumpReal d]
  ext x
  simp only [mem_support, radialFlatBumpFun, ne_eq, Complex.ofReal_eq_zero]

private theorem radialFlatBumpFun_contDiff (d : ℕ) :
    ContDiff ℝ ∞ (radialFlatBumpFun d) := by
  change ContDiff ℝ ∞
    (fun x : Euclidean d =>
      Complex.ofRealCLM (expNegInvGlue (1 - 4 * ‖x‖ ^ 2)))
  exact Complex.ofRealCLM.contDiff.comp
    (expNegInvGlue.contDiff.comp
      (contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ))))

private theorem radialFlatBumpFun_hasCompactSupport (d : ℕ) :
    HasCompactSupport (radialFlatBumpFun d) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Euclidean d) (1 / 2 : ℝ))
  rw [support_radialFlatBumpFun]
  exact Metric.ball_subset_closedBall

private noncomputable def radialFlatBump (d : ℕ) : TestFunction d :=
  (radialFlatBumpFun_hasCompactSupport d).toSchwartzMap
    (radialFlatBumpFun_contDiff d)

@[simp] private theorem radialFlatBump_apply (d : ℕ) (x : Euclidean d) :
    radialFlatBump d x = (radialFlatBumpReal d x : ℂ) := by
  rfl

private theorem radialFlatBump_real (d : ℕ) : IsRealValued (radialFlatBump d) := by
  intro x
  simp only [radialFlatBump_apply, Complex.ofReal_im]

private theorem radialFlatBump_radial (d : ℕ) : IsRadial (radialFlatBump d) := by
  intro x y hxy
  simp only [radialFlatBump_apply, radialFlatBumpReal, hxy]

private theorem integral_radialFlatBumpReal_pos (d : ℕ) :
    0 < ∫ x : Euclidean d, radialFlatBumpReal d x := by
  apply integral_pos_of_integrable_nonneg_nonzero
    (show Continuous (radialFlatBumpReal d) by
      unfold radialFlatBumpReal
      fun_prop)
  · have hcomplex :
        Integrable (radialFlatBump d : Euclidean d → ℂ) :=
      (radialFlatBump d).integrable
    simpa only [radialFlatBump_apply, RCLike.re_to_complex, Complex.ofReal_re] using! hcomplex.re
  · exact radialFlatBumpReal_nonneg d
  · exact (radialFlatBumpReal_zero_pos d).ne'

private theorem IsRadial.fourier {d : ℕ} {f : TestFunction d}
    (hf : IsRadial f) : IsRadial (𝓕 f : TestFunction d) := by
  intro x y hxy
  let A : Euclidean d ≃ₗᵢ[ℝ] Euclidean d :=
    Submodule.reflection (ℝ ∙ (x - y))ᗮ
  have hA : A x = y := Submodule.reflection_sub hxy
  have hcomp : (f : Euclidean d → ℂ) ∘ A = f := by
    funext z
    exact hf (A z) z (A.norm_map z)
  change (𝓕 (f : Euclidean d → ℂ)) x =
    (𝓕 (f : Euclidean d → ℂ)) y
  calc
    (𝓕 (f : Euclidean d → ℂ)) x =
        (𝓕 ((f : Euclidean d → ℂ) ∘ A)) x := by rw [hcomp]
    _ = (𝓕 (f : Euclidean d → ℂ)) (A x) :=
      Real.fourier_comp_linearIsometry A (f : Euclidean d → ℂ) x
    _ = (𝓕 (f : Euclidean d → ℂ)) y := by rw [hA]

private theorem fourier_conj_apply_of_real {d : ℕ} (f : TestFunction d)
    (hf : IsRealValued f) (ξ : Euclidean d) :
    starRingEnd ℂ ((𝓕 f : TestFunction d) ξ) =
      ((𝓕 f : TestFunction d) (-ξ)) := by
  change starRingEnd ℂ ((𝓕 (f : Euclidean d → ℂ)) ξ) =
    (𝓕 (f : Euclidean d → ℂ)) (-ξ)
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  have hreal : starRingEnd ℂ (f x) = f x :=
    Complex.conj_eq_iff_im.mpr (hf x)
  have htwo : starRingEnd ℂ (2 : ℂ) = 2 := Complex.conj_ofNat 2
  simp only [neg_mul, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat, smul_eq_mul,
    map_mul,
    ← Complex.exp_conj, map_neg, htwo, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg,
      hreal, inner_neg_right]

private theorem IsRealValued.fourier_of_radial {d : ℕ} {f : TestFunction d}
    (hf : IsRealValued f) (hrad : IsRadial f) :
    IsRealValued (𝓕 f : TestFunction d) := by
  intro ξ
  apply Complex.conj_eq_iff_im.mp
  rw [fourier_conj_apply_of_real f hf]
  exact hrad.fourier (-ξ) ξ (by simp only [norm_neg])

private noncomputable def radialAutocorrelation (d : ℕ) : TestFunction d :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
    (radialFlatBump d) (radialFlatBump d)

private theorem fourier_radialAutocorrelation_apply (d : ℕ) (ξ : Euclidean d) :
    ((𝓕 (radialAutocorrelation d) : TestFunction d) ξ) =
      ((𝓕 (radialFlatBump d) : TestFunction d) ξ) ^ 2 := by
  unfold radialAutocorrelation
  rw [SchwartzMap.fourier_convolution]
  simp only [SchwartzMap.pairing_apply_apply, ContinuousLinearMap.mul_apply', pow_two]

private theorem fourier_radialFlatBump_real (d : ℕ) :
    IsRealValued (𝓕 (radialFlatBump d) : TestFunction d) :=
  (radialFlatBump_real d).fourier_of_radial (radialFlatBump_radial d)

private theorem fourier_radialAutocorrelation_real (d : ℕ) :
    IsRealValued (𝓕 (radialAutocorrelation d) : TestFunction d) := by
  intro ξ
  rw [fourier_radialAutocorrelation_apply]
  simp only [pow_two, Complex.mul_im, fourier_radialFlatBump_real d ξ, mul_zero, zero_mul, add_zero]

private theorem fourier_radialAutocorrelation_nonneg (d : ℕ) (ξ : Euclidean d) :
    0 ≤ ((𝓕 (radialAutocorrelation d) : TestFunction d) ξ).re := by
  rw [fourier_radialAutocorrelation_apply]
  simp only [pow_two, Complex.mul_re, fourier_radialFlatBump_real d ξ,
    mul_zero, sub_zero]
  exact mul_self_nonneg _

private theorem fourier_radialFlatBump_zero (d : ℕ) :
    ((𝓕 (radialFlatBump d) : TestFunction d) (0 : Euclidean d)) =
      (↑(∫ x : Euclidean d, radialFlatBumpReal d x) : ℂ) := by
  change (𝓕 (radialFlatBump d : Euclidean d → ℂ)) 0 = _
  rw [Real.fourier_eq']
  simpa only [neg_mul, inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    radialFlatBump_apply, smul_eq_mul, one_mul, Complex.coe_algebraMap] using!
    (integral_ofReal (𝕜 := ℂ)
      (f := radialFlatBumpReal d)
      (μ := (volume : Measure (Euclidean d))))

private theorem fourier_radialAutocorrelation_zero_pos (d : ℕ) :
    0 < ((𝓕 (radialAutocorrelation d) : TestFunction d)
      (0 : Euclidean d)).re := by
  rw [fourier_radialAutocorrelation_apply,
    fourier_radialFlatBump_zero]
  simpa only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    mul_self_pos,
    ne_eq] using!
    mul_pos (integral_radialFlatBumpReal_pos d)
      (integral_radialFlatBumpReal_pos d)

private theorem support_radialFlatBump (d : ℕ) :
    Function.support (radialFlatBump d : Euclidean d → ℂ) =
      Metric.ball (0 : Euclidean d) (1 / 2 : ℝ) :=
  support_radialFlatBumpFun d

private theorem support_radialAutocorrelation_subset (d : ℕ) :
    Function.support (radialAutocorrelation d : Euclidean d → ℂ) ⊆
      Metric.ball (0 : Euclidean d) (1 : ℝ) := by
  have hconv :
      (radialAutocorrelation d : Euclidean d → ℂ) =
        MeasureTheory.convolution
          (radialFlatBump d : Euclidean d → ℂ)
          (radialFlatBump d : Euclidean d → ℂ)
          (ContinuousLinearMap.mul ℂ ℂ) volume := by
    funext x
    exact SchwartzMap.convolution_apply (ContinuousLinearMap.mul ℂ ℂ)
      (radialFlatBump d) (radialFlatBump d) x
  rw [hconv]
  calc
    Function.support
        (MeasureTheory.convolution
          (radialFlatBump d : Euclidean d → ℂ)
          (radialFlatBump d : Euclidean d → ℂ)
          (ContinuousLinearMap.mul ℂ ℂ) volume) ⊆
        Function.support (radialFlatBump d : Euclidean d → ℂ) +
          Function.support (radialFlatBump d : Euclidean d → ℂ) :=
      MeasureTheory.support_convolution_subset
        (ContinuousLinearMap.mul ℂ ℂ)
    _ = Metric.ball (0 : Euclidean d) (1 : ℝ) := by
      rw [support_radialFlatBump]
      rw [ball_add_ball (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (0 : ℝ) < 1 / 2)]
      norm_num

private theorem radialAutocorrelation_outside_eq_zero (d : ℕ)
    (x : Euclidean d) (hx : 1 ≤ ‖x‖) :
    radialAutocorrelation d x = 0 := by
  by_contra hne
  have hsupport : x ∈ Function.support
      (radialAutocorrelation d : Euclidean d → ℂ) := hne
  have hball := support_radialAutocorrelation_subset d hsupport
  have hnorm : ‖x‖ < (1 : ℝ) := by
    simpa only [Metric.mem_ball, dist_zero_right] using! hball
  linarith

private theorem radialAutocorrelation_real (d : ℕ) :
    IsRealValued (radialAutocorrelation d) := by
  intro x
  rw [radialAutocorrelation, SchwartzMap.convolution_apply,
    MeasureTheory.convolution_def]
  change
    (∫ t : Euclidean d,
      (radialFlatBumpReal d t : ℂ) *
        (radialFlatBumpReal d (x - t) : ℂ)).im = 0
  simp_rw [← Complex.ofReal_mul]
  have hreal :
      (∫ t : Euclidean d,
        (↑(radialFlatBumpReal d t *
          radialFlatBumpReal d (x - t)) : ℂ)) =
        (↑(∫ t : Euclidean d,
          radialFlatBumpReal d t * radialFlatBumpReal d (x - t)) : ℂ) :=
    integral_ofReal (𝕜 := ℂ)
  rw [hreal]
  simp only [Complex.ofReal_im]

private theorem fourier_radialAutocorrelation_radial (d : ℕ) :
    IsRadial (𝓕 (radialAutocorrelation d) : TestFunction d) := by
  intro x y hxy
  rw [fourier_radialAutocorrelation_apply,
    fourier_radialAutocorrelation_apply]
  rw [(radialFlatBump_radial d).fourier x y hxy]

private theorem radialAutocorrelation_radial (d : ℕ) :
    IsRadial (radialAutocorrelation d) := by
  intro x y hxy
  have h := (fourier_radialAutocorrelation_radial d).fourier
    (-x) (-y) (by simpa only [norm_neg] using! hxy)
  simpa only [fourier_sq_apply, neg_neg] using! h

private noncomputable def autocorrelationAdmissible (d : ℕ) : Admissible d where
  function := radialAutocorrelation d
  real := radialAutocorrelation_real d
  radial := radialAutocorrelation_radial d
  fourier_real := fourier_radialAutocorrelation_real d
  fourier_nonneg := fourier_radialAutocorrelation_nonneg d
  fourier_zero_pos := fourier_radialAutocorrelation_zero_pos d
  outside_nonpos := by
    intro x hx
    rw [radialAutocorrelation_outside_eq_zero d x hx]
    simp only [Complex.zero_re, Std.le_refl]

end

section

end

section

open Filter
open scoped Topology

private noncomputable def SharpBinaryLogAsymptotic : Prop :=
  Tendsto
    (fun d : ℕ => Real.logb 2 (linearProgram d) / (d : ℝ))
    atTop (nhds (-criticalBinaryExponent))

end

section

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology

end

section

open Filter
open scoped Topology

private noncomputable def manuscriptQuotientRootSet (d : ℕ) : Set ℝ :=
  Set.range fun f : Admissible d => quotient f ^ ((d : ℝ)⁻¹)

private noncomputable def manuscriptNormalizedQuotientInfRoot (d : ℕ) : ℝ :=
  (sInf (quotientSet d)) ^ ((d : ℝ)⁻¹) / Real.sqrt (d : ℝ)

private noncomputable def manuscriptPackingDeficit (d : ℕ) : ℝ :=
  max 0 (criticalPackingBase - (linearProgram d) ^ ((d : ℝ)⁻¹))

private noncomputable def manuscriptPackingRootError (d : ℕ) : ℝ :=
  (linearProgram d) ^ ((d : ℝ)⁻¹) - criticalPackingBase

private noncomputable def manuscriptBinaryExponentError (d : ℕ) : ℝ :=
  -(Real.logb 2 (linearProgram d) / (d : ℝ)) -
    criticalBinaryExponent

private noncomputable def manuscriptQuotientRootError (d : ℕ) : ℝ :=
  normalizedProgram d - Real.pi⁻¹

end

end CohnElkies
