/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.TranslationTP2
public import Tengoku
public import Tengoku.LeanPool.LeanPool.Feige.OneSidedDensity

/-!
# Finite signed exponential sums

The common part of a genuine insertion edge is a distinguished rate-one
exponential together with finitely many positive or negative scaled
rate-one exponentials.  This file gives that law an explicit normalized
density and derives its four-point log-concavity from translation TP2
closure under convolution.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory ProbabilityTheory

namespace Feige
namespace LikelihoodRatio

noncomputable section

/--
@isnad1 id=eq.1h1v.s4.069194653165 from=translated src=- shape=70c165f1 vocab=a0169b5e
-/
lemma rightExponentialDensity_eq_exponentialPDF
    {a : ℝ} (ha : 0 < a) :
    rightExponentialDensity a = exponentialPDF a⁻¹ := by
  funext x
  by_cases hx : 0 ≤ x
  · rw [rightExponentialDensity, ite_eq_left hx,
      exponentialPDF_of_nonneg hx]
    congr 1
    field_simp [ha.ne']
  · rw [rightExponentialDensity, ite_eq_right hx,
      exponentialPDF_of_neg (lt_of_not_ge hx)]

/--
@isnad1 id=eq.1h1v.s5.56ebf4078441 from=translated src=- shape=03ffa9dc vocab=7409c02f
-/
lemma lintegral_rightExponentialDensity
    {a : ℝ} (ha : 0 < a) :
    ∫⁻ x, rightExponentialDensity a x = 1 := by
  rw [rightExponentialDensity_eq_exponentialPDF ha]
  exact lintegral_exponentialPDF_eq_one (inv_pos.mpr ha)

/--
@isnad1 id=eq.1h1v.s5.37700774355a from=translated src=- shape=03ffa9dc vocab=40465c1b
-/
lemma lintegral_leftExponentialDensity
    {b : ℝ} (hb : 0 < b) :
    ∫⁻ x, leftExponentialDensity b x = 1 := by
  unfold leftExponentialDensity
  rw [lintegral_neg_eq_self]
  exact lintegral_rightExponentialDensity hb

/--
@isnad1 id=ne.0h2v.s3.9e5a225cdc82 from=translated src=- shape=20072a53 vocab=a3f85fa8
-/
lemma rightExponentialDensity_ne_top (a x : ℝ) :
    rightExponentialDensity a x ≠ ∞ := by
  unfold rightExponentialDensity
  split_ifs <;> simp

/--
@isnad1 id=ne.0h2v.s3.564f105bc402 from=translated src=- shape=20072a53 vocab=e66101da
-/
lemma leftExponentialDensity_ne_top (b x : ℝ) :
    leftExponentialDensity b x ≠ ∞ :=
  rightExponentialDensity_ne_top b (-x)

/--
@isnad1 id=le.1h2v.s4.6e5a2cbc21c0 from=translated src=- shape=6293a8e5 vocab=40a7952c
-/
lemma rightExponentialDensity_le_rate
    {a : ℝ} (ha : 0 < a) (x : ℝ) :
    rightExponentialDensity a x ≤ ENNReal.ofReal a⁻¹ := by
  by_cases hx : 0 ≤ x
  · rw [rightExponentialDensity, ite_eq_left hx]
    have hexp : Real.exp (-x / a) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) ha.le
    rw [show Real.exp (-x / a) / a =
        a⁻¹ * Real.exp (-x / a) by field_simp [ha.ne']]
    rw [ENNReal.ofReal_mul (inv_pos.mpr ha).le]
    exact mul_le_of_le_one_right'
      (ENNReal.ofReal_le_one.mpr hexp)
  · rw [rightExponentialDensity, ite_eq_right hx]
    exact bot_le

/--
@isnad1 id=le.1h2v.s4.6b45e7295c8d from=translated src=- shape=6293a8e5 vocab=f25ca206
-/
lemma leftExponentialDensity_le_rate
    {b : ℝ} (hb : 0 < b) (x : ℝ) :
    leftExponentialDensity b x ≤ ENNReal.ofReal b⁻¹ :=
  rightExponentialDensity_le_rate hb (-x)

/-- The sign of one nondegenerate scaled exponential summand. -/
inductive ExpDirection
  | positive
  | negative
  deriving DecidableEq

/-- One positive or negative scaled rate-one exponential summand. -/
structure SignedExpFactor where
  /-- Whether the exponential summand is positive or negative. -/
  direction : ExpDirection
  /-- The positive scale of the summand. -/
  scale : ℝ
  scale_pos : 0 < scale

namespace SignedExpFactor

/-- The one-sided exponential density associated with a signed factor. -/
def density (F : SignedExpFactor) : ℝ → ℝ≥0∞ :=
  match F.direction with
  | .positive => rightExponentialDensity F.scale
  | .negative => leftExponentialDensity F.scale

/--
@isnad1 id=measurab.0h1v.s3.7235ea2a4de4 from=translated src=- shape=7000f90d vocab=0d0514af
-/
lemma measurable_density (F : SignedExpFactor) :
    Measurable F.density := by
  cases h : F.direction
  · simpa [density, h] using
      measurable_rightExponentialDensity F.scale
  · simpa [density, h] using
      measurable_leftExponentialDensity F.scale

/--
@isnad1 id=ne.0h2v.s3.ed178c990cb2 from=translated src=- shape=92158592 vocab=9b85c4dd
-/
lemma density_ne_top (F : SignedExpFactor) (x : ℝ) :
    F.density x ≠ ∞ := by
  cases h : F.direction
  · simpa [density, h] using
      rightExponentialDensity_ne_top F.scale x
  · simpa [density, h] using
      leftExponentialDensity_ne_top F.scale x

/--
@isnad1 id=eq.0h1v.s4.30f5c815d443 from=translated src=- shape=563353e2 vocab=0771ca87
-/
lemma lintegral_density (F : SignedExpFactor) :
    ∫⁻ x, F.density x = 1 := by
  cases h : F.direction
  · simpa [density, h] using
      lintegral_rightExponentialDensity F.scale_pos
  · simpa [density, h] using
      lintegral_leftExponentialDensity F.scale_pos

/--
@isnad1 id=le.0h2v.s4.2ee606098e5a from=translated src=- shape=761f9f87 vocab=2f78bf23
-/
lemma density_le_rate (F : SignedExpFactor) (x : ℝ) :
    F.density x ≤ ENNReal.ofReal F.scale⁻¹ := by
  cases h : F.direction
  · simpa [density, h] using
      rightExponentialDensity_le_rate F.scale_pos x
  · simpa [density, h] using
      leftExponentialDensity_le_rate F.scale_pos x

/--
@isnad1 id=translat.0h1v.s2.6d112446eb2d from=translated src=- shape=76a08d12 vocab=01c01180
-/
lemma translationTP2_density (F : SignedExpFactor) :
    TranslationTP2 F.density := by
  cases h : F.direction
  · simpa [density, h] using
      (fourPointLogConcave_rightExponentialDensity
        F.scale_pos).translationTP2
  · simpa [density, h] using
      (fourPointLogConcave_leftExponentialDensity
        F.scale_pos).translationTP2

end SignedExpFactor

/--
Density of a distinguished rate-one exponential convolved with finitely
many signed scaled exponentials.
-/
def finiteSignedExpSumDensity :
    List SignedExpFactor → ℝ → ℝ≥0∞
  | [] => rightExponentialDensity 1
  | F :: Fs =>
      densityConvolution F.density (finiteSignedExpSumDensity Fs)

/--
@isnad1 id=measurab.0h1v.s3.399a865be097 from=translated src=- shape=ed1bc477 vocab=63045690
-/
lemma measurable_finiteSignedExpSumDensity :
    ∀ Fs : List SignedExpFactor,
      Measurable (finiteSignedExpSumDensity Fs)
  | [] => measurable_rightExponentialDensity 1
  | F :: Fs =>
      measurable_densityConvolution F.measurable_density
        (measurable_finiteSignedExpSumDensity Fs)

/--
@isnad1 id=eq.0h1v.s4.fb37394cbc12 from=translated src=- shape=b0c45e65 vocab=6c3632c7
-/
lemma lintegral_finiteSignedExpSumDensity :
    ∀ Fs : List SignedExpFactor,
      ∫⁻ x, finiteSignedExpSumDensity Fs x = 1
  | [] => lintegral_rightExponentialDensity zero_lt_one
  | F :: Fs =>
      lintegral_densityConvolution_eq_one F.measurable_density
        (measurable_finiteSignedExpSumDensity Fs)
        F.lintegral_density
        (lintegral_finiteSignedExpSumDensity Fs)

/--
@isnad1 id=le.3h4v.s5.2d557f1dd3a5 from=translated src=- shape=382f8e86 vocab=1bff7749
-/
lemma densityConvolution_le_of_left_bound
    {f g : ℝ → ℝ≥0∞} (hg : Measurable g)
    {C : ℝ≥0∞} (hfC : ∀ x, f x ≤ C)
    (hgInt : ∫⁻ x, g x = 1) (x : ℝ) :
    densityConvolution f g x ≤ C := by
  rw [densityConvolution_apply]
  calc
    (∫⁻ y, f y * g (x - y)) ≤
        ∫⁻ y, C * g (x - y) := by
      exact lintegral_mono fun y ↦
        mul_le_mul_left (hfC y) (g (x - y))
    _ = C * ∫⁻ y, g (x - y) := by
      rw [lintegral_const_mul]
      fun_prop
    _ = C * ∫⁻ y, g y := by
      rw [lintegral_sub_left_eq_self]
    _ = C := by rw [hgInt, mul_one]

/--
@isnad1 id=ne.0h2v.s3.38e3cee38bcf from=translated src=- shape=d86f8732 vocab=5d656f91
-/
lemma finiteSignedExpSumDensity_ne_top :
    ∀ (Fs : List SignedExpFactor) (x : ℝ),
      finiteSignedExpSumDensity Fs x ≠ ∞
  | [], x => rightExponentialDensity_ne_top 1 x
  | F :: Fs, x => by
      apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top)
      exact densityConvolution_le_of_left_bound
        (measurable_finiteSignedExpSumDensity Fs)
        F.density_le_rate
        (lintegral_finiteSignedExpSumDensity Fs) x

/-- Finite signed exponential convolution remains translation TP2.
@isnad1 id=translat.0h1v.s2.c44a95f6a57f from=translated src=- shape=94c7f951 vocab=d7d434e6
-/
theorem translationTP2_finiteSignedExpSumDensity :
    ∀ Fs : List SignedExpFactor,
      TranslationTP2 (finiteSignedExpSumDensity Fs)
  | [] =>
      (fourPointLogConcave_rightExponentialDensity
        zero_lt_one).translationTP2
  | F :: Fs =>
      F.translationTP2_density.convolution
        F.measurable_density
        (measurable_finiteSignedExpSumDensity Fs)
        F.density_ne_top
        (finiteSignedExpSumDensity_ne_top Fs)
        (translationTP2_finiteSignedExpSumDensity Fs)

/-- The explicit four-point log-concavity needed by the local exponential
transfer step.
@isnad1 id=fourpoin.0h1v.s2.f0508ae4e81b from=translated src=- shape=94c7f951 vocab=47d8ceba
-/
theorem fourPointLogConcave_finiteSignedExpSumDensity
    (Fs : List SignedExpFactor) :
    FourPointLogConcave (finiteSignedExpSumDensity Fs) :=
  (translationTP2_finiteSignedExpSumDensity Fs).fourPointLogConcave

/--
@isnad1 id=isprobab.0h1v.s4.6b81e9ea80ce from=translated src=- shape=75f31a62 vocab=d44198fd
-/
instance instIsProbabilityMeasureWithDensityFiniteSignedExpSum
    (Fs : List SignedExpFactor) :
    IsProbabilityMeasure
      (volume.withDensity (finiteSignedExpSumDensity Fs)) where
  measure_univ := by
    rw [withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ,
      lintegral_finiteSignedExpSumDensity Fs]

/-- The same finite signed-exponential law constructed directly by
successive convolution of its absolutely continuous factor laws. -/
def finiteSignedExpSumMeasure :
    List SignedExpFactor → Measure ℝ
  | [] => volume.withDensity (rightExponentialDensity 1)
  | F :: Fs =>
      (volume.withDensity F.density) ∗
        finiteSignedExpSumMeasure Fs

/-- The recursively convolved law has exactly the explicit TP2 density.
@isnad1 id=eq.0h1v.s4.cabd34a7fff8 from=translated src=- shape=c658f770 vocab=ae1663a0
-/
theorem finiteSignedExpSumMeasure_eq_withDensity :
    ∀ Fs : List SignedExpFactor,
      finiteSignedExpSumMeasure Fs =
        volume.withDensity (finiteSignedExpSumDensity Fs)
  | [] => rfl
  | F :: Fs => by
      rw [finiteSignedExpSumMeasure, finiteSignedExpSumDensity,
        finiteSignedExpSumMeasure_eq_withDensity Fs,
        conv_withDensity_eq_withDensity_densityConvolution
          F.measurable_density
          (measurable_finiteSignedExpSumDensity Fs)]

/--
@isnad1 id=isprobab.0h1v.s3.949cb952a0d9 from=translated src=- shape=ed1bc477 vocab=28fc4d35
-/
instance instIsProbabilityMeasureFiniteSignedExpSumMeasure
    (Fs : List SignedExpFactor) :
    IsProbabilityMeasure (finiteSignedExpSumMeasure Fs) := by
  rw [finiteSignedExpSumMeasure_eq_withDensity Fs]
  infer_instance

end
end LikelihoodRatio
end Feige
