/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku

/-!
# Likelihood-ratio comparison for exponential convolutions

This file formalizes the four-point and double-integral parts of the local
exponential transfer step used in the proof of Theorem 2.1.  We use an
`ℝ≥0∞`-valued density so that Tonelli and monotone integration require no
auxiliary integrability assumptions.
-/

@[expose] public section

open MeasureTheory Real Set
open scoped ENNReal

namespace Feige

namespace LikelihoodRatio

/-- The one-dimensional four-point form of log-concavity.

For nonnegative functions on the line this is the exact multiplicative
inequality needed below.  Ordinary log-concave densities with convex
support satisfy this property by concavity of `log f`.
-/
def FourPointLogConcave (f : ℝ → ℝ≥0∞) : Prop :=
  ∀ ⦃r p q s : ℝ⦄,
    r ≤ p → p ≤ q → r ≤ s → s ≤ q → p + s = r + q →
      f r * f q ≤ f p * f s

/-- The geometric specialization of the four-point inequality used in the
likelihood-ratio comparison.
@isnad1 id=le.6h7v.s7.3c097e46a66c from=translated src=- shape=510c9a3c vocab=a0c761f4
-/
theorem four_point_exponential_shifts
    {f : ℝ → ℝ≥0∞} (hf : FourPointLogConcave f)
    {a b x y s t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hxy : y ≤ x) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    f (x + b * t) * f (y - a * s) ≤
      f (x - a * s) * f (y + b * t) := by
  have h := hf
    (r := y - a * s) (p := x - a * s)
    (q := x + b * t) (s := y + b * t)
    (by linarith [mul_nonneg ha hs])
    (by linarith [mul_nonneg ha hs, mul_nonneg hb ht])
    (by linarith [mul_nonneg ha hs, mul_nonneg hb ht])
    (by linarith)
    (by ring)
  simpa [mul_comm] using h

/-- The exponential convolution weight. -/
noncomputable def expWeight (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (exp (-s))

/--
@isnad1 id=measurab.0h0v.s2.cdc86f266d12 from=translated src=- shape=54c8eceb vocab=1f62f5f5
-/
theorem measurable_expWeight : Measurable expWeight := by
  unfold expWeight
  fun_prop

/-- The positive-shift density `f₊`, expressed as a nonnegative integral. -/
noncomputable def fPlus (f : ℝ → ℝ≥0∞) (a x : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ici 0, f (x - a * s) * expWeight s

/-- The negative-shift density `f₋`, expressed as a nonnegative integral. -/
noncomputable def fMinus (f : ℝ → ℝ≥0∞) (b x : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ici 0, f (x + b * t) * expWeight t

/-- Monotone likelihood-ratio inequality for the two shift densities.

The proof expands both products as double nonnegative integrals and
applies the four-point inequality pointwise.  Because all functions are
`ℝ≥0∞`-valued, Tonelli is unconditional.
@isnad1 id=le.5h5v.s6.125f7d605c1c from=translated src=- shape=fc763b8a vocab=e8467f1d
-/
theorem fPlus_mul_fMinus_mono
    {f : ℝ → ℝ≥0∞} (hfmeas : Measurable f)
    (hflc : FourPointLogConcave f)
    {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hxy : y ≤ x) :
    fMinus f b x * fPlus f a y ≤
      fPlus f a x * fMinus f b y := by
  have hw : Measurable expWeight := measurable_expWeight
  have hPlusX : Measurable (fun s : ℝ => f (x - a * s) * expWeight s) := by
    fun_prop
  have hMinusY : Measurable (fun t : ℝ => f (y + b * t) * expWeight t) := by
    fun_prop
  have hPlusY : Measurable (fun s : ℝ => f (y - a * s) * expWeight s) := by
    fun_prop
  have hMinusX : Measurable (fun t : ℝ => f (x + b * t) * expWeight t) := by
    fun_prop
  rw [mul_comm (fMinus f b x), fPlus, fMinus,
    ← lintegral_lintegral_mul hPlusY.aemeasurable hMinusX.aemeasurable]
  rw [fPlus, fMinus,
    ← lintegral_lintegral_mul hPlusX.aemeasurable hMinusY.aemeasurable]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  have hpoint := four_point_exponential_shifts hflc ha hb hxy hs ht
  calc
    (f (y - a * s) * expWeight s) *
        (f (x + b * t) * expWeight t) =
        (f (x + b * t) * f (y - a * s)) *
          (expWeight s * expWeight t) := by ac_rfl
    _ ≤ (f (x - a * s) * f (y + b * t)) *
          (expWeight s * expWeight t) :=
      mul_le_mul_left hpoint _
    _ = (f (x - a * s) * expWeight s) *
        (f (y + b * t) * expWeight t) := by ac_rfl

/-- Measurability of the positive exponential convolution.
@isnad1 id=measurab.1h2v.s4.bd00c1bc098d from=translated src=- shape=4535375a vocab=f88651d6
-/
theorem measurable_fPlus {f : ℝ → ℝ≥0∞} (hf : Measurable f) (a : ℝ) :
    Measurable (fPlus f a) := by
  unfold fPlus
  apply Measurable.lintegral_prod_right
  exact (hf.comp (measurable_fst.sub (measurable_const.mul measurable_snd))).mul
    (measurable_expWeight.comp measurable_snd)

/-- Measurability of the negative exponential convolution.
@isnad1 id=measurab.1h2v.s4.81c24167cc03 from=translated src=- shape=4535375a vocab=0114c433
-/
theorem measurable_fMinus {f : ℝ → ℝ≥0∞} (hf : Measurable f) (b : ℝ) :
    Measurable (fMinus f b) := by
  unfold fMinus
  apply Measurable.lintegral_prod_right
  exact (hf.comp (measurable_fst.add (measurable_const.mul measurable_snd))).mul
    (measurable_expWeight.comp measurable_snd)

/-- The lower-tail transfer functional `u` for a nonnegative density `g`. -/
noncomputable def uIntegral (g : ℝ → ℝ≥0∞) (d : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ici 0, g x * ENNReal.ofReal (exp (-x / d))

/-- The upper-tail transfer functional `v` for a nonnegative density `g`. -/
noncomputable def vIntegral (g : ℝ → ℝ≥0∞) (c : ℝ) : ℝ≥0∞ :=
  ∫⁻ y in Iio 0, g y * ENNReal.ofReal (exp (y / c))

/-- Integrating the likelihood-ratio comparison against the two exponential
weights gives `u₋ v₊ ≤ u₊ v₋`.
@isnad1 id=le.4h5v.s6.ea0507a81c16 from=translated src=- shape=429696b4 vocab=217e155d
-/
theorem uMinus_mul_vPlus_le
    {f : ℝ → ℝ≥0∞} (hfmeas : Measurable f)
    (hflc : FourPointLogConcave f)
    {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    uIntegral (fMinus f b) d * vIntegral (fPlus f a) c ≤
      uIntegral (fPlus f a) d * vIntegral (fMinus f b) c := by
  have hfp : Measurable (fPlus f a) := measurable_fPlus hfmeas a
  have hfm : Measurable (fMinus f b) := measurable_fMinus hfmeas b
  have huP : Measurable
      (fun x : ℝ => fPlus f a x * ENNReal.ofReal (exp (-x / d))) := by
    fun_prop
  have huM : Measurable
      (fun x : ℝ => fMinus f b x * ENNReal.ofReal (exp (-x / d))) := by
    fun_prop
  have hvP : Measurable
      (fun y : ℝ => fPlus f a y * ENNReal.ofReal (exp (y / c))) := by
    fun_prop
  have hvM : Measurable
      (fun y : ℝ => fMinus f b y * ENNReal.ofReal (exp (y / c))) := by
    fun_prop
  rw [uIntegral, vIntegral,
    ← lintegral_lintegral_mul huM.aemeasurable hvP.aemeasurable]
  rw [uIntegral, vIntegral,
    ← lintegral_lintegral_mul huP.aemeasurable hvM.aemeasurable]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
  have hmlr := fPlus_mul_fMinus_mono hfmeas hflc ha hb (le_trans hy.le hx)
  calc
    (fMinus f b x * ENNReal.ofReal (exp (-x / d))) *
        (fPlus f a y * ENNReal.ofReal (exp (y / c))) =
      (fMinus f b x * fPlus f a y) *
        (ENNReal.ofReal (exp (-x / d)) *
          ENNReal.ofReal (exp (y / c))) := by ac_rfl
    _ ≤ (fPlus f a x * fMinus f b y) *
        (ENNReal.ofReal (exp (-x / d)) *
          ENNReal.ofReal (exp (y / c))) :=
      mul_le_mul_left hmlr _
    _ = (fPlus f a x * ENNReal.ofReal (exp (-x / d))) *
        (fMinus f b y * ENNReal.ofReal (exp (y / c))) := by ac_rfl

/-- Algebraic bridge from the cross-product comparison to monotonicity
of `θ = u / (u + v)`.  This real-valued form is convenient after
converting finite probability integrals from `ℝ≥0∞`.
@isnad1 id=le.3h4v.s6.e2c7d9b5cd11 from=translated src=- shape=3d649366 vocab=b1824736
-/
theorem theta_le_theta_of_cross
    {uPlus uMinus vPlus vMinus : ℝ}
    (hwPlus : 0 < uPlus + vPlus)
    (hwMinus : 0 < uMinus + vMinus)
    (hcross : uMinus * vPlus ≤ uPlus * vMinus) :
    uMinus / (uMinus + vMinus) ≤
      uPlus / (uPlus + vPlus) := by
  rw [div_le_div_iff₀ hwMinus hwPlus]
  nlinarith

end LikelihoodRatio

end Feige
