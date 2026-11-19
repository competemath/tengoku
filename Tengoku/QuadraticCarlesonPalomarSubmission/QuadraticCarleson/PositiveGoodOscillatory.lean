/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.OscillatoryReductionMaximal
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.PositiveHighHeightConvergence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# All-height oscillatory L² estimates

Height zero and the strict positive-height tail give a summable L² bound.
The actual full-real and lacunary oscillatory suprema are dominated by this
common measurable majorant. Its Markov estimate controls outer level sets
without a measurability assumption on the real supremum.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace PositiveGoodOscillatory

open OscillatoryReduction PositiveHighHeightEstimate

noncomputable def allHeightMajorant (b : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ∑' r : ℕ, paperFixedHeightQuadraticMaximal r b x

/--
@isnad1 id=eq.0h2v.s5.86737bb7ce72 from=translated src=- shape=22d0a7be vocab=511109d1
-/
theorem allHeightMajorant_eq_zero_add_tail (b : ℝ → ℂ) (x : ℝ) :
    allHeightMajorant b x = paperFixedHeightQuadraticMaximal 0 b x +
      highHeightMajorant 0 b x := by
  unfold allHeightMajorant highHeightMajorant
  simpa only [zero_add] using
    (tsum_eq_zero_add' (f := fun r ↦ paperFixedHeightQuadraticMaximal r b x) ENNReal.summable)

/--
@isnad1 id=measurab.1h1v.s6.ecf5643ee0ae from=translated src=- shape=6c5cb9b0 vocab=88673ffe
-/
theorem measurable_allHeightMajorant {b : ℝ → ℂ} (hb : MemLp b 2) :
    Measurable (allHeightMajorant b) :=
  Measurable.tsum (fun r ↦ measurable_paperFixedHeightQuadraticMaximal r hb)

noncomputable def allHeightL2Constant : ℝ≥0∞ :=
  ENNReal.ofReal fixedHeightL2DecayConstant + highHeightTailConstant

/--
@isnad1 id=lt.0h0v.s3.fd81e893a9f2 from=translated src=- shape=f463f024 vocab=00b1a215
-/
theorem allHeightL2Constant_lt_top : allHeightL2Constant < ∞ :=
  ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, highHeightTailConstant_lt_top⟩

/--
@isnad1 id=eq.0h0v.s5.9be87d3dec30 from=translated src=- shape=3f97b58b vocab=a3408b74
-/
theorem tsum_fixedHeightDecay_allHeights :
    (∑' r : ℕ, ENNReal.ofReal (fixedHeightL2DecayConstant *
      (2 : ℝ) ^ (-(r : ℝ) / 10))) = allHeightL2Constant := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  have ht := tsum_fixedHeightDecay_highHeight 0
  simp only [Nat.cast_zero, neg_zero, zero_div, Real.rpow_zero, ENNReal.ofReal_one,
    mul_one, zero_add] at ht
  simpa only [Nat.cast_zero, neg_zero, zero_div, Real.rpow_zero, mul_one,
    allHeightL2Constant] using congrArg (fun s ↦ ENNReal.ofReal fixedHeightL2DecayConstant + s) ht

/--
@isnad1 id=le.1h1v.s7.6761ebf4ba3b from=translated src=- shape=ebece45f vocab=279bb724
-/
theorem allHeightMajorant_eLpNorm_le {b : ℝ → ℂ} (hb : MemLp b 2) :
    eLpNorm (allHeightMajorant b) 2 ≤ allHeightL2Constant * eLpNorm b 2 := by
  have hp (r : ℕ) : eLpNorm (paperFixedHeightQuadraticMaximal r b) 2 ≤
      ENNReal.ofReal (fixedHeightL2DecayConstant * (2 : ℝ) ^ (-(r : ℝ) / 10)) *
        eLpNorm b 2 := paperFixedHeightQuadraticMaximal_eLpNorm_decay r hb
  have hs := ENNReal.tsum_le_tsum hp
  rw [ENNReal.tsum_mul_right, tsum_fixedHeightDecay_allHeights] at hs
  exact (eLpNorm_tsum_two_le (fun r ↦ paperFixedHeightQuadraticMaximal r b)
    (fun r ↦ measurable_paperFixedHeightQuadraticMaximal r hb)).trans hs

/--
@isnad1 id=memlp.1h1v.s6.1b9a7f3e7c48 from=translated src=- shape=cd5460d0 vocab=6011d4cf
-/
theorem memLp_allHeightMajorant {b : ℝ → ℂ} (hb : MemLp b 2) :
    MemLp (allHeightMajorant b) 2 :=
  ⟨(measurable_allHeightMajorant hb).aestronglyMeasurable,
    (allHeightMajorant_eLpNorm_le hb).trans_lt
      (ENNReal.mul_lt_top allHeightL2Constant_lt_top hb.eLpNorm_lt_top)⟩

/--
@isnad1 id=le.0h2v.s3.475379ec0d5d from=translated src=- shape=8b3ecf9b vocab=72b09310
-/
theorem paperOscillatoryMaximal_le_majorant (b : ℝ → ℂ) (x : ℝ) :
    paperOscillatoryMaximal b x ≤ allHeightMajorant b x := by
  apply iSup_le
  intro lam
  apply enorm_tsum_le_tsum_enorm.trans
  apply ENNReal.tsum_le_tsum
  intro r
  exact le_iSup (fun μ : {μ : ℝ // μ ≠ 0} ↦ ‖∫ t, b (x - t) *
    (dyadicPsi (oscillatoryScaleIndex μ.1 r μ.2) t : ℂ) * phase (μ.1 * t ^ 2)‖ₑ) lam

/-- The real-modulation oscillatory operator uses the exact series from
the principal-value reduction.
@isnad1 id=le.1h1v.s7.4e406458f1d1 from=translated src=- shape=ebece45f vocab=efe26403
-/
theorem paperOscillatoryMaximal_eLpNorm_le {b : ℝ → ℂ} (hb : MemLp b 2) :
    eLpNorm (paperOscillatoryMaximal b) 2 ≤ allHeightL2Constant * eLpNorm b 2 := by
  apply (eLpNorm_mono_enorm (f := paperOscillatoryMaximal b) (g := allHeightMajorant b)
    (fun x ↦ paperOscillatoryMaximal_le_majorant b x)).trans
  exact allHeightMajorant_eLpNorm_le hb

/-- One null set works simultaneously for every nonzero real modulation.
@isnad1 id=eventual.1h1v.s7.0082423d1c10 from=translated src=- shape=d5ecb784 vocab=05cf6c9e
-/
theorem ae_summable_norm_oscillatoryIntegrals {b : ℝ → ℂ} (hb : MemLp b 2) :
    ∀ᵐ x, ∀ lam : {lam : ℝ // lam ≠ 0}, Summable (fun r : ℕ ↦
      ‖∫ t, b (x - t) * (dyadicPsi (oscillatoryScaleIndex lam.1 r lam.2) t : ℂ) *
        phase (lam.1 * t ^ 2)‖) := by
  filter_upwards [ae_summable_norm_highHeightIntegrals 0 hb] with x hx
  intro lam
  apply (summable_nat_add_iff 1).mp
  simpa only [zero_add] using hx lam

/--
@isnad1 id=le.1h1v.s7.563fd5705990 from=translated src=- shape=02f6e1b5 vocab=a675ad6f
-/
theorem allHeightMajorant_sq_lintegral_le {b : ℝ → ℂ} (hb : MemLp b 2) :
    (∫⁻ x, allHeightMajorant b x ^ 2) ≤
      allHeightL2Constant ^ 2 * ∫⁻ x, ‖b x‖ₑ ^ 2 := by
  have h := pow_le_pow_left₀ bot_le (allHeightMajorant_eLpNorm_le hb) 2
  simpa only [mul_pow, eLpNorm_two_sq_lintegral, enorm_eq_self] using h

/-- Chebyshev for the common measurable majorant, with arbitrary threshold.
@isnad1 id=le.1h2v.s8.16a9dcf5ff4c from=translated src=- shape=5e06a9fe vocab=e5328afa
-/
theorem paperOscillatoryMaximal_levelSet_mul_le {b : ℝ → ℂ} (hb : MemLp b 2)
    (a : ℝ≥0∞) :
    a ^ 2 * volume {x | a < paperOscillatoryMaximal b x} ≤
      allHeightL2Constant ^ 2 * ∫⁻ x, ‖b x‖ₑ ^ 2 := by
  have hset : {x | a < paperOscillatoryMaximal b x} ⊆ {x | a ^ 2 ≤ allHeightMajorant b x ^ 2} := by
    intro x hx
    exact pow_le_pow_left₀ bot_le (hx.trans_le (paperOscillatoryMaximal_le_majorant b x)).le 2
  apply (mul_le_mul' le_rfl (measure_mono hset)).trans
  apply (mul_meas_ge_le_lintegral (μ := volume)
    ((measurable_allHeightMajorant hb).pow_const 2) (a ^ 2)).trans
  exact allHeightMajorant_sq_lintegral_le hb

noncomputable def paperLacunaryOscillatoryMaximal (b : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ m : ℤ, ‖paperOscillatoryAction (dyadicModulation m) (dyadicModulation_pos m).ne' b x‖ₑ

/--
@isnad1 id=le.0h2v.s3.4911a9f6f522 from=translated src=- shape=8b3ecf9b vocab=4a19c0ac
-/
theorem paperLacunaryOscillatoryMaximal_le_full (b : ℝ → ℂ) (x : ℝ) :
    paperLacunaryOscillatoryMaximal b x ≤ paperOscillatoryMaximal b x := by
  apply iSup_le
  intro m
  exact le_iSup (fun lam : {lam : ℝ // lam ≠ 0} ↦ ‖paperOscillatoryAction lam.1 lam.2 b x‖ₑ)
    ⟨dyadicModulation m, (dyadicModulation_pos m).ne'⟩

/--
@isnad1 id=le.1h1v.s7.35fc6f4674f9 from=translated src=- shape=ebece45f vocab=8fab2713
-/
theorem paperLacunaryOscillatoryMaximal_eLpNorm_le {b : ℝ → ℂ} (hb : MemLp b 2) :
    eLpNorm (paperLacunaryOscillatoryMaximal b) 2 ≤ allHeightL2Constant * eLpNorm b 2 := by
  exact (eLpNorm_mono_enorm (f := paperLacunaryOscillatoryMaximal b)
    (g := paperOscillatoryMaximal b) (fun x ↦ paperLacunaryOscillatoryMaximal_le_full b x)).trans
      (paperOscillatoryMaximal_eLpNorm_le hb)

/--
@isnad1 id=le.1h2v.s8.f2ec932bf29c from=translated src=- shape=5e06a9fe vocab=e13dfd59
-/
theorem paperLacunaryOscillatoryMaximal_levelSet_mul_le {b : ℝ → ℂ} (hb : MemLp b 2)
    (a : ℝ≥0∞) :
    a ^ 2 * volume {x | a < paperLacunaryOscillatoryMaximal b x} ≤
      allHeightL2Constant ^ 2 * ∫⁻ x, ‖b x‖ₑ ^ 2 := by
  apply (mul_le_mul' le_rfl (measure_mono (fun x hx ↦
    hx.trans_le (paperLacunaryOscillatoryMaximal_le_full b x)))).trans
  exact paperOscillatoryMaximal_levelSet_mul_le hb a

end PositiveGoodOscillatory
end QuadraticCarleson
