/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.PositiveGoodOscillatory
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.CalderonZygmundDyadicStopping
import Tengoku.Seed.MeasureTheory.Function.L2Space

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The actual stopping-time good contribution

The stopping construction itself proves `∫ |g|² ≤ 5 ∫ |f|`. Combining it
with the genuine all-height oscillatory L² estimate closes the good-part
level-set estimate, both for full real and for dyadic modulations.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace PositiveGoodOscillatory

open OscillatoryReduction CalderonZygmundDyadicStopping

/--
@isnad1 id=memlp.1h1v.s6.5b33f536a86f from=translated src=- shape=669ddec9 vocab=39f1089b
-/
theorem memLp_stoppingGoodPart {f : ℝ → ℂ} (hf : Integrable f) :
    MemLp (stoppingGoodPart f) 2 :=
  (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_stoppingGoodPart hf)).mpr
    (integrable_sq_norm_stoppingGoodPart hf)

/--
@isnad1 id=le.1h1v.s7.2ea5e5c33c18 from=translated src=- shape=4c2af4b7 vocab=414d4cdc
-/
theorem lintegral_sq_enorm_stoppingGoodPart_le {f : ℝ → ℂ} (hf : Integrable f) :
    (∫⁻ x, ‖stoppingGoodPart f x‖ₑ ^ 2) ≤ 5 * ∫⁻ x, ‖f x‖ₑ := by
  have heq : (∫⁻ x, ‖stoppingGoodPart f x‖ₑ ^ 2) =
      ENNReal.ofReal (∫ x, ‖stoppingGoodPart f x‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_sq_norm_stoppingGoodPart hf)
      (Filter.Eventually.of_forall fun x ↦ sq_nonneg ‖stoppingGoodPart f x‖)]
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hmass : ENNReal.ofReal (∫ x, ‖f x‖) = ∫⁻ x, ‖f x‖ₑ := by
    simpa only [ofReal_norm] using ofReal_integral_eq_lintegral_ofReal hf.norm
      (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
  calc
    _ = ENNReal.ofReal (∫ x, ‖stoppingGoodPart f x‖ ^ 2) := heq
    _ ≤ ENNReal.ofReal (5 * ∫ x, ‖f x‖) := ENNReal.ofReal_le_ofReal
      (integral_sq_norm_stoppingGoodPart_le_five_l1 hf)
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5), hmass]; norm_num

noncomputable def stoppingGoodOscillatoryConstant : ℝ≥0∞ := 5 * allHeightL2Constant ^ 2

/--
@isnad1 id=lt.0h0v.s3.8d473a98f2af from=translated src=- shape=f463f024 vocab=3417b4a2
-/
theorem stoppingGoodOscillatoryConstant_lt_top : stoppingGoodOscillatoryConstant < ∞ :=
  ENNReal.mul_lt_top (by finiteness) (ENNReal.pow_lt_top allHeightL2Constant_lt_top)

/-- A measurable squared-L² majorant for the actual good-part oscillatory
operator, bounded directly by the original input's L¹ mass.
@isnad1 id=le.1h1v.s7.e075980efa78 from=translated src=- shape=1fa58261 vocab=2a0dfde2
-/
theorem stoppingGoodPart_majorant_sq_lintegral_le {f : ℝ → ℂ} (hf : Integrable f) :
    (∫⁻ x, allHeightMajorant (stoppingGoodPart f) x ^ 2) ≤
      stoppingGoodOscillatoryConstant * ∫⁻ x, ‖f x‖ₑ := by
  apply (allHeightMajorant_sq_lintegral_le (memLp_stoppingGoodPart hf)).trans
  apply (mul_le_mul' le_rfl (lintegral_sq_enorm_stoppingGoodPart_le hf)).trans_eq
  unfold stoppingGoodOscillatoryConstant
  ring

/--
@isnad1 id=le.1h1v.s7.105984e6e749 from=translated src=- shape=7b1e2ee9 vocab=8e24420c
-/
theorem stoppingGoodPart_oscillatory_eLpNorm_sq_le {f : ℝ → ℂ} (hf : Integrable f) :
    eLpNorm (paperOscillatoryMaximal (stoppingGoodPart f)) 2 ^ 2 ≤
      stoppingGoodOscillatoryConstant * ∫⁻ x, ‖f x‖ₑ := by
  have h := pow_le_pow_left₀ bot_le
    (paperOscillatoryMaximal_eLpNorm_le (memLp_stoppingGoodPart hf)) 2
  rw [mul_pow, eLpNorm_two_sq_lintegral (stoppingGoodPart f)] at h
  apply h.trans
  apply (mul_le_mul' le_rfl (lintegral_sq_enorm_stoppingGoodPart_le hf)).trans_eq
  unfold stoppingGoodOscillatoryConstant
  ring

/--
@isnad1 id=le.1h2v.s7.9cd51e6e9787 from=translated src=- shape=51427da7 vocab=0201a24f
-/
theorem stoppingGoodPart_oscillatory_levelSet_mul_le {f : ℝ → ℂ} (hf : Integrable f)
    (a : ℝ≥0∞) :
    a ^ 2 * volume {x | a < paperOscillatoryMaximal (stoppingGoodPart f) x} ≤
      stoppingGoodOscillatoryConstant * ∫⁻ x, ‖f x‖ₑ := by
  apply (paperOscillatoryMaximal_levelSet_mul_le (memLp_stoppingGoodPart hf) a).trans
  apply (mul_le_mul' le_rfl (lintegral_sq_enorm_stoppingGoodPart_le hf)).trans_eq
  unfold stoppingGoodOscillatoryConstant
  ring

/-- The full-real good contribution at the normalized endpoint threshold.
@isnad1 id=le.1h1v.s7.88d012226d7b from=translated src=- shape=78cc982b vocab=de85af4f
-/
theorem stoppingGoodPart_oscillatory_levelSet_le {f : ℝ → ℂ} (hf : Integrable f) :
    volume {x | 1 < paperOscillatoryMaximal (stoppingGoodPart f) x} ≤
      stoppingGoodOscillatoryConstant * ∫⁻ x, ‖f x‖ₑ := by
  simpa only [one_pow, one_mul] using stoppingGoodPart_oscillatory_levelSet_mul_le hf 1

/--
@isnad1 id=le.1h1v.s7.78cc2122750f from=translated src=- shape=7b1e2ee9 vocab=833c6990
-/
theorem stoppingGoodPart_lacunaryOscillatory_eLpNorm_sq_le
    {f : ℝ → ℂ} (hf : Integrable f) :
    eLpNorm (paperLacunaryOscillatoryMaximal (stoppingGoodPart f)) 2 ^ 2 ≤
      stoppingGoodOscillatoryConstant * ∫⁻ x, ‖f x‖ₑ := by
  have h := pow_le_pow_left₀ bot_le
    (paperLacunaryOscillatoryMaximal_eLpNorm_le (memLp_stoppingGoodPart hf)) 2
  rw [mul_pow, eLpNorm_two_sq_lintegral (stoppingGoodPart f)] at h
  apply h.trans
  apply (mul_le_mul' le_rfl (lintegral_sq_enorm_stoppingGoodPart_le hf)).trans_eq
  unfold stoppingGoodOscillatoryConstant
  ring

/--
@isnad1 id=le.1h2v.s7.0f3f2e629426 from=translated src=- shape=51427da7 vocab=1b21689c
-/
theorem stoppingGoodPart_lacunaryOscillatory_levelSet_mul_le
    {f : ℝ → ℂ} (hf : Integrable f) (a : ℝ≥0∞) :
    a ^ 2 * volume {x | a < paperLacunaryOscillatoryMaximal (stoppingGoodPart f) x} ≤
      stoppingGoodOscillatoryConstant * ∫⁻ x, ‖f x‖ₑ := by
  apply (paperLacunaryOscillatoryMaximal_levelSet_mul_le (memLp_stoppingGoodPart hf) a).trans
  apply (mul_le_mul' le_rfl (lintegral_sq_enorm_stoppingGoodPart_le hf)).trans_eq
  unfold stoppingGoodOscillatoryConstant
  ring

/-- The dyadic-modulation good contribution obeys the same endpoint estimate.
@isnad1 id=le.1h1v.s7.c94d1bb7a6b4 from=translated src=- shape=78cc982b vocab=30c21474
-/
theorem stoppingGoodPart_lacunaryOscillatory_levelSet_le {f : ℝ → ℂ} (hf : Integrable f) :
    volume {x | 1 < paperLacunaryOscillatoryMaximal (stoppingGoodPart f) x} ≤
      stoppingGoodOscillatoryConstant * ∫⁻ x, ‖f x‖ₑ := by
  simpa only [one_pow, one_mul] using stoppingGoodPart_lacunaryOscillatory_levelSet_mul_le hf 1

/-- The actual good-part series converges absolutely outside one null set,
simultaneously for all nonzero real modulations.
@isnad1 id=eventual.1h1v.s7.188e3ce124c8 from=translated src=- shape=8a640f40 vocab=201e7e53
-/
theorem ae_summable_norm_stoppingGoodPart_oscillatoryIntegrals
    {f : ℝ → ℂ} (hf : Integrable f) :
    ∀ᵐ x, ∀ lam : {lam : ℝ // lam ≠ 0}, Summable (fun r : ℕ ↦
      ‖∫ t, stoppingGoodPart f (x - t) *
        (dyadicPsi (oscillatoryScaleIndex lam.1 r lam.2) t : ℂ) * phase (lam.1 * t ^ 2)‖) :=
  ae_summable_norm_oscillatoryIntegrals (memLp_stoppingGoodPart hf)

end PositiveGoodOscillatory
end QuadraticCarleson
