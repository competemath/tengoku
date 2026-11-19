/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Seed.MeasureTheory.Function.LpSeminorm.CompareExp
public import Tengoku.Seed.Tactic.FieldSimp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hölder's inequality in integral-power form

This form keeps the measure factor explicit when increasing the exponents
of an integral transform on a bounded parameter set.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch

/--
@isnad1 id=le.2h4v.s6.cf9d5114dec2 from=translated src=- shape=9de8560b vocab=61fd6bd0
-/
theorem lintegral_rpow_le_measure_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f) {t : ℝ} (ht : 1 ≤ t) :
    (∫⁻ x, f x ∂μ) ^ t ≤ μ univ ^ (t - 1) * ∫⁻ x, f x ^ t ∂μ := by
  have ht0 := zero_lt_one.trans_le ht
  have h := ENNReal.rpow_le_rpow
    (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ)
      (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal t by simpa using ENNReal.ofReal_le_ofReal ht)
      hf.aestronglyMeasurable) ht0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ ht0.le] at h
  have he := eLpNorm_enorm_rpow (μ := μ) (p := 1) f ht0
  simp only [one_mul, enorm_eq_self] at he
  rw [← he] at h
  have hr : (1 - 1 / t) * t = t - 1 := by field_simp
  simpa only [eLpNorm_one_eq_lintegral_enorm, enorm_eq_self,
    ENNReal.toReal_one, one_div_one, ENNReal.toReal_ofReal ht0.le,
    ← ENNReal.rpow_mul, hr, mul_comm] using h

end NKBesicovitch
