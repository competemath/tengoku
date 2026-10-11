/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.AdamsEndpoints

/-!
# Adams Bridge

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology

noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- The cylinder integral is bounded by the Morrey seminorm at every scale. -/
theorem cylinderPowerIntegral_le_morreyNorm_pow
    {p q : ℝ} (hp : 0 < p) {f : ParabolicPoint → ℝ}
    (_ : AEMeasurable f volume) {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    cylinderPowerIntegral p f z r ≤
      (ENNReal.ofReal r) ^ (5 * (1 - p / q)) * morreyNorm p q f ^ p := by
  let A : ℝ≥0∞ := ENNReal.ofReal r
  let I : ℝ≥0∞ := cylinderPowerIntegral p f z r
  let α : ℝ := 5 * (1 - p / q)
  have hA0 : A ≠ 0 := by
    dsimp [A]
    exact (ENNReal.ofReal_pos.mpr hr).ne'
  have hAtop : A ≠ ∞ := by
    dsimp [A]
    exact ENNReal.ofReal_ne_top
  have hcell : morreyCell p q f z r ≤ morreyNorm p q f := by
    unfold morreyNorm
    exact le_iSup_of_le z (le_iSup_of_le ⟨r, hr⟩ le_rfl)
  have hpow' := ENNReal.rpow_le_rpow hcell hp.le
  rw [morreyCell_eq] at hpow'
  have hpow_raw : ((A ^ (-α / p) * (I ^ (1 / p))) ^ p) ≤
      morreyNorm p q f ^ p := by
    have hexp : -(5 * (1 - p / q) / p) = -(5 * (1 - p / q)) / p := by
      ring_nf
    rw [hexp] at hpow'
    simpa [A, I, α] using hpow'
  have hpow_eq : (A ^ (-α / p) * (I ^ (1 / p))) ^ p =
      A ^ (-α) * I := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul]
    have hα : (-α / p) * p = -α := by
      field_simp [hp.ne']
    have hpone : (1 / p) * p = 1 := by
      field_simp [hp.ne']
    rw [hα, hpone, ENNReal.rpow_one]
  have hpow : A ^ (-α) * I ≤ morreyNorm p q f ^ p := by
    rw [← hpow_eq]
    exact hpow_raw
  have hscale : A ^ α * (A ^ (-α) * I) = I := by
    calc
      A ^ α * (A ^ (-α) * I) = (A ^ α * A ^ (-α)) * I := by ac_rfl
      _ = A ^ (α + (-α)) * I := by
        rw [← ENNReal.rpow_add _ _ hA0 hAtop]
      _ = I := by rw [add_neg_cancel, ENNReal.rpow_zero, one_mul]
  have hmul := mul_le_mul_left hpow (A ^ α)
  have hmul' : A ^ α * (A ^ (-α) * I) ≤
      A ^ α * morreyNorm p q f ^ p := by
    simpa [mul_comm] using hmul
  rw [hscale] at hmul'
  calc
    I ≤ A ^ α * morreyNorm p q f ^ p := hmul'
    _ = (ENNReal.ofReal r) ^ (5 * (1 - p / q)) * morreyNorm p q f ^ p := by
      rfl

/-- The maximal function is subadditive on nonnegative measurable data. -/
theorem parabolicMaximalFunction_add_le'
    {F G : ParabolicPoint → ℝ≥0∞} (hF : Measurable F) (_ : Measurable G)
    (z : ParabolicPoint) :
    parabolicMaximalFunction (F + G) z ≤
      parabolicMaximalFunction F z + parabolicMaximalFunction G z := by
  rw [parabolicMaximalFunction, parabolicMaximalFunction]
  refine iSup_le fun c ↦ iSup_le fun r ↦ ?_
  by_cases hz : z ∈ Metric.ball c r
  · simp only [indicator_of_mem hz]
    calc
      ⨍⁻ y in Metric.ball c r, (F + G) y ∂volume ≤
          ⨍⁻ y in Metric.ball c r, F y ∂volume +
            ⨍⁻ y in Metric.ball c r, G y ∂volume := by
        simp only [Pi.add_apply]
        rw [setLAverage_eq, setLAverage_eq, setLAverage_eq, lintegral_add_left
          (μ := volume.restrict (Metric.ball c r)) hF, ENNReal.add_div]
      _ ≤ parabolicMaximalFunction F z + parabolicMaximalFunction G z := by
        gcongr
        · calc
            ⨍⁻ y in Metric.ball c r, F y ∂volume =
                (Metric.ball c r).indicator
                  (fun _ ↦ ⨍⁻ y in Metric.ball c r, F y ∂volume) z :=
              (indicator_of_mem hz (fun _ ↦
                ⨍⁻ y in Metric.ball c r, F y ∂volume)).symm
            _ ≤ parabolicMaximalFunction F z := by
              exact le_iSup₂_of_le c r le_rfl
        · calc
            ⨍⁻ y in Metric.ball c r, G y ∂volume =
                (Metric.ball c r).indicator
                  (fun _ ↦ ⨍⁻ y in Metric.ball c r, G y ∂volume) z :=
              (indicator_of_mem hz (fun _ ↦
                ⨍⁻ y in Metric.ball c r, G y ∂volume)).symm
            _ ≤ parabolicMaximalFunction G z := by
              exact le_iSup₂_of_le c r le_rfl
  · change (Metric.ball c r).indicator _ z ≤ _
    rw [indicator_of_notMem hz]
    exact bot_le

end CKN.Foundation.Parabolic.Morrey
