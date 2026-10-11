/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.AdamsBridge

/-!
# Adams M4

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology

noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- A concrete constant for the localized maximal-function estimate. -/
def parabolicAdamsMaximalConstant (P τ : ℝ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ (P - 1) *
    (parabolicMaximalStrongConstant P *
        ENNReal.ofReal (8 : ℝ) ^ (5 * (1 - P / τ)) +
      volume (parabolicCylinder 0 0 1) *
        (((ENNReal.ofReal (2 : ℝ)) ^ (5 * (1 - 1 / τ)) /
          volume (parabolicCylinder 0 0 1)) *
          (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P)) ^ P)

/-- A concrete constant in the parabolic Adams inequality. -/
def parabolicAdamsPotentialConstant (β P τ : ℝ) : ℝ≥0∞ :=
  let lam : ℝ := 1 - β * τ / 5
  let theta : ℝ := β * τ / 5
  let s : ℝ := P / lam
  let D : ℝ≥0∞ := volume (parabolicCylinder 0 0 1) ^ (1 - 1 / P)
  (((parabolicHedbergNearConstant β + parabolicTailKernelConstant β τ) *
      D ^ theta) ^ s * parabolicAdamsMaximalConstant P τ) ^ (1 / s)

private theorem test_ofReal_toReal_rpow_le
    {p : ℝ} (hp : 0 ≤ p) (G : ParabolicPoint → ℝ≥0∞) (w : ParabolicPoint) :
    ENNReal.ofReal |(G w).toReal| ^ p ≤ G w ^ p := by
  have hnonneg : 0 ≤ (G w).toReal := ENNReal.toReal_nonneg
  by_cases htop : G w = ∞
  · rcases hp.eq_or_lt with rfl | hp
    · simp [htop]
    · rw [htop, ENNReal.toReal_top, abs_zero, ENNReal.ofReal_zero,
        ENNReal.zero_rpow_of_pos hp, ENNReal.top_rpow_of_pos hp]
      exact bot_le
  · rw [abs_of_nonneg hnonneg, ENNReal.ofReal_toReal htop]

/-- The real-valued Morrey cell is controlled by the corresponding ENNReal integral. -/
theorem morreyCell_toReal_le_lintegral_rpow
    {p q : ℝ} (hp : 0 ≤ p) {G : ParabolicPoint → ℝ≥0∞}
    {z : ParabolicPoint} {r : ℝ} :
    morreyCell p q (fun w ↦ (G w).toReal) z r ≤
      (ENNReal.ofReal r) ^ (-(5 * (1 - p / q) / p)) *
        (∫⁻ w in parabolicCylinder z.1 z.2 r, G w ^ p) ^ (1 / p) := by
  unfold morreyCell cylinderPowerIntegral
  apply mul_le_mul_right
  apply ENNReal.rpow_le_rpow
  · apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (by
      rw [parabolicCylinder]
      exact (vec3Ball_measurable z.1 r).prod measurableSet_Ioc)] with w hw
    exact test_ofReal_toReal_rpow_le hp G w
  · exact one_div_nonneg.mpr hp

end CKN.Foundation.Parabolic.Morrey
