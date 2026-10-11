/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Kernel

/-!
# Tail

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology

noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- The absolute integral on a positive cylinder is controlled by its Morrey norm. -/
theorem cylinderAbsIntegral_le_morreyNorm {q : ℝ} (hq : 1 ≤ q)
    {f : ParabolicPoint → ℝ} (_ : AEMeasurable f volume)
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal |f w|) ≤
      (ENNReal.ofReal r) ^ (5 * (1 - 1 / q)) * morreyNorm 1 q f := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hcell : morreyCell 1 q f z r ≤ morreyNorm 1 q f := by
    unfold morreyNorm
    exact le_iSup_of_le z (le_iSup_of_le ⟨r, hr⟩ le_rfl)
  have hcell' : (ENNReal.ofReal r) ^ (-(5 * (1 - 1 / q))) *
      cylinderPowerIntegral 1 f z r ≤ morreyNorm 1 q f := by
    simpa [morreyCell, one_div, hq0.ne'] using hcell
  have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hrtop : ENNReal.ofReal r ≠ ∞ := ENNReal.ofReal_ne_top
  have hinv : (ENNReal.ofReal r) ^ (5 * (1 - 1 / q)) *
      (ENNReal.ofReal r) ^ (-(5 * (1 - 1 / q))) = 1 := by
    rw [← ENNReal.rpow_add _ _ hr0 hrtop, add_neg_cancel, ENNReal.rpow_zero]
  calc
    (∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal |f w|) =
        cylinderPowerIntegral 1 f z r := by
      unfold cylinderPowerIntegral
      apply lintegral_congr
      intro w
      simp
    _ = (ENNReal.ofReal r) ^ (5 * (1 - 1 / q)) *
          ((ENNReal.ofReal r) ^ (-(5 * (1 - 1 / q))) *
            cylinderPowerIntegral 1 f z r) := by
      calc
        cylinderPowerIntegral 1 f z r =
            1 * cylinderPowerIntegral 1 f z r := by rw [one_mul]
        _ = ((ENNReal.ofReal r) ^ (5 * (1 - 1 / q)) *
              (ENNReal.ofReal r) ^ (-(5 * (1 - 1 / q)))) *
            cylinderPowerIntegral 1 f z r := by rw [hinv]
        _ = _ := by ac_rfl
    _ ≤ (ENNReal.ofReal r) ^ (5 * (1 - 1 / q)) * morreyNorm 1 q f :=
      by
        simpa [mul_comm] using
          (mul_le_mul_left hcell' ((ENNReal.ofReal r) ^
            (5 * (1 - 1 / q))))

lemma exists_positive_shell {z w : ParabolicPoint} {R : ℝ}
    (hR : 0 < R) (hRρ : R ≤ parabolicRho₂ z w) :
    ∃ k : ℕ, w ∈ parabolicRieszShell R (k : ℤ) z := by
  let x : ℝ := parabolicRho₂ z w / R
  let L : ℝ := Real.log 2
  let k : ℤ := ⌊Real.log x / L⌋
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hx : 1 ≤ x := by
    dsimp [x]
    exact (one_le_div hR).2 hRρ
  have hk : 0 ≤ k := by
    apply (Int.floor_nonneg).2
    exact div_nonneg (Real.log_nonneg hx) hL.le
  have hklo : (k : ℝ) ≤ Real.log x / L := Int.floor_le _
  have hkhi : Real.log x / L < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hpowlo : (2 : ℝ) ^ (k : ℝ) ≤ x := by
    apply (Real.strictMonoOn_log.le_iff_le
      (Real.rpow_pos_of_pos (by norm_num) _) (by positivity : 0 < x)).mp
    rw [Real.log_rpow (by norm_num)]
    calc
      (k : ℝ) * Real.log 2 ≤ (Real.log x / L) * L :=
        mul_le_mul_of_nonneg_right hklo hL.le
      _ = Real.log x := by field_simp [hL.ne']
  have hpowhi : x < (2 : ℝ) ^ ((k : ℝ) + 1) := by
    apply (Real.strictMonoOn_log.lt_iff_lt
      (by positivity : 0 < x) (Real.rpow_pos_of_pos (by norm_num) _)).mp
    rw [Real.log_rpow (by norm_num)]
    calc
      Real.log x = (Real.log x / L) * L := by field_simp [hL.ne']
      _ < ((k : ℝ) + 1) * L := mul_lt_mul_of_pos_right hkhi hL
  have hinner : (2 : ℝ) ^ (k : ℝ) * R ≤ parabolicRho₂ z w := by
    simpa [x] using (le_div_iff₀ hR).mp hpowlo
  have houter : parabolicRho₂ z w < (2 : ℝ) ^ ((k : ℝ) + 1) * R := by
    simpa [x] using (div_lt_iff₀ hR).mp hpowhi
  have hmem : w ∈ parabolicRieszShell R k z := mem_parabolicRieszShell hinner houter
  exact ⟨k.toNat, by simpa [Int.toNat_of_nonneg hk] using hmem⟩

/-- Nonnegative-index parabolic shell for the far-field Morrey estimate. -/
def positiveShell (R : ℝ) (n : ℕ) (z : ParabolicPoint) : Set ParabolicPoint :=
  parabolicRieszShell R (n : ℤ) z

/-- The dyadic constant used by the Morrey tail estimate. -/
def parabolicTailKernelConstant (β q : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, (ENNReal.ofReal (2 : ℝ)) ^
    ((n : ℝ) * (β - 5 / q) + 2 * (5 * (1 - 1 / q)))

end CKN.Foundation.Parabolic.Morrey
