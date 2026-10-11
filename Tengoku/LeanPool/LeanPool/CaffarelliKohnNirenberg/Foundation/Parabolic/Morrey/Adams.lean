/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Maximal.StrongType
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Hedberg
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Inclusions
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Kernel

/-!
# Hedberg and Adams estimates

This module connects the parabolic Riesz potential with the exported maximal
function estimates and the cylinder Morrey seminorm.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology

noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- The maximal function applied to the absolute value of a real function. -/
def parabolicMaximalMajorant (f : ParabolicPoint → ℝ) : ParabolicPoint → ℝ≥0∞ :=
  parabolicMaximalFunction (fun w ↦ ENNReal.ofReal |f w|)

private lemma volume_metricBall_le {z : ParabolicPoint} {R : ℝ} (hR : 0 < R) :
    volume (Metric.ball z R) ≤
      ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (R ^ 5) *
        volume (parabolicCylinder 0 0 1) := by
  let T : ℝ := z.2 + (2 * R) ^ 2 / 2
  have hball := metricBall_subset_parabolicCylinder (x := z.1) (t := T)
    (r := 2 * R) (by positivity)
  have hcenter : (z.1, T - (2 * R) ^ 2 / 2) = z := by
    dsimp [T]
    congr 1
    ring_nf
  have hradius : (2 * R) / 2 = R := by ring_nf
  rw [hcenter, hradius] at hball
  have hscale := volume_parabolicCylinder_radius_scale
    (x := z.1) (t := T) (r := 1) (a := 2 * R) (by positivity)
  have hunit : volume (parabolicCylinder z.1 T 1) =
      volume (parabolicCylinder 0 0 1) := by
    rw [volume_parabolicCylinder_zero, volume_parabolicCylinder_zero]
  calc
    volume (Metric.ball z R) ≤ volume (parabolicCylinder z.1 T (2 * R)) :=
      measure_mono hball
    _ = ENNReal.ofReal ((2 * R) ^ 5) * volume (parabolicCylinder z.1 T 1) := by
      simpa using hscale
    _ = ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (R ^ 5) *
        volume (parabolicCylinder 0 0 1) := by
      rw [hunit, show (2 * R) ^ 5 = 2 ^ 5 * R ^ 5 by ring_nf,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 5),
        ENNReal.ofReal_pow (by positivity : 0 ≤ R) 5]

/-- Negative-index dyadic parabolic shell for the near-field Morrey estimate. -/
def nearShell (R : ℝ) (n : ℕ) (z : ParabolicPoint) : Set ParabolicPoint :=
  parabolicRieszShell R (Int.negSucc n) z

private lemma nearShell_measurable (R : ℝ) (n : ℕ) (z : ParabolicPoint) :
    MeasurableSet (nearShell R n z) := by
  exact measurableSet_parabolicRieszShell R (Int.negSucc n) z

private lemma nearShell_pairwise {R : ℝ} (hR : 0 < R) (z : ParabolicPoint) :
    Pairwise (Function.onFun Disjoint (fun n ↦ nearShell R n z)) := by
  intro n m hnm
  change Disjoint (nearShell R n z) (nearShell R m z)
  rw [Set.disjoint_left]
  intro w hwn hwm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have hindex : Int.negSucc m + 1 ≤ Int.negSucc n := by omega
    have hexp : ((Int.negSucc m : ℝ) + 1) ≤ (Int.negSucc n : ℝ) := by
      exact_mod_cast hindex
    have hpow : (2 : ℝ) ^ ((Int.negSucc m : ℝ) + 1) ≤
        (2 : ℝ) ^ (Int.negSucc n : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hrad := mul_le_mul_of_nonneg_right hpow hR.le
    exact (not_lt_of_ge (hrad.trans hwn.1)) hwm.2
  · have hindex : Int.negSucc n + 1 ≤ Int.negSucc m := by omega
    have hexp : ((Int.negSucc n : ℝ) + 1) ≤ (Int.negSucc m : ℝ) := by
      exact_mod_cast hindex
    have hpow : (2 : ℝ) ^ ((Int.negSucc n : ℝ) + 1) ≤
        (2 : ℝ) ^ (Int.negSucc m : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hrad := mul_le_mul_of_nonneg_right hpow hR.le
    exact (not_lt_of_ge (hrad.trans hwm.1)) hwn.2

private lemma zero_set_volume (z : ParabolicPoint) :
    volume ({w | parabolicRho₂ z w = 0} : Set ParabolicPoint) = 0 := by
  apply measure_mono_null (parabolicRho₂_zero_subset_singleton z)
  rcases z with ⟨x, t⟩
  change (volume : Measure (Vec3 × ℝ)) ({(x, t)} : Set (Vec3 × ℝ)) = 0
  have hset : ({(x, t)} : Set (Vec3 × ℝ)) = {x} ×ˢ {t} := by
    ext p
    rcases p with ⟨y, s⟩
    simp only [mem_singleton_iff]
    constructor
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · rintro ⟨hy, hs⟩
      exact Prod.ext hy hs
  rw [hset]
  change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ))
    ({x} ×ˢ {t}) = 0
  rw [Measure.prod_prod]
  simp

private lemma near_shell_integral_le
    {β q : ℝ} (hβ : 0 < β) (hβ5 : β < 5) (_ : 1 ≤ q)
    (_ : β * q < 5) {R : ℝ} (hR : 0 < R)
    {f : ParabolicPoint → ℝ} {M : ParabolicPoint → ℝ≥0∞}
    (hf : AEMeasurable f volume) (hM : IsParabolicMaximalMajorant f M)
    (n : ℕ) (z : ParabolicPoint) :
    (∫⁻ w in nearShell R n z,
      parabolicRieszKernel β z w * ENNReal.ofReal |f w|) ≤
      (ENNReal.ofReal (2 ^ 5) *
        (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1))) *
        (ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β) *
          ENNReal.ofReal (R ^ β)) * M z := by
  let a : ℝ := (2 : ℝ) ^ (Int.negSucc n : ℝ) * R
  let b : ℝ := (2 : ℝ) ^ ((Int.negSucc n : ℝ) + 1) * R
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hkernel : ∀ w ∈ nearShell R n z,
      parabolicRieszKernel β z w ≤ (ENNReal.ofReal a) ^ (-(5 - β)) := by
    intro w hw
    have hinner : a ≤ parabolicRho₂ z w := by
      simpa [a, nearShell] using hw.1
    rw [parabolicRieszKernel, ENNReal.rpow_neg, ENNReal.rpow_neg,
      ENNReal.inv_le_inv]
    apply ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hinner)
    exact sub_nonneg.mpr hβ5.le
  have hsubset : nearShell R n z ⊆ Metric.ball z b := by
    intro w hw
    apply parabolicRho₂_lt_subset_metricBall
    simpa [b, nearShell] using hw.2
  have hball :
      (∫⁻ w in nearShell R n z, ENNReal.ofReal |f w|) ≤
        M z * volume (Metric.ball z b) := by
    calc
      (∫⁻ w in nearShell R n z, ENNReal.ofReal |f w|) ≤
          ∫⁻ w in Metric.ball z b, ENNReal.ofReal |f w| :=
        lintegral_mono_set hsubset
      _ ≤ M z * volume (Metric.ball z b) := hM z b hb
  have hball' :
      (∫⁻ w in nearShell R n z, ENNReal.ofReal |f w|) ≤
        M z * (ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (b ^ 5) *
          volume (parabolicCylinder 0 0 1)) :=
    hball.trans (by
      simpa [mul_comm] using (mul_le_mul_left (volume_metricBall_le hb) (M z)))
  have hprod :
      (∫⁻ w in nearShell R n z,
        parabolicRieszKernel β z w * ENNReal.ofReal |f w|) ≤
        (ENNReal.ofReal a) ^ (-(5 - β)) *
          (∫⁻ w in nearShell R n z, ENNReal.ofReal |f w|) := by
    calc
      (∫⁻ w in nearShell R n z,
          parabolicRieszKernel β z w * ENNReal.ofReal |f w|) ≤
          ∫⁻ w in nearShell R n z,
            (ENNReal.ofReal a) ^ (-(5 - β)) * ENNReal.ofReal |f w| := by
        apply setLIntegral_mono_ae
          ((hf.norm.ennreal_ofReal.restrict).const_mul
            ((ENNReal.ofReal a) ^ (-(5 - β))))
        filter_upwards [] with w hw
        simpa only [Real.norm_eq_abs] using
          (mul_le_mul (hkernel w hw) (le_refl _) (by positivity) (by positivity))
      _ = (ENNReal.ofReal a) ^ (-(5 - β)) *
          (∫⁻ w in nearShell R n z, ENNReal.ofReal |f w|) := by
        rw [lintegral_const_mul' _ _ (by
          rw [ENNReal.rpow_neg]
          exact ENNReal.inv_ne_top.mpr
            (ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr ha)
              ENNReal.ofReal_ne_top)))]
  calc
    (∫⁻ w in nearShell R n z,
        parabolicRieszKernel β z w * ENNReal.ofReal |f w|) ≤
        (ENNReal.ofReal a) ^ (-(5 - β)) *
          (M z * (ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (b ^ 5) *
            volume (parabolicCylinder 0 0 1))) :=
      hprod.trans (by
        simpa [mul_comm] using
          (mul_le_mul_right hball' ((ENNReal.ofReal a) ^ (-(5 - β)))))
    _ = (ENNReal.ofReal (2 ^ 5) *
        (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1))) *
        (ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β) *
          ENNReal.ofReal (R ^ β)) * M z := by
      have hba : b = 2 * a := by
        dsimp [a, b]
        rw [Real.rpow_add (by positivity)]
        ring_nf
      have hscale :
          (ENNReal.ofReal a) ^ (-(5 - β)) * ENNReal.ofReal (b ^ 5) =
            ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (a ^ β) := by
        rw [hba]
        exact shell_power_identity ha hβ.le hβ5.le
      calc
        (ENNReal.ofReal a) ^ (-(5 - β)) *
            (M z * (ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (b ^ 5) *
              volume (parabolicCylinder 0 0 1))) =
            M z * ((ENNReal.ofReal a) ^ (-(5 - β)) *
              ENNReal.ofReal (b ^ 5)) *
              (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1)) := by
                ac_rfl
        _ = M z * (ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (a ^ β)) *
              (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1)) := by
                rw [hscale]
        _ = (ENNReal.ofReal (2 ^ 5) *
            (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1))) *
            (ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β) *
              ENNReal.ofReal (R ^ β)) * M z := by
          rw [Real.mul_rpow (by positivity) hR.le,
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤
              ((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β)]
          ac_rfl

/-- The geometric constant in the local Hedberg estimate. -/
def parabolicHedbergNearConstant (β : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (2 ^ 5) *
      (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1))) *
    ∑' n : ℕ, ENNReal.ofReal
      (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β)

end Morrey
end Parabolic
end Foundation
end CKN
