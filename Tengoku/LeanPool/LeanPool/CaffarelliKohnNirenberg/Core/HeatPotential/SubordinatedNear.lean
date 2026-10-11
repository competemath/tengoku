/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.SubordinatedBase

/-!
# Subordinated Near

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
noncomputable section
namespace CKN.Core.HeatPotential
open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

lemma heatPotential_near_factor_toReal
    {δ q r b : ℝ} {N : ℝ≥0∞} (hr : 0 < r) (hδ : 0 < δ) :
    ((ENNReal.ofReal 2) ^ q *
      (1 - (ENNReal.ofReal 2) ^ (-δ))⁻¹ *
      (ENNReal.ofReal (256 * r)) ^ δ *
      (volume (parabolicCylinder 0 0 1)) ^ b * N).toReal =
      (2 : ℝ) ^ q * (1 - (2 : ℝ) ^ (-δ))⁻¹ *
        (256 * r) ^ δ *
        (volume (parabolicCylinder 0 0 1)).toReal ^ b * N.toReal := by
  have hden : (1 : ℝ≥0∞) - (ENNReal.ofReal 2) ^ (-δ) =
      ENNReal.ofReal (1 - (2 : ℝ) ^ (-δ)) := by
    rw [ENNReal.ofReal_rpow_of_pos (by norm_num)]
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by norm_num]
    exact (ENNReal.ofReal_sub (p := 1) (q := (2 : ℝ) ^ (-δ))
      (by positivity)).symm
  have hq : (2 : ℝ) ^ (-δ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hδ])
  have hdenR : 0 ≤ 1 - (2 : ℝ) ^ (-δ) := sub_nonneg.mpr hq.le
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul]
  rw [← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow]
  rw [ENNReal.toReal_ofReal (by positivity), hden, ENNReal.toReal_inv]
  rw [ENNReal.toReal_ofReal hdenR]
  rw [← ENNReal.toReal_rpow]
  rw [ENNReal.toReal_ofReal (by positivity)]

lemma heatPotential_near_factor_ne_top
    {δ q r b : ℝ} {N : ℝ≥0∞} (_ : 0 < r) (hδ : 0 < δ)
    (hq : 0 ≤ q) (hb : 0 ≤ b) (hN : N < ∞) :
    ((ENNReal.ofReal 2) ^ q *
      (1 - (ENNReal.ofReal 2) ^ (-δ))⁻¹ *
      (ENNReal.ofReal (256 * r)) ^ δ *
      (volume (parabolicCylinder 0 0 1)) ^ b * N) ≠ ∞ := by
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · apply ENNReal.rpow_ne_top_of_nonneg hq ENNReal.ofReal_ne_top
        · apply ENNReal.inv_ne_top.mpr
          have hq' : (ENNReal.ofReal 2) ^ (-δ) < 1 := by
            rw [ENNReal.ofReal_rpow_of_pos (by norm_num)]
            apply ENNReal.ofReal_lt_one.mpr
            exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
              (by linarith only [hδ])
          exact (tsub_pos_iff_lt.mpr hq').ne'
      · apply ENNReal.rpow_ne_top_of_nonneg hδ.le
        exact ENNReal.ofReal_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg hb
      exact Integration.volume_parabolicCylinder_lt_top.ne
  · exact hN.ne

lemma subordinated_parabolicRho₂_le_two_parabolicDist
    (z w : ParabolicPoint) :
    parabolicRho₂ z w ≤ 2 * parabolicDist z w := by
  unfold parabolicRho₂ parabolicDist
  have hs : vec3EuclideanNorm (z.1 - w.1) ≤
      max (vec3EuclideanNorm (z.1 - w.1)) (Real.sqrt |z.2 - w.2|) :=
    le_max_left _ _
  have ht : Real.sqrt |z.2 - w.2| ≤
      max (vec3EuclideanNorm (z.1 - w.1)) (Real.sqrt |z.2 - w.2|) :=
    le_max_right _ _
  linarith only [hs, ht]

lemma subordinated_parabolicRho₂_quasi_triangle
    (a b c : ParabolicPoint) :
    parabolicRho₂ a c ≤
      2 * parabolicRho₂ a b + 2 * parabolicRho₂ b c := by
  have hdist : parabolicDist a c ≤ parabolicDist a b + parabolicDist b c := by
    rw [← dist_eq_parabolicDist a c, ← dist_eq_parabolicDist a b,
      ← dist_eq_parabolicDist b c]
    exact dist_triangle _ _ _
  have hab := parabolicDist_le_parabolicRho₂ a b
  have hbc := parabolicDist_le_parabolicRho₂ b c
  calc
    parabolicRho₂ a c ≤ 2 * parabolicDist a c :=
      subordinated_parabolicRho₂_le_two_parabolicDist a c
    _ ≤ 2 * (parabolicDist a b + parabolicDist b c) := by gcongr
    _ ≤ 2 * (parabolicRho₂ a b + parabolicRho₂ b c) := by
      gcongr
    _ = 2 * parabolicRho₂ a b + 2 * parabolicRho₂ b c := by ring

lemma heatPotential_near_set_subset_riesz_ball
    {z p : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) :
    heatPotentialNearSet z r ⊆ {v | parabolicRho₂ p v < 256 * r} := by
  intro v hv
  have hpdist : parabolicDist p z ≤ r := by
    rw [← dist_eq_parabolicDist]
    exact Metric.mem_closedBall.mp hp
  have hprho : parabolicRho₂ p z ≤ 2 * r := by
    exact (subordinated_parabolicRho₂_le_two_parabolicDist p z).trans
      (mul_le_mul_of_nonneg_left hpdist (by norm_num))
  have hquasi := subordinated_parabolicRho₂_quasi_triangle p z v
  have hv' : parabolicRho₂ z v < 64 * r := hv
  calc
    parabolicRho₂ p v ≤ 2 * parabolicRho₂ p z + 2 * parabolicRho₂ z v := hquasi
    _ < 2 * (2 * r) + 2 * (64 * r) := by
      exact add_lt_add_of_le_of_lt
        (mul_le_mul_of_nonneg_left hprho (by norm_num))
        (mul_lt_mul_of_pos_left hv' (by norm_num))
    _ < 256 * r := by linarith only [hr]

lemma heatPotential_far_uniform_kernel_bound
    {z p : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) :
    ∀ v ∈ ⋃ j : ℕ, heatPotentialFarShellSet z r j,
      |heatPotentialKernel p v| ≤ 1000 / (16 * r) ^ 3 := by
  intro v hv
  rcases mem_iUnion.mp hv with ⟨j, hj⟩
  have hscale : 16 * r ≤ (2 : ℝ) ^ ((j : ℝ) + 4) * r := by
    have hpow : (2 : ℝ) ^ (4 : ℝ) ≤ (2 : ℝ) ^ ((j : ℝ) + 4) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      norm_num
    exact mul_le_mul_of_nonneg_right (by norm_num at hpow ⊢; exact hpow) hr.le
  have hkernel := heatPotential_far_shell_kernel_abs_le hr hp hj
  have hpow : (16 * r) ^ 3 ≤
      ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hscale 3
  have hinv : 1 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 3 ≤
      1 / (16 * r) ^ 3 := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by positivity) hpow)
  exact hkernel.trans (by
    have hmul := mul_le_mul_of_nonneg_left hinv
      (show 0 ≤ (1000 : ℝ) by norm_num)
    simpa only [one_div, div_eq_mul_inv, one_mul] using hmul)

lemma heatPotential_far_uniform_spatial_kernel_bound
    {z p : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (i : Fin 3) :
    ∀ v ∈ ⋃ j : ℕ, heatPotentialFarShellSet z r j,
      |heatPotentialSpatialKernel i p v| ≤ 300000 / (16 * r) ^ 4 := by
  intro v hv
  rcases mem_iUnion.mp hv with ⟨j, hj⟩
  have hscale : 16 * r ≤ (2 : ℝ) ^ ((j : ℝ) + 4) * r := by
    have hpow : (2 : ℝ) ^ (4 : ℝ) ≤ (2 : ℝ) ^ ((j : ℝ) + 4) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      norm_num
    exact mul_le_mul_of_nonneg_right (by norm_num at hpow ⊢; exact hpow) hr.le
  have hkernel := heatPotential_far_shell_spatial_kernel_abs_le (i := i) hr hp hj
  have hpow : (16 * r) ^ 4 ≤
      ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hscale 4
  have hinv : 1 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4 ≤
      1 / (16 * r) ^ 4 := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by positivity) hpow)
  exact hkernel.trans (by
    have hmul := mul_le_mul_of_nonneg_left hinv
      (show 0 ≤ (300000 : ℝ) by norm_num)
    simpa only [one_div, div_eq_mul_inv, one_mul] using hmul)

end CKN.Core.HeatPotential
