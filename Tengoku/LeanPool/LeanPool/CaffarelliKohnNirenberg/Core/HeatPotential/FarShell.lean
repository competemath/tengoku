/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.Far

/-!
# Far Shell

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric
open Filter

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

theorem measurable_heatPotentialSpatialKernel_translate (i : Fin 3) (w : ParabolicPoint) :
    Measurable (fun v : ParabolicPoint => heatPotentialSpatialKernel i w v) := by
  unfold heatPotentialSpatialKernel
  unfold heatKernelSpaceDerivative
  apply Measurable.ite
  · measurability
  · have hheat : Measurable (fun v : ParabolicPoint =>
        heatKernel (w.1 - v.1) (w.2 - v.2)) := by
      unfold heatKernel
      apply Measurable.ite
      · measurability
      · measurability
      · exact measurable_const
    have hcoef : Measurable (fun v : ParabolicPoint =>
        -(w.1 - v.1) i / (2 * (w.2 - v.2))) := by
      measurability
    exact hcoef.mul hheat
  · exact measurable_const

/-- Far parabolic shell with the six-scale separation used in heat-kernel difference estimates. -/
def heatPotentialFarShellSet (z : ParabolicPoint) (r : ℝ) (j : ℕ) :
    Set ParabolicPoint :=
  parabolicRieszShell r (j + 6 : ℤ) z
theorem measurableSet_heatPotentialFarShellSet (z : ParabolicPoint) (r : ℝ)
    (j : ℕ) : MeasurableSet (heatPotentialFarShellSet z r j) := by
  exact measurableSet_parabolicRieszShell r (j + 6 : ℤ) z

private lemma parabolicRho₂_symm (z w : ParabolicPoint) :
    parabolicRho₂ z w = parabolicRho₂ w z := by
  unfold parabolicRho₂
  rw [abs_sub_comm]
  congr 1
  have hneg : z.1 - w.1 = -(w.1 - z.1) := by abel
  calc
    vec3EuclideanNorm (z.1 - w.1) =
        vec3EuclideanNorm (-(w.1 - z.1)) := by rw [hneg]
    _ = vec3EuclideanNorm (w.1 - z.1) := by
      unfold vec3EuclideanNorm
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      change (-(w.1 i - z.1 i)) ^ 2 = (w.1 i - z.1 i) ^ 2
      ring

private lemma parabolicRho₂_le_two_parabolicDist (z w : ParabolicPoint) :
    parabolicRho₂ z w ≤ 2 * parabolicDist z w := by
  unfold parabolicRho₂ parabolicDist
  have hs : vec3EuclideanNorm (z.1 - w.1) ≤
      max (vec3EuclideanNorm (z.1 - w.1)) (Real.sqrt |z.2 - w.2|) :=
    le_max_left _ _
  have ht : Real.sqrt |z.2 - w.2| ≤
      max (vec3EuclideanNorm (z.1 - w.1)) (Real.sqrt |z.2 - w.2|) :=
    le_max_right _ _
  linarith only [hs, ht]

private lemma parabolicRho₂_quasi_triangle (a b c : ParabolicPoint) :
    parabolicRho₂ a c ≤
      2 * parabolicRho₂ a b + 2 * parabolicRho₂ b c := by
  have hdist : parabolicDist a c ≤ parabolicDist a b + parabolicDist b c := by
    rw [← dist_eq_parabolicDist a c, ← dist_eq_parabolicDist a b,
      ← dist_eq_parabolicDist b c]
    exact dist_triangle _ _ _
  have hab : parabolicDist a b ≤ parabolicRho₂ a b :=
    parabolicDist_le_parabolicRho₂ _ _
  have hbc : parabolicDist b c ≤ parabolicRho₂ b c :=
    parabolicDist_le_parabolicRho₂ _ _
  calc
    parabolicRho₂ a c ≤ 2 * parabolicDist a c :=
      parabolicRho₂_le_two_parabolicDist _ _
    _ ≤ 2 * (parabolicDist a b + parabolicDist b c) :=
      mul_le_mul_of_nonneg_left hdist (by norm_num)
    _ = 2 * parabolicDist a b + 2 * parabolicDist b c := by ring
    _ ≤ 2 * parabolicRho₂ a b + 2 * parabolicRho₂ b c := by
      exact add_le_add (mul_le_mul_of_nonneg_left hab (by norm_num))
        (mul_le_mul_of_nonneg_left hbc (by norm_num))

theorem heatPotential_far_shell_kernel_separation
    {z w v : ParabolicPoint} {r : ℝ} {j : ℕ}
    (hr : 0 < r) (hw : w ∈ @Metric.closedBall ParabolicPoint
      parabolicPseudoMetricSpace z r)
    (hv : v ∈ heatPotentialFarShellSet z r j) :
    w.2 - v.2 ≤ 0 ∨
      (2 : ℝ) ^ ((j : ℝ) + 4) * r ≤
        rhoTwo (w.1 - v.1) (w.2 - v.2) := by
  by_cases ht : w.2 - v.2 ≤ 0
  · exact Or.inl ht
  · right
    have htpos : 0 < w.2 - v.2 := lt_of_not_ge ht
    have hdist : parabolicDist w z ≤ r := by
      rw [← dist_eq_parabolicDist]
      simpa [dist_comm] using hw
    have hrhowz : parabolicRho₂ w z ≤ 2 * r := by
      exact (parabolicRho₂_le_two_parabolicDist w z).trans
        (mul_le_mul_of_nonneg_left hdist (by norm_num))
    have hsource : (2 : ℝ) ^ ((j : ℝ) + 6) * r ≤
        parabolicRho₂ z v := by
      simpa [heatPotentialFarShellSet, Nat.cast_add, Int.cast_ofNat,
        add_assoc, add_comm, add_left_comm] using hv.1
    have hquasi := parabolicRho₂_quasi_triangle z w v
    have hlow : 2 ^ ((j : ℝ) + 5) * r - 2 * r ≤ parabolicRho₂ w v := by
      have hq : 2 * parabolicRho₂ z w + 2 * parabolicRho₂ w v ≥
          parabolicRho₂ z v := by linarith only [hquasi]
      have hsym : parabolicRho₂ z w = parabolicRho₂ w z :=
        parabolicRho₂_symm _ _
      have hq' : 2 * parabolicRho₂ w v ≥
          parabolicRho₂ z v - 2 * (2 * r) := by
        rw [hsym] at hq
        linarith only [hq, hrhowz]
      have hpow : 2 ^ ((j : ℝ) + 5) * r ≤ parabolicRho₂ z v / 2 := by
        have hpow' : 2 ^ ((j : ℝ) + 6) * r =
            2 * (2 ^ ((j : ℝ) + 5) * r) := by
          rw [show (j : ℝ) + 6 = ((j : ℝ) + 5) + 1 by ring,
            Real.rpow_add (by norm_num)]
          ring
        rw [hpow'] at hsource
        linarith only [hsource]
      linarith only [hq', hpow]
    rw [show rhoTwo (w.1 - v.1) (w.2 - v.2) = parabolicRho₂ w v by
      unfold rhoTwo parabolicRho₂
      rw [abs_of_pos htpos]
      exact add_comm _ _]
    have hpow : 2 ≤ (2 : ℝ) ^ ((j : ℝ) + 4) := by
      have hone : (2 : ℝ) ^ (1 : ℝ) = 2 := by norm_num
      have hj : (1 : ℝ) ≤ (j : ℝ) + 4 := by
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith only [hj0]
      calc
        (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := hone.symm
        _ ≤ (2 : ℝ) ^ ((j : ℝ) + 4) :=
          Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) hj
    have hrpow : 2 * r ≤ (2 : ℝ) ^ ((j : ℝ) + 4) * r :=
      mul_le_mul_of_nonneg_right hpow hr.le
    have hpow' : (2 : ℝ) ^ ((j : ℝ) + 5) =
        2 * ((2 : ℝ) ^ ((j : ℝ) + 4)) := by
      calc
        (2 : ℝ) ^ ((j : ℝ) + 5) =
            (2 : ℝ) ^ (((j : ℝ) + 4) + 1) := by congr 1; ring
        _ = (2 : ℝ) ^ ((j : ℝ) + 4) * (2 : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_add (by norm_num)]
        _ = 2 * ((2 : ℝ) ^ ((j : ℝ) + 4)) := by norm_num; ring
    rw [hpow'] at hlow
    linarith only [hlow, hrpow]
theorem heatPotential_far_shell_rho_separation
    {z w v : ParabolicPoint} {r : ℝ} {j : ℕ}
    (hr : 0 < r) (hw : w ∈ @Metric.closedBall ParabolicPoint
      parabolicPseudoMetricSpace z r)
    (hv : v ∈ heatPotentialFarShellSet z r j) :
    (2 : ℝ) ^ ((j : ℝ) + 4) * r ≤ parabolicRho₂ w v := by
  have hdist : parabolicDist w z ≤ r := by
    rw [← dist_eq_parabolicDist]
    simpa [dist_comm] using hw
  have hrhowz : parabolicRho₂ w z ≤ 2 * r := by
    exact (parabolicRho₂_le_two_parabolicDist w z).trans
      (mul_le_mul_of_nonneg_left hdist (by norm_num))
  have hsource : (2 : ℝ) ^ ((j : ℝ) + 6) * r ≤ parabolicRho₂ z v := by
    simpa [heatPotentialFarShellSet, Nat.cast_add, Int.cast_ofNat,
      add_assoc, add_comm, add_left_comm] using hv.1
  have hquasi := parabolicRho₂_quasi_triangle z w v
  have hq : 2 * parabolicRho₂ z w + 2 * parabolicRho₂ w v ≥
      parabolicRho₂ z v := by linarith only [hquasi]
  have hsym : parabolicRho₂ z w = parabolicRho₂ w z :=
    parabolicRho₂_symm _ _
  have hq' : 2 * parabolicRho₂ w v ≥
      parabolicRho₂ z v - 2 * (2 * r) := by
    rw [hsym] at hq
    linarith only [hq, hrhowz]
  have hpow : 2 ^ ((j : ℝ) + 5) * r ≤ parabolicRho₂ z v / 2 := by
    have hpow' : 2 ^ ((j : ℝ) + 6) * r =
        2 * (2 ^ ((j : ℝ) + 5) * r) := by
      rw [show (j : ℝ) + 6 = ((j : ℝ) + 5) + 1 by ring,
        Real.rpow_add (by norm_num)]
      ring
    rw [hpow'] at hsource
    linarith only [hsource]
  have hlow : 2 ^ ((j : ℝ) + 5) * r - 2 * r ≤ parabolicRho₂ w v := by
    linarith only [hq', hpow]
  have hpow2 : 2 ≤ (2 : ℝ) ^ ((j : ℝ) + 4) := by
    have hone : (2 : ℝ) ^ (1 : ℝ) = 2 := by norm_num
    have hj : (1 : ℝ) ≤ (j : ℝ) + 4 := by
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith only [hj0]
    calc
      (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := hone.symm
      _ ≤ (2 : ℝ) ^ ((j : ℝ) + 4) :=
        Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) hj
  have hrpow : 2 * r ≤ (2 : ℝ) ^ ((j : ℝ) + 4) * r :=
    mul_le_mul_of_nonneg_right hpow2 hr.le
  have hpow' : (2 : ℝ) ^ ((j : ℝ) + 5) =
      2 * ((2 : ℝ) ^ ((j : ℝ) + 4)) := by
    calc
      (2 : ℝ) ^ ((j : ℝ) + 5) =
          (2 : ℝ) ^ (((j : ℝ) + 4) + 1) := by congr 1; ring
      _ = (2 : ℝ) ^ ((j : ℝ) + 4) * (2 : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_add (by norm_num)]
      _ = 2 * ((2 : ℝ) ^ ((j : ℝ) + 4)) := by norm_num; ring
  rw [hpow'] at hlow
  linarith only [hlow, hrpow]

theorem heatPotential_far_shell_kernel_abs_le
    {z w v : ParabolicPoint} {r : ℝ} {j : ℕ}
    (hr : 0 < r) (hw : w ∈ @Metric.closedBall ParabolicPoint
      parabolicPseudoMetricSpace z r)
    (hv : v ∈ heatPotentialFarShellSet z r j) :
    |heatPotentialKernel w v| ≤
        1000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 3 := by
  rcases heatPotential_far_shell_kernel_separation hr hw hv with ht | hsep
  · change |heatKernelPlus (w.1 - v.1, w.2 - v.2)| ≤
      1000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 3
    rw [heatKernelPlus_eq_zero_of_nonpos ht, abs_zero]
    positivity
  · exact heatPotentialKernel_abs_le (by positivity) hsep

theorem heatPotential_far_shell_spatial_kernel_abs_le
    {i : Fin 3} {z w v : ParabolicPoint} {r : ℝ} {j : ℕ}
    (hr : 0 < r) (hw : w ∈ @Metric.closedBall ParabolicPoint
      parabolicPseudoMetricSpace z r)
    (hv : v ∈ heatPotentialFarShellSet z r j) :
    |heatPotentialSpatialKernel i w v| ≤
        300000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4 := by
  rcases heatPotential_far_shell_kernel_separation hr hw hv with ht | hsep
  · rw [heatPotentialSpatialKernel, heatKernelSpaceDerivative,
      ite_eq_right (not_lt.mpr ht), abs_zero]
    positivity
  · exact heatPotentialSpatialKernel_abs_le (by positivity) hsep

end CKN.Core.HeatPotential
