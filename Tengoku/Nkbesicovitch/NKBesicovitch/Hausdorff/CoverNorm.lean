/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Hausdorff.DiskPlate
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.MixedNorm.Sums
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.PlateMeasurability
public import Tengoku.Nkbesicovitch.NKBesicovitch.Grassmannian.Measure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Direction-space cost of a countable disk cover

A countable cover of every directional disk gives a positive lower bound
for the sum of the maximal norms of the thickened covering sets. Centers
are chosen separately in each direction; no measurable selection is used.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace NKBesicovitch.Hausdorff

variable {n k : ℕ}

theorem one_le_tsum_diskAverage_of_cover (U : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (hU : ∀ j, MeasurableSet (U j)) (V : Grassmannian n k)
    (a : EuclideanSpace ℝ (Fin n)) (hcover : unitDisk V.val a ⊆ ⋃ j, U j) :
    1 ≤ ∑' j, diskAverage ((U j).indicator (fun _ ↦ (1 : ℝ≥0∞))) V a := by
  let D := closedBall (0 : V.val) 1
  have hD : volume D ≠ 0 := (measure_closedBall_pos volume _ zero_lt_one).ne'
  have hDf : volume D ≠ ∞ := measure_closedBall_lt_top.ne
  have hf (j) : Measurable (fun v : V.val ↦
      (U j).indicator (fun _ ↦ (1 : ℝ≥0∞)) (a + v)) :=
    (measurable_const.indicator (hU j)).comp
      (continuous_const.add continuous_subtype_val).measurable
  have hpoint (v : V.val) (hv : v ∈ D) :
      1 ≤ ∑' j, (U j).indicator (fun _ ↦ (1 : ℝ≥0∞)) (a + v) := by
    have hx : a + (v : EuclideanSpace ℝ (Fin n)) ∈ unitDisk V.val a := by
      simpa [unitDisk, D, mem_closedBall_zero_iff] using And.intro v.property hv
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hx)
    simpa only [indicator_of_mem hj] using
      (ENNReal.le_tsum (f := fun j ↦ (U j).indicator (fun _ ↦ (1 : ℝ≥0∞)) (a + v)) j)
  have h := setLIntegral_mono (μ := volume) (Measurable.tsum hf) hpoint
  rw [setLIntegral_const, one_mul, lintegral_tsum (fun j ↦ (hf j).aemeasurable)] at h
  have hdiv := ENNReal.div_le_div_right h (volume D)
  rw [ENNReal.div_self hD hDf] at hdiv
  simpa only [diskAverage, div_eq_mul_inv, ENNReal.tsum_mul_right, D] using hdiv

theorem one_le_tsum_plateMaximal_of_cover (U : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (hU : ∀ j, MeasurableSet (U j)) (δ : ℕ → ℝ≥0)
    (hδ : ∀ j, 0 < δ j ∧ δ j ≤ 1) {E : Set (EuclideanSpace ℝ (Fin n))}
    (hB : IsBesicovitch k E) (hcover : E ⊆ ⋃ j, U j) (V : Grassmannian n k) :
    1 ≤ (2 : ℝ≥0∞) ^ k * ∑' j, plateMaximal (δ j)
      ((thickening (δ j) (U j)).indicator (fun _ ↦ (1 : ℝ≥0∞))) V := by
  obtain ⟨a, ha⟩ := isBesicovitch_iff_unitDisk_subset.mp hB V.val V.property
  calc
    _ ≤ ∑' j, diskAverage ((U j).indicator (fun _ ↦ (1 : ℝ≥0∞))) V a :=
      one_le_tsum_diskAverage_of_cover U hU V a (ha.trans hcover)
    _ ≤ ∑' j, (2 : ℝ≥0∞) ^ k * plateMaximal (δ j)
        ((thickening (δ j) (U j)).indicator (fun _ ↦ (1 : ℝ≥0∞))) V :=
      ENNReal.tsum_le_tsum fun j ↦ diskAverage_indicator_le_plateMaximal (hU j) V a
        (hδ j).1 (hδ j).2
    _ = _ := ENNReal.tsum_mul_left

end NKBesicovitch.Hausdorff
