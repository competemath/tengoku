/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Hausdorff.ScaleNorm
public import Tengoku.Nkbesicovitch.NKBesicovitch.Hausdorff.CoverNorm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Summing the covering scales

Classifying positive radii by successive powers of one half gives a
countable open cover. Below dimension `n-α`, the maximal norms are bounded
by a convergent geometric series times the total covering cost.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace NKBesicovitch.Hausdorff

theorem dyadic_rpow_tsum_ne_top {t : ℝ} (ht : 0 < t) :
    (∑' j : ℕ, (((1 / 2 : ℝ≥0) ^ j : ℝ≥0) : ℝ≥0∞) ^ t) ≠ ∞ := by
  have he (j : ℕ) : (((1 / 2 : ℝ≥0) ^ j : ℝ≥0) : ℝ≥0∞) ^ t =
      (((1 / 2 : ℝ≥0) : ℝ≥0∞) ^ t) ^ j := by
    rw [ENNReal.coe_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      mul_comm (j : ℝ) t, ENNReal.rpow_mul_natCast]
  simp_rw [he]
  exact (tsum_geometric_lt_top.mpr (ENNReal.rpow_lt_one (by norm_num) ht)).ne

theorem exists_dyadic_cover {n : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin n))
    (r : ℕ → ℝ≥0) (hr : ∀ i, 0 < r i ∧ r i ≤ 1) :
    ∃ I : ℕ → Set ℕ, (∀ j i, i ∈ I j → (1 / 2 : ℝ≥0) ^ j / 2 ≤ r i ∧
        r i ≤ (1 / 2 : ℝ≥0) ^ j) ∧
      (⋃ i, ball (x i) (r i)) ⊆ ⋃ j, ⋃ i ∈ I j, ball (x i) (r i) := by
  choose J hJ using fun i ↦ exists_nat_pow_near_of_lt_one (hr i).1 (hr i).2
    (by norm_num : (0 : ℝ≥0) < 1 / 2) (by norm_num : (1 / 2 : ℝ≥0) < 1)
  refine ⟨fun j ↦ {i | J i = j}, ?_, ?_⟩
  · intro j i hi
    change J i = j at hi
    subst j
    constructor
    · simpa only [pow_succ, div_eq_mul_inv, one_mul] using (hJ i).1.le
    · exact (hJ i).2
  · intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨J i, mem_iUnion₂.mpr ⟨i, rfl, hi⟩⟩

end NKBesicovitch.Hausdorff
