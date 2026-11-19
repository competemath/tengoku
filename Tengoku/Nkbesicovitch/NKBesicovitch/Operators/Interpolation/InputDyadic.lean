/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.Interpolation.Dyadic
public import Tengoku.Seed.Analysis.SpecificLimits.Basic
public import Tengoku.Seed.Algebra.Order.BigOperators.Ring.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Two dyadic superlevel series for a nonnegative input

Halving scales cover values at most one. Doubling scales cover larger
values, including infinity. The latter case is handled by a divergent
geometric series, so pointwise finiteness of the input is not assumed.
-/

public section

open Set
open scoped ENNReal

namespace NKBesicovitch

variable {X : Type*}

/--
@isnad1 id=le.1h3v.s7.b304fb579d79 from=translated src=- shape=46ac5c74 vocab=3efc0483
-/
theorem le_small_dyadic_sum (f : X → ℝ≥0∞) (x : X) (hx : f x ≤ 1) :
    f x ≤ ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) *
      {y | ENNReal.ofReal ((1 / 2 : ℝ) ^ j / 2) ≤ f y}.indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
  by_cases hz : f x = 0
  · rw [hz]
    exact zero_le
  obtain ⟨j, hj, hj'⟩ := exists_dyadic_scale_ennreal (pos_iff_ne_zero.mpr hz) zero_lt_one
    (by simpa only [ENNReal.ofReal_one] using hx)
  simp only [one_mul] at hj hj'
  have hm : x ∈ {y | ENNReal.ofReal ((1 / 2 : ℝ) ^ j / 2) ≤ f y} := hj.le
  have hterm := ENNReal.le_tsum (f := fun j : ℕ ↦ ENNReal.ofReal ((1 / 2 : ℝ) ^ j) *
    {y | ENNReal.ofReal ((1 / 2 : ℝ) ^ j / 2) ≤ f y}.indicator (fun _ ↦ (1 : ℝ≥0∞)) x) j
  rw [indicator_of_mem hm, mul_one] at hterm
  exact hj'.trans hterm

/--
@isnad1 id=le.1h3v.s7.e1b0331acdb0 from=translated src=- shape=54350569 vocab=d62b10cc
-/
theorem le_large_dyadic_sum (f : X → ℝ≥0∞) (x : X) (hx : 1 ≤ f x) :
    f x ≤ ∑' j : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (j + 1)) *
      {y | ENNReal.ofReal ((2 : ℝ) ^ j) ≤ f y}.indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
  by_cases htop : f x = ∞
  · have hm (j : ℕ) : x ∈ {y | ENNReal.ofReal ((2 : ℝ) ^ j) ≤ f y} := by simp [htop]
    simp_rw [indicator_of_mem (hm _), mul_one,
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat]
    rw [ENNReal.tsum_geometric_add_one]
    rw [tsub_eq_zero_iff_le.mpr (by norm_num : (1 : ℝ≥0∞) ≤ 2), ENNReal.inv_zero]
    simp
  have hx' : 1 ≤ (f x).toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono htop hx
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near hx' (by norm_num : (1 : ℝ) < 2)
  have hm : x ∈ {y | ENNReal.ofReal ((2 : ℝ) ^ j) ≤ f y} := by
    change ENNReal.ofReal ((2 : ℝ) ^ j) ≤ f x
    rw [← ENNReal.ofReal_toReal htop]
    exact ENNReal.ofReal_le_ofReal hj
  have hu : f x ≤ ENNReal.ofReal ((2 : ℝ) ^ (j + 1)) := by
    rw [← ENNReal.ofReal_toReal htop]
    exact ENNReal.ofReal_le_ofReal hj'.le
  have hterm := ENNReal.le_tsum (f := fun j : ℕ ↦ ENNReal.ofReal ((2 : ℝ) ^ (j + 1)) *
    {y | ENNReal.ofReal ((2 : ℝ) ^ j) ≤ f y}.indicator (fun _ ↦ (1 : ℝ≥0∞)) x) j
  rw [indicator_of_mem hm, mul_one] at hterm
  exact hu.trans hterm

/--
@isnad1 id=le.0h3v.s8.bbcbb22fff24 from=translated src=- shape=f60b7208 vocab=9a764fd5
-/
theorem le_dyadic_superlevel_sums (f : X → ℝ≥0∞) (x : X) :
    f x ≤ (∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) *
      {y | ENNReal.ofReal ((1 / 2 : ℝ) ^ j / 2) ≤ f y}.indicator (fun _ ↦ (1 : ℝ≥0∞)) x) +
        ∑' j : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (j + 1)) *
          {y | ENNReal.ofReal ((2 : ℝ) ^ j) ≤ f y}.indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
  rcases le_total (f x) 1 with hsmall | hlarge
  · exact (le_small_dyadic_sum f x hsmall).trans (le_add_of_nonneg_right zero_le)
  · exact (le_large_dyadic_sum f x hlarge).trans (le_add_of_nonneg_left zero_le)

end NKBesicovitch
