/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

import Tengoku.Leancert.LeanCert.QProduct.Finite
import Tengoku.Seed.Algebra.Ring.GeomSum
import Tengoku.Seed.Data.Finset.Image
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.Basic
import Tengoku.Seed.Topology.Algebra.Monoid

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Stability lemmas for finite q-product integrals

This file proves the elementary order facts used by the directed-limit theory:
on `[0,1]`, every positive exponent factor `1 - u^n` lies in `[0,1]`, so finite
products are nonnegative, bounded by one, and antitone in the exponent set.
-/

namespace LeanCert.QProduct

open scoped BigOperators
open MeasureTheory

theorem pow_mem_unit_interval {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (n : Nat) :
    u ^ n ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨pow_nonneg hu.1 n, pow_le_one₀ hu.1 hu.2⟩

/-- The finite product profile is nonnegative on `[0,1]`. -/
theorem qProd_nonneg (S : Finset Nat) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ qProd S u := by
  classical
  unfold qProd
  apply Finset.prod_nonneg
  intro n hn
  exact sub_nonneg.mpr (pow_mem_unit_interval hu n).2

/-- Product-integral values are nonnegative. -/
theorem F_nonneg (S : Finset Nat) : 0 ≤ F S := by
  unfold F
  have hInt : IntervalIntegrable (fun u => qProd S u) volume (0 : ℝ) 1 := by
    classical
    unfold qProd
    apply Continuous.intervalIntegrable
    exact continuous_finsetProd S fun n hn =>
      continuous_const.sub (continuous_id.pow n)
  apply intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  intro u hu
  exact qProd_nonneg S hu

/-- Odd exponent tails beginning at `5` telescope against the factor `1 - u^2`. -/
theorem odd_tail_telescope_bound (M : Nat) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (1 - u ^ 2) * (∑ j ∈ Finset.range (M + 1), u ^ (5 + 2 * j)) ≤ u ^ 5 := by
  have hsum :
      (∑ j ∈ Finset.range (M + 1), u ^ (5 + 2 * j)) =
        u ^ 5 * ∑ j ∈ Finset.range (M + 1), (u ^ 2) ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_add, pow_mul]
  rw [mul_comm]
  rw [hsum, mul_assoc, geom_sum_mul_neg]
  calc
    u ^ 5 * (1 - (u ^ 2) ^ (M + 1)) ≤ u ^ 5 * 1 := by
      apply mul_le_mul_of_nonneg_left
      · have hnonneg : 0 ≤ (u ^ 2) ^ (M + 1) := pow_nonneg (sq_nonneg u) _
        linarith
      · exact pow_nonneg hu.1 5
    _ = u ^ 5 := by ring

/-- Any finite set of odd exponents at least `5` and bounded by `M` is dominated
by the full odd geometric tail beginning at `5`. -/
theorem odd_tail_sum_le_geom (A : Finset Nat) (M : Nat)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hodd : ∀ q ∈ A, Odd q) (h5 : ∀ q ∈ A, 5 ≤ q) (hM : ∀ q ∈ A, q < M + 1) :
    ∑ q ∈ A, u ^ q ≤ ∑ j ∈ Finset.range (M + 1), u ^ (5 + 2 * j) := by
  classical
  let G : Finset Nat := (Finset.range (M + 1)).image (fun j => 5 + 2 * j)
  have hsub : A ⊆ G := by
    intro q hq
    rcases hodd q hq with ⟨k, hk⟩
    have hq5 := h5 q hq
    have hqM := hM q hq
    subst q
    refine Finset.mem_image.mpr ?_
    refine ⟨k - 2, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  have hsum_subset : ∑ q ∈ A, u ^ q ≤ ∑ q ∈ G, u ^ q := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro q hqG hqA
    exact pow_nonneg hu.1 q
  have hG :
      (∑ q ∈ G, u ^ q) = ∑ j ∈ Finset.range (M + 1), u ^ (5 + 2 * j) := by
    unfold G
    rw [Finset.sum_image]
    intro a ha b hb h
    simp only at h
    omega
  exact hsum_subset.trans_eq hG

end LeanCert.QProduct
