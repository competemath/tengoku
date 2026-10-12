/-
Copyright (c) 2026 Jonathan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Ho
-/
module

public import Tengoku
import Tengoku.LeanPool.LeanPool.Isoperimetric.PrekopaLeindler

/-!
# The Brunn–Minkowski inequality

This file deduces the Brunn–Minkowski inequality from the Prékopa–Leindler
inequality, both for the standard product measure on `ℝⁿ` and for the
Euclidean structure `EuclideanSpace ℝ (Fin n)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Pointwise

/-- Brunn–Minkowski when `A` has infinite volume. -/
lemma brunn_minkowski_infinite
    {d : ℕ} {A B C : Set (Fin (d + 1) → ℝ)}
    (hA : volume A = ⊤) (hB : B.Nonempty) (hABC : A + B ⊆ C)
    : (volume A)^((d:ℝ)+1)⁻¹ + (volume B)^((d:ℝ)+1)⁻¹ ≤ (volume C)^((d:ℝ)+1)⁻¹ := by
  have h_top_pow : (⊤ : ENNReal) ^ ((d : ℝ) + 1)⁻¹ = ⊤ :=
    ENNReal.top_rpow_of_pos Nat.inv_pos_of_nat
  calc
    (volume A)^((d:ℝ)+1)⁻¹ + (volume B)^((d:ℝ)+1)⁻¹ =
        (volume (A + {hB.some}))^((d:ℝ)+1)⁻¹ := by
      simp [hA, h_top_pow]
    _ ≤ (volume (A + B))^((d:ℝ)+1)⁻¹ := by gcongr; exact singleton_subset_iff.mpr hB.some_mem
    _ ≤ (volume C)^((d:ℝ)+1)⁻¹ := by gcongr

/-- Brunn–Minkowski when `A` has zero volume. -/
lemma brunn_minkowski_zero
    {d : ℕ} {A B C : Set (Fin (d + 1) → ℝ)}
    (hA_zero : volume A = 0) (hA_nonempty : A.Nonempty) (hABC : A + B ⊆ C)
    : (volume A)^((d:ℝ)+1)⁻¹ + (volume B)^((d:ℝ)+1)⁻¹ ≤ (volume C)^((d:ℝ)+1)⁻¹ := by
  have h_zero_pow : (0 : ENNReal) ^ ((d : ℝ) + 1)⁻¹ = 0 :=
    ENNReal.zero_rpow_of_pos Nat.inv_pos_of_nat
  simp only [hA_zero, h_zero_pow, zero_add]
  gcongr 1
  calc
    volume B = volume ({hA_nonempty.some} + B) := by simp
    _ ≤ volume (A + B) := by gcongr; exact singleton_subset_iff.mpr hA_nonempty.some_mem
    _ ≤ volume C := by gcongr
