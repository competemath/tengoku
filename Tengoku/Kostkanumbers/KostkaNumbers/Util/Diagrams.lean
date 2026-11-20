/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/
module

public import Tengoku
import Tengoku.Kostkanumbers.KostkaNumbers.Util.Util

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
This file contains some basic results about YoungDiagrams that I need that are not in Mathlib.
I intend to upstream most of these results to Mathlib.
-/

public section

namespace YoungDiagram

variable {γ : YoungDiagram}

@[simp] lemma bot_card : (⊥ : YoungDiagram).card = 0 := by simp

@[simp] lemma bot_rowLens : (⊥ : YoungDiagram).rowLens = [] := by
  simp [rowLens, colLen]

lemma eq_bot_iff_forall_notMem : γ = ⊥ ↔ ∀ i j : ℕ, (i, j) ∉ γ := by
  simp [YoungDiagram.ext_iff, Finset.eq_empty_iff_forall_notMem]

lemma eq_bot_iff_card_eq_zero : γ = ⊥ ↔ γ.card = 0 := by
  simp [YoungDiagram.ext_iff]

lemma eq_bot_iff_zero_zero_notMem : γ = ⊥ ↔ (0, 0) ∉ γ := by
  rw [eq_bot_iff_forall_notMem]
  refine ⟨fun h ↦ h 0 0, fun h i j ↦ ?_⟩
  contrapose! h
  exact γ.up_left_mem i.zero_le j.zero_le h

lemma eq_iff_rowLens_eq {γ γ' : YoungDiagram} : γ = γ' ↔ γ.rowLens = γ'.rowLens := by
  simp_rw [← equivListRowLens_apply_coe, Subtype.coe_inj, equivListRowLens.apply_eq_iff_eq]

lemma eq_iff_rowLens_eq' {γ γ' : YoungDiagram} :
    γ = γ' ↔ Multiset.ofList γ.rowLens = Multiset.ofList γ'.rowLens := by
  rw [eq_iff_rowLens_eq, Multiset.coe_eq_coe,
    List.perm_iff_eq_of_sortedGE γ.rowLens_sorted γ'.rowLens_sorted]

lemma colLen_mono {γ γ' : YoungDiagram} (h : γ' ≤ γ) (j : ℕ) : γ'.colLen j ≤ γ.colLen j := by
  by_contra!
  rw [← mem_iff_lt_colLen] at this
  apply h at this
  simp [mem_iff_lt_colLen] at this

lemma rowLen_mono {γ γ' : YoungDiagram} (h : γ' ≤ γ) (i : ℕ) : γ'.rowLen i ≤ γ.rowLen i := by
  by_contra!
  rw [← mem_iff_lt_rowLen] at this
  apply h at this
  simp [mem_iff_lt_rowLen] at this

@[simp]
lemma rowLen_bot : (⊥ : YoungDiagram).rowLen = 0 := by
  ext i
  rw [Pi.zero_apply, ← le_zero_iff, ← Std.not_lt, ← mem_iff_lt_rowLen]
  exact notMem_bot _

@[simp]
lemma colLen_bot : (⊥ : YoungDiagram).colLen = 0 := by
  ext i
  rw [Pi.zero_apply, ← le_zero_iff, ← Std.not_lt, ← mem_iff_lt_colLen]
  exact notMem_bot _

lemma card_sdiff {γ' : YoungDiagram} (h : γ' ≤ γ) :
    (γ.cells \ γ'.cells).card = γ.card - γ'.card := by
  rw [YoungDiagram.card, Finset.card_sdiff_of_subset h]

lemma row_transpose (γ : YoungDiagram) (i : ℕ) : γ.transpose.row i =
    Finset.image Prod.swap (γ.col i) := by
  ext x
  simp [row, col]
  grind

lemma col_transpose (γ : YoungDiagram) (i : ℕ) : γ.transpose.col i =
    Finset.image Prod.swap (γ.row i) := by
  nth_rw 2 [← transpose_transpose γ]
  rw [row_transpose γ.transpose, Finset.image_image, Prod.swap_swap_eq, Finset.image_id]

lemma col_eq_image_swap_transpose {γ : YoungDiagram} (i : ℕ) : γ.col i =
    Finset.image Prod.swap (γ.transpose.row i) := by
  rw [row_transpose, Finset.image_image, Prod.swap_swap_eq, Finset.image_id]

lemma row_eq_image_swap_transpose {γ : YoungDiagram} (i : ℕ) : γ.row i =
    Finset.image Prod.swap (γ.transpose.col i) := by
  rw [col_transpose, Finset.image_image, Prod.swap_swap_eq, Finset.image_id]

end YoungDiagram
