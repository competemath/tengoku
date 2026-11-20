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

/--
@isnad1 id=eq.0h0v.s4.387eb2222de7 from=translated src=- shape=35225b15 vocab=9b21b923
-/
@[simp] lemma bot_card : (⊥ : YoungDiagram).card = 0 := by simp

/--
@isnad1 id=eq.0h0v.s4.1352d88c1443 from=translated src=- shape=f18a2434 vocab=05167080
-/
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

/--
@isnad1 id=le.1h3v.s4.357f242b83b3 from=translated src=- shape=c3066638 vocab=66e82273
-/
lemma colLen_mono {γ γ' : YoungDiagram} (h : γ' ≤ γ) (j : ℕ) : γ'.colLen j ≤ γ.colLen j := by
  by_contra!
  rw [← mem_iff_lt_colLen] at this
  apply h at this
  simp [mem_iff_lt_colLen] at this

/--
@isnad1 id=le.1h3v.s4.efc65f369c9b from=translated src=- shape=c3066638 vocab=a5a242dd
-/
lemma rowLen_mono {γ γ' : YoungDiagram} (h : γ' ≤ γ) (i : ℕ) : γ'.rowLen i ≤ γ.rowLen i := by
  by_contra!
  rw [← mem_iff_lt_rowLen] at this
  apply h at this
  simp [mem_iff_lt_rowLen] at this

/--
@isnad1 id=eq.0h0v.s5.b3d6fbeb899f from=translated src=- shape=24c74e3c vocab=3e10597b
-/
@[simp]
lemma rowLen_bot : (⊥ : YoungDiagram).rowLen = 0 := by
  ext i
  rw [Pi.zero_apply, ← le_zero_iff, ← Std.not_lt, ← mem_iff_lt_rowLen]
  exact notMem_bot _

/--
@isnad1 id=eq.0h0v.s5.afc5227ab6ee from=translated src=- shape=24c74e3c vocab=03505525
-/
@[simp]
lemma colLen_bot : (⊥ : YoungDiagram).colLen = 0 := by
  ext i
  rw [Pi.zero_apply, ← le_zero_iff, ← Std.not_lt, ← mem_iff_lt_colLen]
  exact notMem_bot _

/--
@isnad1 id=eq.1h2v.s5.02f9c77f416c from=translated src=- shape=0dc80236 vocab=e639b37a
-/
lemma card_sdiff {γ' : YoungDiagram} (h : γ' ≤ γ) :
    (γ.cells \ γ'.cells).card = γ.card - γ'.card := by
  rw [YoungDiagram.card, Finset.card_sdiff_of_subset h]

/--
@isnad1 id=eq.0h2v.s5.f2ca19c54a3f from=translated src=- shape=0c58fdc4 vocab=e83f77fa
-/
lemma row_transpose (γ : YoungDiagram) (i : ℕ) : γ.transpose.row i =
    Finset.image Prod.swap (γ.col i) := by
  ext x
  simp [row, col]
  grind

/--
@isnad1 id=eq.0h2v.s5.12849601aa67 from=translated src=- shape=0c58fdc4 vocab=e83f77fa
-/
lemma col_transpose (γ : YoungDiagram) (i : ℕ) : γ.transpose.col i =
    Finset.image Prod.swap (γ.row i) := by
  nth_rw 2 [← transpose_transpose γ]
  rw [row_transpose γ.transpose, Finset.image_image, Prod.swap_swap_eq, Finset.image_id]

/--
@isnad1 id=eq.0h2v.s5.aa0448272ce5 from=translated src=- shape=ab48286d vocab=e83f77fa
-/
lemma col_eq_image_swap_transpose {γ : YoungDiagram} (i : ℕ) : γ.col i =
    Finset.image Prod.swap (γ.transpose.row i) := by
  rw [row_transpose, Finset.image_image, Prod.swap_swap_eq, Finset.image_id]

/--
@isnad1 id=eq.0h2v.s5.8b26cbfb03f6 from=translated src=- shape=ab48286d vocab=e83f77fa
-/
lemma row_eq_image_swap_transpose {γ : YoungDiagram} (i : ℕ) : γ.row i =
    Finset.image Prod.swap (γ.transpose.col i) := by
  rw [col_transpose, Finset.image_image, Prod.swap_swap_eq, Finset.image_id]

end YoungDiagram
