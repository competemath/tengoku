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
Some additional lemmas about Young Diagrams that are used.  These are either more complicated to
prove or more specific, so I don't plan to upstream them to Mathlib. The main result of this file is
`card_ofRowLens`, which shows `(ofRowLens L hL).card = L.sum`
-/

public section

namespace YoungDiagram

variable {γ : YoungDiagram}

lemma cells_eq_biUnion_row : γ.cells = Finset.biUnion
    (Finset.univ : Finset (Fin (γ.rowLens.length))) (fun x ↦ γ.row x) := by
  ext x
  simp only [mem_cells, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · intro h
    use ⟨x.1, by
      rw [length_rowLens, ← mem_iff_lt_colLen]
      exact γ.up_left_mem (by rfl) (Nat.zero_le x.2) h⟩
    simp [mem_row_iff, h]
  · grind [mem_row_iff]

lemma disjoint_row {i j : ℕ} (h : i ≠ j) : Disjoint (γ.row i) (γ.row j) := by
  grind [Disjoint, mem_row_iff]

lemma card_eq_sum_rowLens_get : γ.card = ∑ i : Fin (γ.rowLens.length), γ.rowLens.get i := by
  simp only [List.get_eq_getElem, get_rowLens, rowLen_eq_card]
  rw [← Finset.card_biUnion, YoungDiagram.card, cells_eq_biUnion_row]
  simp only [Set.PairwiseDisjoint, Finset.coe_univ]
  intro a _ b _ hab
  simp only [Function.onFun]
  exact disjoint_row <| Fin.val_ne_of_ne hab

lemma card_eq_sum_rowLens : γ.card = γ.rowLens.sum := by
  simp only [card_eq_sum_rowLens_get, List.get_eq_getElem, Fin.sum_univ_getElem]

@[simp]
lemma card_ofRowLens {L : List ℕ} {hL : L.SortedGE} (hp : ∀ x ∈ L, 0 < x) :
    (ofRowLens L hL).card = L.sum := by
  rw [card_eq_sum_rowLens_get, rowLens_ofRowLens_eq_self hp]
  simp only [List.get_eq_getElem, Fin.sum_univ_getElem]

@[simp]
lemma rowLen_eq_zero {γ : YoungDiagram} {i : ℕ} (hi : ¬ i < γ.colLen 0) :
    γ.rowLen i = 0 := by
  rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, Nat.pos_iff_ne_zero] at hi
  exact Function.notMem_support.mp hi

@[simp]
lemma rowLen_ofRowLens' {w : List ℕ} {hw : w.SortedGE} {i : ℕ} (hi : i < w.length) :
    (ofRowLens w hw).rowLen i = w[i] := by
  simp [rowLen, Nat.find_eq_iff, mem_ofRowLens, hi]

@[simp]
lemma colLen_ofRowLens_two {a b : ℕ} {hab : [a, b].SortedGE} {i : ℕ} :
    (ofRowLens [a, b] hab).colLen i = if i < a then if i < b then 2 else 1 else 0 := by
  split_ifs
  all_goals simp [colLen, Nat.find_eq_iff, mem_ofRowLens]; grind

@[simp]
lemma colLen_ofRowLens_three {a b c : ℕ} {habc : [a, b, c].SortedGE} {i : ℕ} :
    (ofRowLens [a, b, c] habc).colLen i =
    if i < a then if i < b then if i < c then 3 else 2 else 1 else 0 := by
  split_ifs
  all_goals simp [colLen, Nat.find_eq_iff, mem_ofRowLens]; grind

end YoungDiagram
