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

/--
@isnad1 id=eq.0h1v.s5.074548343f16 from=translated src=- shape=65788b7a vocab=bf7d200b
-/
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

/--
@isnad1 id=disjoint.1h3v.s4.8c71b44bdc43 from=translated src=- shape=61490a9f vocab=3e30804c
-/
lemma disjoint_row {i j : ℕ} (h : i ≠ j) : Disjoint (γ.row i) (γ.row j) := by
  grind [Disjoint, mem_row_iff]

/--
@isnad1 id=eq.0h1v.s5.0250ca76d4de from=translated src=- shape=081f2ef6 vocab=7bc28d25
-/
lemma card_eq_sum_rowLens_get : γ.card = ∑ i : Fin (γ.rowLens.length), γ.rowLens.get i := by
  simp only [List.get_eq_getElem, get_rowLens, rowLen_eq_card]
  rw [← Finset.card_biUnion, YoungDiagram.card, cells_eq_biUnion_row]
  simp only [Set.PairwiseDisjoint, Finset.coe_univ]
  intro a _ b _ hab
  simp only [Function.onFun]
  exact disjoint_row <| Fin.val_ne_of_ne hab

/--
@isnad1 id=eq.0h1v.s3.064b1d84a36d from=translated src=- shape=6b4ab8ce vocab=a64cbd68
-/
lemma card_eq_sum_rowLens : γ.card = γ.rowLens.sum := by
  simp only [card_eq_sum_rowLens_get, List.get_eq_getElem, Fin.sum_univ_getElem]

/--
@isnad1 id=eq.2h1v.s5.ab3ffb219737 from=translated src=- shape=5afac376 vocab=0e6a211b
-/
@[simp]
lemma card_ofRowLens {L : List ℕ} {hL : L.SortedGE} (hp : ∀ x ∈ L, 0 < x) :
    (ofRowLens L hL).card = L.sum := by
  rw [card_eq_sum_rowLens_get, rowLens_ofRowLens_eq_self hp]
  simp only [List.get_eq_getElem, Fin.sum_univ_getElem]

/--
@isnad1 id=eq.1h2v.s4.5fa867067217 from=translated src=- shape=6ff2fd9f vocab=77efc3b5
-/
@[simp]
lemma rowLen_eq_zero {γ : YoungDiagram} {i : ℕ} (hi : ¬ i < γ.colLen 0) :
    γ.rowLen i = 0 := by
  rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, Nat.pos_iff_ne_zero] at hi
  exact Function.notMem_support.mp hi

/--
@isnad1 id=eq.2h2v.s5.6aa181685a73 from=translated src=- shape=c3c8d48a vocab=726700eb
-/
@[simp]
lemma rowLen_ofRowLens' {w : List ℕ} {hw : w.SortedGE} {i : ℕ} (hi : i < w.length) :
    (ofRowLens w hw).rowLen i = w[i] := by
  simp [rowLen, Nat.find_eq_iff, mem_ofRowLens, hi]

/--
@isnad1 id=eq.1h3v.s6.cd0270313757 from=translated src=- shape=4d268a79 vocab=5fa1a57e
-/
@[simp]
lemma colLen_ofRowLens_two {a b : ℕ} {hab : [a, b].SortedGE} {i : ℕ} :
    (ofRowLens [a, b] hab).colLen i = if i < a then if i < b then 2 else 1 else 0 := by
  split_ifs
  all_goals simp [colLen, Nat.find_eq_iff, mem_ofRowLens]; grind

/--
@isnad1 id=eq.1h4v.s6.2f69a2df0198 from=translated src=- shape=48aa982f vocab=5fa1a57e
-/
@[simp]
lemma colLen_ofRowLens_three {a b c : ℕ} {habc : [a, b, c].SortedGE} {i : ℕ} :
    (ofRowLens [a, b, c] habc).colLen i =
    if i < a then if i < b then if i < c then 3 else 2 else 1 else 0 := by
  split_ifs
  all_goals simp [colLen, Nat.find_eq_iff, mem_ofRowLens]; grind

end YoungDiagram
