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
This file proves various lemmas about sorting small lists and multisets.
-/

public section
namespace Tengoku.Kostkanumbers end Tengoku.Kostkanumbers open Tengoku.Kostkanumbers 
lemma _root_.Tengoku.Kostkanumbers.sorted_pair {a b : ℕ} (h : a ≥ b) : List.SortedGE [a, b] :=
  List.Pairwise.sortedGE (by simp [h])

lemma _root_.Tengoku.Kostkanumbers.sorted_triple {a b c : ℕ} (hab : a ≥ b) (hbc : b ≥ c) :
    List.SortedGE [a, b, c] := List.Pairwise.sortedGE (by simp [hab, hbc, le_trans hbc hab])

lemma _root_.Tengoku.Kostkanumbers.sort_pair_ge {a b : ℕ} (hab : a ≥ b) : ({a, b} : Multiset ℕ).sort (· ≥ ·) = [a, b] := by
  refine List.Perm.eq_of_pairwise' (List.pairwise_mergeSort' _ _) (sorted_pair hab).pairwise ?_
  exact List.Perm.trans (List.mergeSort_perm _ _) (by rfl)

lemma _root_.Tengoku.Kostkanumbers.sort_triple_le {a b c : ℕ} (hab : a ≥ b) (hbc : b ≥ c) :
    (({a, b, c} : Multiset ℕ).sort (· ≤ ·)) = [c, b, a] := by
  have habc : [a, b, c].reverse = [c, b, a] := by simp
  refine List.Perm.eq_of_pairwise' (List.pairwise_mergeSort' _ _) ?_ ?_
  · rw [← habc, List.pairwise_reverse]
    exact (sorted_triple hab hbc).pairwise
  · refine List.Perm.trans (List.mergeSort_perm _ _) ?_
    rw [← habc, List.perm_reverse]

lemma _root_.Tengoku.Kostkanumbers.sort_triple_ge {a b c : ℕ} (hab : a ≥ b) (hbc : b ≥ c) :
    (({a, b, c} : Multiset ℕ).sort (· ≥ ·)) = [a, b, c] :=
  List.Perm.eq_of_pairwise' (List.pairwise_mergeSort' _ _) (sorted_triple hab hbc).pairwise <|
    List.Perm.trans (List.mergeSort_perm _ _) (by rfl)

@[simp] lemma _root_.Tengoku.Kostkanumbers.max_triple {a b c : ℕ} (hab : a ≥ b) (hbc : b ≥ c) :
    ({a, b, c} : Multiset ℕ).toList.max (by simp) = a := by
  rw! [← Multiset.sort_getElem_zero_eq_max, sort_triple_ge hab hbc]
  rfl

@[simp] lemma _root_.Tengoku.Kostkanumbers.min_triple {a b c : ℕ} (hab : a ≥ b) (hbc : b ≥ c) :
    ({a, b, c} : Multiset ℕ).toList.min (by simp) = c := by
  rw! [← Multiset.sort_getElem_zero_eq_min, sort_triple_le hab hbc]
  rfl
-- Tengoku: root names of this library moved to Tengoku.Kostkanumbers so they do not collide with other libraries (generated)
