/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/
module

public import Tengoku
public import Tengoku.Kostkanumbers.KostkaNumbers.Util.Remove
public import Tengoku.Kostkanumbers.KostkaNumbers.Util.Counts
import all Tengoku.Kostkanumbers.KostkaNumbers.Util.Counts
import Tengoku.Kostkanumbers.KostkaNumbers.Util.Util

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

public section

/-!
The `fromCounts` operation takes a Multiset and interprets it as the tally of some set (in a minimal
way) such that there are more smaller numbers.  For example,
{4, 4, 2, 1, 1}.fromCounts = {0,0,0,0,1,1,1,1,2,2,3,4}.  This is the "inverse" of the `counts`
operation (see `fromCounts_counts`).  This is a natural operation in the context of SSYT, where a
partition μ={4,4,2,1,1} indicates that the tableau has 4 0's, 4 1's, 2 2's, 1 3, and 1 4.  That is,
the content of the tableau should be `μ.fromCounts` (see the definition of `kostkaNumber`).
-/

namespace Multiset

section Counts

variable {μ : Multiset ℕ}

noncomputable
def fromCounts (μ : Multiset ℕ) : Multiset ℕ := ∑ n : {n : ℕ | n < (μ.sort (· ≥ ·)).length},
  replicate ((μ.sort (· ≥ ·))[n.1]'(n.2)) n.1

lemma count_fromCounts {n : ℕ} (h : n < μ.card) :
    count n μ.fromCounts = (μ.sort (· ≥ ·))[n]'(by simp[h]) := by
  simp only [fromCounts, ge_iff_le, count_sum', count_replicate]
  rw [Finset.sum_eq_single_of_mem (⟨n, by simp[h]⟩ :
    {n : ℕ | n < (μ.sort (· ≥ ·)).length}) (Finset.mem_univ _)]
  · simp
  · grind

lemma mem_fromCounts (h0 : 0 ∉ μ) (n : ℕ) (hn : n < μ.card) :
    n ∈ μ.fromCounts := by
  rw [← count_pos, count_fromCounts hn]
  refine Nat.pos_of_ne_zero ?_
  contrapose! h0
  rw [← h0]
  have hn' : n < (μ.sort (· ≥ ·)).length := by simp [hn]
  have hm := List.getElem_mem hn'
  rwa [Multiset.mem_sort] at hm

lemma notMem_fromCounts (μ : Multiset ℕ) (n : ℕ) (hn : n ≥ μ.card) :
    n ∉ μ.fromCounts := by
  rw [← count_pos, fromCounts, count_sum']
  simp [count_replicate]
  lia

lemma mem_fromCounts_iff {n : ℕ} (h0 : 0 ∉ μ) :
    n ∈ μ.fromCounts ↔ n < μ.card := by
  constructor
  · contrapose!
    exact notMem_fromCounts μ n
  · exact mem_fromCounts h0 n

lemma map_count_fromCounts (μ : Multiset ℕ) :
    List.map (fun n ↦ count n μ.fromCounts) (List.range μ.card) = μ.sort (· ≥ ·) :=
  List.ext_getElem (by simp) (by grind [count_fromCounts])

lemma fromCounts_dedup (h0 : 0 ∉ μ) : μ.fromCounts.dedup = range μ.card :=
  dedup_eq_range (mem_fromCounts h0) (notMem_fromCounts μ)

lemma fromCounts_counts (h0 : 0 ∉ μ) : μ.fromCounts.counts = μ := by
  rw [counts, fromCounts_dedup h0, ← coe_range, map_coe, map_count_fromCounts]
  nth_rw 2 [← coe_toList μ]
  rw [coe_eq_coe]
  exact Multiset.sort_perm_toList _

lemma fromCounts_sorted (μ : Multiset ℕ) : List.Pairwise (· ≥ ·) <|
    List.map (fun n => Multiset.count n μ.fromCounts) (List.range μ.card) := by
  rw [map_count_fromCounts]
  exact Multiset.pairwise_sort _ _

@[simp]
lemma fromCounts_card : μ.fromCounts.card = μ.sum := by
  simp only [fromCounts, ge_iff_le, card_sum, card_replicate]
  let e : {n : ℕ | n < (μ.sort (· ≥ ·)).length} → Fin (μ.sort (· ≥ ·)).length :=
    fun n ↦ ⟨n, n.2⟩
  rw [Fintype.sum_bijective e ?_ _ (fun n ↦ (μ.sort (· ≥ ·))[n.1]) ?_]
  · rw [Fin.sum_univ_getElem, ← sum_coe]
    congr
    nth_rw 2 [← coe_toList μ]
    rw [coe_eq_coe]
    exact Multiset.sort_perm_toList _
  · constructor
    · intro n m
      grind
    · intro n
      use ⟨n.1, n.2⟩
  · simp [e]

@[simp] lemma fromCounts_zero : fromCounts 0 = 0 := by
  rw [← Multiset.bot_eq_zero, ← bot_counts_iff]
  refine fromCounts_counts ?_
  rw [bot_eq_zero]
  exact notMem_zero 0

@[simp] lemma fromCounts_bot : fromCounts ⊥ = ⊥ := by simp

lemma ne_zero_of_fromCounts_ne_zero (hμ : μ.fromCounts ≠ 0) : μ ≠ 0 := by
  contrapose! hμ
  rw [hμ, fromCounts_zero]

lemma zero_mem_fromCounts_of_nonempty (hμ : μ.fromCounts ≠ 0) : 0 ∈ μ.fromCounts := by
  have hex : ∃ n, n ∈ μ.fromCounts := by
    contrapose! hμ
    exact eq_zero_of_forall_notMem hμ
  obtain ⟨n, hn⟩ := hex
  rw [← count_pos, count_fromCounts] at hn
  · rw [← count_pos, count_fromCounts]
    · refine lt_of_lt_of_le hn ?_
      refine List.Pairwise.rel_get_of_le (Multiset.pairwise_sort _ (· ≥ ·)) ?_
      simp
    · rw [Nat.pos_iff_ne_zero, ne_eq, card_eq_zero]
      exact ne_zero_of_fromCounts_ne_zero hμ
  · rw [count_pos] at hn
    contrapose! hn
    exact notMem_fromCounts μ n hn

lemma fromCounts_eq_zero_iff (μ : Multiset ℕ) (h0 : 0 ∉ μ) :
    μ.fromCounts = 0 ↔ μ = 0 := by
  rw [← Multiset.bot_eq_zero, ← Multiset.bot_counts_iff, Multiset.fromCounts_counts h0]

lemma fromCounts_eq_nil_iff (h0 : 0 ∉ μ) :
    μ.fromCounts.toList = [] ↔ μ.toList = [] := by
  rw [Multiset.toList_eq_nil, Multiset.toList_eq_nil, Multiset.fromCounts_eq_zero_iff μ h0]

lemma fromCounts_remove_card (h0 : 0 ∉ μ) :
    (μ.fromCounts.remove 0).toFinset.card = μ.card - 1 := by
  by_cases hμ : μ = 0
  · simp [hμ]
  · rw [remove_toFinset_card]
    · nth_rw 2 [← fromCounts_counts h0]
      rw [counts_card]
    · refine zero_mem_fromCounts_of_nonempty ?_
      rwa [ne_eq, fromCounts_eq_zero_iff μ h0]

lemma cons_fromCounts_of_min (n : ℕ) (h : ∀ m ∈ μ, m ≥ n) :
    (n ::ₘ μ).fromCounts = μ.fromCounts + Multiset.replicate n (μ.card) := by
  simp only [fromCounts, ge_iff_le, Multiset.sort_cons' h]
  let n' : {m | m < ((n ::ₘ μ).sort (· ≥ ·)).length} :=
    ⟨((n ::ₘ μ).sort (· ≥ ·)).length - 1, by simp⟩
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ n')]
  conv => lhs; rhs; simp [n']
  rw [add_left_inj]
  let e : (a : {m | m < ((n ::ₘ μ).sort (· ≥ ·)).length}) →
    (a ∈ (Finset.univ.erase n')) → {m | m < (μ.sort (· ≥ ·)).length} :=
    fun a ha ↦ ⟨a.1, by
      have ha' := a.2
      simp [n', ← Subtype.coe_inj] at ha ha'
      simp [Nat.lt_of_le_of_ne ha' ha]
      ⟩
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · simp [e]
  · simp [e]
  · simp only [Finset.mem_univ, Finset.mem_erase, ne_eq, and_true, Subtype.exists, ge_iff_le,
      length_sort, card_cons, Order.lt_add_one_iff, forall_const, Subtype.forall, Subtype.mk.injEq,
      exists_prop, exists_and_right, exists_eq_right, e]
    intro a ha
    use (by grind)
    simp [n']
    grind
  · simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true, Subtype.forall, ge_iff_le,
      length_sort, card_cons, Order.lt_add_one_iff, e]
    intro a ha ha'
    rw [List.getElem_append_left]

lemma erase_fromCounts_of_min (μ : Multiset ℕ) (hμ : μ.toList ≠ []) :
    (μ.erase (μ.toList.min hμ)).fromCounts = μ.fromCounts.remove (μ.card - 1) := by
  have hm : μ.toList.min hμ ∈ μ.toList := List.min_mem hμ
  rw [mem_toList] at hm
  nth_rw 3 [← cons_erase hm]
  rw [cons_fromCounts_of_min (μ.toList.min hμ), remove_add, remove_of_notMem, remove_replicate,
    empty_eq_zero, add_zero]
  · exact Multiset.card_erase_of_mem hm
  · exact notMem_fromCounts _ _ <| by simp [Multiset.card_erase_of_mem hm]
  · intro m hm
    exact List.min_le_of_mem <| by simp [mem_of_mem_erase hm]

lemma fromCounts_singleton {n : ℕ} (hn : n ≠ 0) :
    ({n} : Multiset ℕ).fromCounts = Multiset.replicate n 0 := by
  have hn0 : 0 ∉ ({n} : Multiset ℕ) := by
    rw [mem_singleton]
    exact hn.symm
  simp only [fromCounts, ge_iff_le, sort_singleton, List.getElem_singleton]
  rw [Finset.sum_eq_single_of_mem ⟨0, by simp⟩ (Finset.mem_univ _) (by simp; grind)]

end Counts

end Multiset
