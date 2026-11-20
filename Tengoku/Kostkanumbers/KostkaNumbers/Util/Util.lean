/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/
module

public import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
This file contains some basic results about Lists and Multisets that I need that are not in Mathlib.
I intend to upstream most of these results to Mathlib.
-/

public section

namespace List

variable {α : Type*} {x : α} {R : α → α → Prop} {r : α → α → Bool}

lemma sortedGE_replicate {α : Type*} [Preorder α] {a : α} (n : ℕ) :
    (replicate n a).SortedGE := pairwise_replicate_of_refl.sortedGE

lemma perm_iff_eq_of_sortedGE {α : Type*} [PartialOrder α] {l₁ l₂ : List α} (h₁ : l₁.SortedGE)
    (h₂ : l₂.SortedGE) : l₁.Perm l₂ ↔ l₁ = l₂ :=
  ⟨List.Perm.eq_of_sortedGE h₁ h₂, List.Perm.of_eq⟩

lemma pairwise_append_singleton {L : List α} (hL : Pairwise R L) (h : ∀ y ∈ L, R y x) :
    Pairwise R (L ++ [x]) := by
  simpa [pairwise_append, hL]

-- include dual version
lemma max_eq_bot_iff {α : Type*} [Max α] [PartialOrder α] [OrderBot α] [Std.LawfulOrderSup α]
    {l : List α} (hl : l ≠ []) :
    l.max hl = ⊥ ↔ ∀ x ∈ l, x = ⊥ := by
  simp_rw [eq_bot_iff, List.max_le_iff]

-- include dual version
lemma min_eq_bot_of_bot_mem {α : Type*} [LinearOrder α] [OrderBot α]
    {l : List α} (hl : l ≠ []) (h : ⊥ ∈ l) :
    l.min hl = ⊥ := by
  rw [eq_bot_iff]
  exact min_le_of_mem h

lemma mem_tail_of_mem_ne_head {α : Type*} {l : List α} {a : α} (hl : l ≠ []) (ha : a ∈ l)
    (hah : a ≠ l.head hl) :
    a ∈ l.tail := by
  rw [← List.cons_head_tail hl] at ha
  grind

end List

namespace Multiset

variable {α : Type*}

@[to_additive]
lemma prod_eq_one_iff_eq_one [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α]
    [CanonicallyOrderedMul α] {μ : Multiset α} (h0 : 1 ∉ μ) :
    μ.prod = 1 ↔ μ = 0 := by
  refine ⟨?_, fun h ↦ h ▸ prod_zero⟩
  rw [prod_eq_one_iff, eq_zero_iff_forall_notMem]
  grind

lemma card_le_sum (μ : Multiset ℕ) (hp : ∀ x ∈ μ, x > 0) : μ.card ≤ μ.sum := by
  grind [card_nsmul_le_sum hp]

lemma sum_erase' [DecidableEq α] [AddCommMonoid α] [PartialOrder α] [Sub α] [OrderedSub α]
    [AddLeftReflectLE α] {μ : Multiset α} {a : α} (h : a ∈ μ) : (μ.erase a).sum = μ.sum - a := by
  rw [← sum_erase h]
  simp only [add_tsub_cancel_left]

lemma dedup_eq_range {M : Multiset ℕ} {m : ℕ} (h : ∀ n < m, n ∈ M) (h' : ∀ n ≥ m, n ∉ M) :
    M.dedup = range m := by
  ext n
  rw [count_eq_of_nodup (nodup_dedup M), count_eq_of_nodup (nodup_range m)]
  grind [mem_dedup, mem_range]

lemma erase_eq_zero_iff [DecidableEq α] (s : Multiset α) (a : α) :
    s.erase a = 0 ↔ s = 0 ∨ s = {a} := by
  rw [← coe_toList s, coe_erase, coe_eq_zero, List.erase_eq_nil_iff, coe_eq_zero, coe_eq_singleton]

-- expand to match List.erase_replicate suite of lemmas
lemma erase_replicate [DecidableEq α] {n : ℕ} {a : α} :
    (replicate n a).erase a = replicate (n - 1) a := by
  rw [← Multiset.coe_replicate, Multiset.coe_erase, List.erase_replicate_self,
    Multiset.coe_replicate]

@[simp]
lemma replicate_toList {α : Type*} (a : α) (n : ℕ) :
    (replicate n a).toList = List.replicate n a := by
  simp [List.eq_replicate_iff, mem_replicate]

@[simp]
lemma replicate_eq_zero_iff {α : Type*} (n : ℕ) (a : α) :
    replicate n a = 0 ↔ n = 0 := by
  simp [replicate]

variable {r : α → α → Prop} [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r]

lemma count_sort [DecidableEq α] {M : Multiset α} {x : α} :
    List.count x (M.sort r) = count x M := by
  simp [← coe_count]

lemma sort_perm_toList (s : Multiset α) : (s.sort r).Perm s.toList := by
  nth_rw 1 [← coe_toList s]
  rw [coe_sort]
  exact List.mergeSort_perm _ _

-- model after corresponding Finset lemmas
lemma sort_getElem_zero_eq_max {α : Type*} [LinearOrder α] {μ : Multiset α}
    (hμ : μ.toList ≠ []) :
    (μ.sort (· ≥ ·))[0]'(by simp [card_pos, ← toList_eq_nil, hμ]) =
    μ.toList.max hμ := by
  symm
  rw [List.max_eq_iff]
  simp_rw [mem_toList, ← mem_sort (· ≥ ·)]
  constructor
  · exact List.getElem_mem _
  · intro a ha
    obtain ⟨i, _, hia⟩ := List.getElem_of_mem ha
    rw [← hia]
    exact List.Pairwise.rel_get_of_le (pairwise_sort _ (· ≥ ·)) (by simp)

lemma sort_getElem_zero_eq_min {α : Type*} [LinearOrder α] {μ : Multiset α}
    (hμ : μ.toList ≠ []) :
    (μ.sort (· ≤ ·))[0]'(by simp [card_pos, ← toList_eq_nil, hμ]) =
    μ.toList.min hμ := by
  symm
  rw [List.min_eq_iff]
  simp_rw [mem_toList, ← mem_sort (· ≤ ·)]
  constructor
  · exact List.getElem_mem _
  · intro a ha
    obtain ⟨i, _, hia⟩ := List.getElem_of_mem ha
    rw [← hia]
    exact List.Pairwise.rel_get_of_le (pairwise_sort _ (· ≤ ·)) (by simp)

-- don't upstream
lemma sort_eq_replicate_iff {μ : Multiset α} {n : ℕ} {x : α} :
    (μ.sort r) = List.replicate n x ↔ μ = replicate n x := by
  simp [List.eq_replicate_iff, eq_replicate, length_sort, mem_sort]

@[simp]
lemma sort_sum (r : α → α → Prop) [DecidableRel r] [IsTrans α r]
    [Std.Antisymm r] [Std.Total r] [AddCommMonoid α] (s : Multiset α) :
    (s.sort r).sum = s.sum := by
  rw [← sum_toList s, (sort_perm_toList s).sum_eq]

lemma sort_cons' {x : α} {R : α → α → Prop} {M : Multiset α} [DecidableRel R] [Std.Total R]
    [IsTrans α R] [Std.Antisymm R] (h : ∀ y ∈ M, R y x) :
    (x ::ₘ M).sort R = M.sort R ++ [x] := by
  refine List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ R) ?_ ?_
  · simpa [List.pairwise_append]
  · rw [← singleton_add, add_comm, ← coe_eq_coe, sort_eq, ← coe_add, coe_singleton, sort_eq]

end Multiset
