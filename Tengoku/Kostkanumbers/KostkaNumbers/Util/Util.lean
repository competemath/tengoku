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

/--
@isnad1 id=sortedge.0h3v.s4.ff7e718f9158 from=translated src=- shape=cce7a5b5 vocab=f7b90648
-/
lemma sortedGE_replicate {α : Type*} [Preorder α] {a : α} (n : ℕ) :
    (replicate n a).SortedGE := pairwise_replicate_of_refl.sortedGE

/--
@isnad1 id=iff.2h3v.s5.a1d84d9a29ee from=translated src=- shape=1bc8ab95 vocab=99ff3ce0
-/
lemma perm_iff_eq_of_sortedGE {α : Type*} [PartialOrder α] {l₁ l₂ : List α} (h₁ : l₁.SortedGE)
    (h₂ : l₂.SortedGE) : l₁.Perm l₂ ↔ l₁ = l₂ :=
  ⟨List.Perm.eq_of_sortedGE h₁ h₂, List.Perm.of_eq⟩

/--
@isnad1 id=pairwise.1h5v.s5.6a6022c5139d from=translated src=- shape=71ac038f vocab=803bbeea
-/
lemma pairwise_append_singleton {L : List α} (hL : Pairwise R L) (h : ∀ y ∈ L, R y x) :
    Pairwise R (L ++ [x]) := by
  simpa [pairwise_append, hL]

-- include dual version
/--
@isnad1 id=iff.1h2v.s6.248551d55631 from=translated src=- shape=e52a05a1 vocab=cfe2f2f1
-/
lemma max_eq_bot_iff {α : Type*} [Max α] [PartialOrder α] [OrderBot α] [Std.LawfulOrderSup α]
    {l : List α} (hl : l ≠ []) :
    l.max hl = ⊥ ↔ ∀ x ∈ l, x = ⊥ := by
  simp_rw [eq_bot_iff, List.max_le_iff]

-- include dual version
/--
@isnad1 id=eq.2h2v.s6.c35d5b80db0e from=translated src=- shape=6256b12b vocab=52d04702
-/
lemma min_eq_bot_of_bot_mem {α : Type*} [LinearOrder α] [OrderBot α]
    {l : List α} (hl : l ≠ []) (h : ⊥ ∈ l) :
    l.min hl = ⊥ := by
  rw [eq_bot_iff]
  exact min_le_of_mem h

/--
@isnad1 id=mem.3h3v.s5.98e845f62b29 from=translated src=- shape=228f3fd8 vocab=c6ab19da
-/
lemma mem_tail_of_mem_ne_head {α : Type*} {l : List α} {a : α} (hl : l ≠ []) (ha : a ∈ l)
    (hah : a ≠ l.head hl) :
    a ∈ l.tail := by
  rw [← List.cons_head_tail hl] at ha
  grind

end List

namespace Multiset

variable {α : Type*}

/--
@isnad1 id=iff.1h2v.s6.1e4b0f37d51c from=translated src=- shape=2030f0b7 vocab=1d11dcc7
-/
@[to_additive]
lemma prod_eq_one_iff_eq_one [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α]
    [CanonicallyOrderedMul α] {μ : Multiset α} (h0 : 1 ∉ μ) :
    μ.prod = 1 ↔ μ = 0 := by
  refine ⟨?_, fun h ↦ h ▸ prod_zero⟩
  rw [prod_eq_one_iff, eq_zero_iff_forall_notMem]
  grind

/--
@isnad1 id=le.1h1v.s5.7ad7696f7993 from=translated src=- shape=66868720 vocab=125cd7e5
-/
lemma card_le_sum (μ : Multiset ℕ) (hp : ∀ x ∈ μ, x > 0) : μ.card ≤ μ.sum := by
  grind [card_nsmul_le_sum hp]

/--
@isnad1 id=eq.1h3v.s6.030d438ab0dd from=translated src=- shape=84f8a81a vocab=d9e3dd9d
-/
lemma sum_erase' [DecidableEq α] [AddCommMonoid α] [PartialOrder α] [Sub α] [OrderedSub α]
    [AddLeftReflectLE α] {μ : Multiset α} {a : α} (h : a ∈ μ) : (μ.erase a).sum = μ.sum - a := by
  rw [← sum_erase h]
  simp only [add_tsub_cancel_left]

/--
@isnad1 id=eq.2h2v.s5.4a6ce1c2511e from=translated src=- shape=8b7130a0 vocab=bf4ba119
-/
lemma dedup_eq_range {M : Multiset ℕ} {m : ℕ} (h : ∀ n < m, n ∈ M) (h' : ∀ n ≥ m, n ∉ M) :
    M.dedup = range m := by
  ext n
  rw [count_eq_of_nodup (nodup_dedup M), count_eq_of_nodup (nodup_range m)]
  grind [mem_dedup, mem_range]

/--
@isnad1 id=iff.0h3v.s5.059b51bad272 from=translated src=- shape=c1e1faf0 vocab=11cb7289
-/
lemma erase_eq_zero_iff [DecidableEq α] (s : Multiset α) (a : α) :
    s.erase a = 0 ↔ s = 0 ∨ s = {a} := by
  rw [← coe_toList s, coe_erase, coe_eq_zero, List.erase_eq_nil_iff, coe_eq_zero, coe_eq_singleton]

-- expand to match List.erase_replicate suite of lemmas
/--
@isnad1 id=eq.0h3v.s5.0b003c7b3468 from=translated src=- shape=eb430673 vocab=08950749
-/
lemma erase_replicate [DecidableEq α] {n : ℕ} {a : α} :
    (replicate n a).erase a = replicate (n - 1) a := by
  rw [← Multiset.coe_replicate, Multiset.coe_erase, List.erase_replicate_self,
    Multiset.coe_replicate]

/--
@isnad1 id=eq.0h3v.s4.39cb2f2500b2 from=translated src=- shape=5908264a vocab=9d7deba4
-/
@[simp]
lemma replicate_toList {α : Type*} (a : α) (n : ℕ) :
    (replicate n a).toList = List.replicate n a := by
  simp [List.eq_replicate_iff, mem_replicate]

/--
@isnad1 id=iff.0h3v.s4.c4e8a986cecc from=translated src=- shape=36135a9f vocab=50232fca
-/
@[simp]
lemma replicate_eq_zero_iff {α : Type*} (n : ℕ) (a : α) :
    replicate n a = 0 ↔ n = 0 := by
  simp [replicate]

variable {r : α → α → Prop} [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r]

/--
@isnad1 id=eq.0h4v.s5.669f4d565c01 from=translated src=- shape=7be2b8e6 vocab=f066d13a
-/
lemma count_sort [DecidableEq α] {M : Multiset α} {x : α} :
    List.count x (M.sort r) = count x M := by
  simp [← coe_count]

/--
@isnad1 id=perm.0h3v.s5.35e5601992df from=translated src=- shape=d41b9d0c vocab=2f094099
-/
lemma sort_perm_toList (s : Multiset α) : (s.sort r).Perm s.toList := by
  nth_rw 1 [← coe_toList s]
  rw [coe_sort]
  exact List.mergeSort_perm _ _

-- model after corresponding Finset lemmas
/--
@isnad1 id=eq.1h2v.s6.6f9c6e3e4e18 from=translated src=- shape=50302796 vocab=5cd422ba
-/
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

/--
@isnad1 id=eq.1h2v.s6.cb1676156546 from=translated src=- shape=50302796 vocab=13198db9
-/
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
/--
@isnad1 id=iff.0h5v.s5.e4db7e4d0a7e from=translated src=- shape=8aa08753 vocab=44112ddb
-/
lemma sort_eq_replicate_iff {μ : Multiset α} {n : ℕ} {x : α} :
    (μ.sort r) = List.replicate n x ↔ μ = replicate n x := by
  simp [List.eq_replicate_iff, eq_replicate, length_sort, mem_sort]

/--
@isnad1 id=eq.0h3v.s5.e9f9ee78a0d5 from=translated src=- shape=ba59cc60 vocab=70fe5798
-/
@[simp]
lemma sort_sum (r : α → α → Prop) [DecidableRel r] [IsTrans α r]
    [Std.Antisymm r] [Std.Total r] [AddCommMonoid α] (s : Multiset α) :
    (s.sort r).sum = s.sum := by
  rw [← sum_toList s, (sort_perm_toList s).sum_eq]

/--
@isnad1 id=eq.0h5v.s6.b7cfd94053b5 from=translated src=- shape=b35c7e12 vocab=e5d7043b
-/
lemma sort_cons' {x : α} {R : α → α → Prop} {M : Multiset α} [DecidableRel R] [Std.Total R]
    [IsTrans α R] [Std.Antisymm R] (h : ∀ y ∈ M, R y x) :
    (x ::ₘ M).sort R = M.sort R ++ [x] := by
  refine List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ R) ?_ ?_
  · simpa [List.pairwise_append]
  · rw [← singleton_add, add_comm, ← coe_eq_coe, sort_eq, ← coe_add, coe_singleton, sort_eq]

end Multiset
