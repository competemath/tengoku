/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/
module

public import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Define a remove operation on multisets that removes all copies of a single element from a multiset.
-/

public section

namespace Multiset

section Remove

variable {α : Type*} [DecidableEq α] (S : Multiset α) (a : α)

def remove := S - (replicate (count a S) a)

/--
@isnad1 id=eq.0h2v.s5.94dcb7a4f8f7 from=translated src=- shape=71574104 vocab=4690da16
-/
@[simp] lemma remove_bot : remove (⊥ : Multiset α) a = ⊥ := by
  simp [remove]

/--
@isnad1 id=eq.0h2v.s5.e499156db9b6 from=translated src=- shape=08dc7e38 vocab=740d388a
-/
@[simp] lemma remove_zero : remove 0 a = 0 := by
  simp [remove]

/--
@isnad1 id=not.0h3v.s4.fad5320f8406 from=translated src=- shape=ba340462 vocab=53cdc14c
-/
@[grind ., simp]
lemma notMem_of_remove : a ∉ S.remove a := by
  simp [remove, ← count_eq_zero]

/--
@isnad1 id=eq.1h3v.s4.faadbb918ef0 from=translated src=- shape=e950396f vocab=53cdc14c
-/
lemma remove_of_notMem (ha : a ∉ S) : S.remove a = S := by
  rw [← count_pos, Nat.pos_iff_ne_zero] at ha
  push Not at ha
  rw [remove, ha, replicate_zero, Multiset.sub_zero]

/--
@isnad1 id=iff.1h4v.s5.4aebf5493cf4 from=translated src=- shape=cbe4ce9d vocab=53cdc14c
-/
lemma mem_remove_of_ne {a b : α} (h : a ≠ b) : b ∈ S.remove a ↔ b ∈ S := by
  simp [remove, mem_sub, count_replicate, h, count_pos]

variable {S : Multiset α} {a b : α}

/--
@isnad1 id=iff.1h4v.s5.b21beadf6126 from=translated src=- shape=0fe84d4b vocab=53cdc14c
-/
lemma mem_remove_of_mem (b : α) (h : a ∈ S) : a ∈ S.remove b ↔ b ≠ a := by
  grind [mem_remove_of_ne]

/--
@isnad1 id=mem.1h4v.s5.9a4f0a05a235 from=translated src=- shape=6fb8f08d vocab=53cdc14c
-/
lemma mem_of_mem_remove (h : b ∈ S.remove a) : b ∈ S := by
  rw [← count_pos]
  rw [remove, mem_sub] at h
  exact lt_of_le_of_lt (Nat.zero_le _) h

/--
@isnad1 id=eq.1h3v.s5.c4c8ee6e55bb from=translated src=- shape=ab38bbe7 vocab=93ffae3a
-/
lemma insert_remove_toFinset (ha : a ∈ S) : insert a (S.remove a).toFinset = S.toFinset := by
  grind [mem_of_mem_remove, mem_remove_of_ne]

/--
@isnad1 id=eq.0h3v.s4.67b13b8149be from=translated src=- shape=aedbc537 vocab=c3807b2c
-/
@[grind =]
lemma remove_toFinset (S : Multiset α) (a : α) : (S.remove a).toFinset = S.toFinset.erase a := by
  by_cases ha : a ∈ S
  · grind [insert_remove_toFinset]
  · grind [remove_of_notMem]

/--
@isnad1 id=eq.1h3v.s5.dc8b87995763 from=translated src=- shape=3065cd1d vocab=5ece672b
-/
lemma remove_toFinset_card (S : Multiset α) (a : α) (ha : a ∈ S) :
    (S.remove a).toFinset.card = S.toFinset.card - 1 := by grind

/--
@isnad1 id=eq.0h1v.s4.0e2771c7e81d from=translated src=- shape=7bb053c7 vocab=72b33a88
-/
lemma remove_zero_sum (μ : Multiset ℕ) : μ.sum = (μ.remove 0).sum := by
  by_cases! h0 : 0 ∉ μ
  · rw [remove_of_notMem μ 0 h0]
  simp only [Finset.sum_multiset_count, smul_eq_mul, remove, count_sub, count_replicate]
  rw [← insert_remove_toFinset h0, Finset.sum_insert_zero]
  · exact Finset.sum_congr rfl (by grind)
  · rw [mul_zero]

/--
@isnad1 id=eq.0h3v.s4.03b2fac645e8 from=translated src=- shape=523ad36e vocab=715729d9
-/
lemma cons_remove {μ : Multiset α} (a : α) : (a ::ₘ μ).remove a = μ.remove a := by
  simp [remove]

/--
@isnad1 id=le.0h3v.s5.fecf35ca12eb from=translated src=- shape=1f61805d vocab=a4c328c4
-/
lemma sub_card_le_card {s t : Multiset α} : (s - t).card ≤ s.card := by
  exact card_le_card <| Multiset.sub_le_self s t

/--
@isnad1 id=le.0h3v.s4.647a5f889755 from=translated src=- shape=f51e9c00 vocab=d0458603
-/
lemma remove_card_le_card {μ : Multiset α} {a : α} : (μ.remove a).card ≤ μ.card := by
  simp [remove, sub_card_le_card]

/--
@isnad1 id=eq.1h4v.s5.bd08b3d16601 from=translated src=- shape=34d0daf0 vocab=b5d4a308
-/
lemma remove_replicate {n : ℕ} {a b : α} (h : a = b) : (Multiset.replicate n a).remove b = ∅ := by
  simp [remove, h]

/--
@isnad1 id=eq.0h4v.s5.b41446398013 from=translated src=- shape=5852e890 vocab=4679048a
-/
lemma remove_add {s t : Multiset α} (a : α) : (s + t).remove a = s.remove a + t.remove a := by
  rw [remove, count_add, replicate_add, tsub_add_eq_tsub_tsub, add_comm, add_tsub_assoc_of_le,
    add_comm, add_tsub_assoc_of_le, remove, remove]
  · rw [← Multiset.filter_eq]
    exact filter_le _ t
  · rw [← Multiset.filter_eq]
    exact filter_le _ s

/--
@isnad1 id=eq.0h3v.s5.2ade3e66178b from=translated src=- shape=8c5e1371 vocab=042cc7ae
-/
lemma sub_remove {s : Multiset α} {a : α} : s - (s.remove a) = replicate (count a s) a := by
  rw [remove, tsub_tsub_cancel_of_le]
  rw [← Multiset.filter_eq]
  exact filter_le _ s

end Remove

end Multiset
