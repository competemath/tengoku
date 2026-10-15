/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku

/-! # Collection -/

@[expose] public section

/-- Imported declaration from the Incompleteness formalization. -/
class Cons (β : outParam Type*) (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  cons : β → α → α
export Cons (cons)

instance (α : Type*) : Cons α (Set α) := ⟨insert⟩

instance (α : Type*) : Cons α (List α) := ⟨List.cons⟩

instance (α : Type*) : Cons α (Multiset α) := ⟨Multiset.cons⟩

instance (α : Type*) [DecidableEq α] : Cons α (Finset α) := ⟨insert⟩

/-- Imported declaration from the Incompleteness formalization. -/
class Collection (β : outParam Type*) (α : Type*) extends Membership β α, HasSubset α,
  EmptyCollection α, Cons β α where
  subset_iff {a b : α} : a ⊆ b ↔ ∀ x ∈ a, x ∈ b
  not_mem_empty (x : β) : ¬x ∈ (∅ : α)
  mem_cons_iff {x z : β} {a : α} : x ∈ cons z a ↔ x = z ∨ x ∈ a

attribute [simp] Collection.not_mem_empty Collection.mem_cons_iff

instance Set.collection : Collection α (Set α) where
  Subset a b := a ⊆ b
  subset_iff := iff_of_eq Set.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Cons.cons]

instance List.collection : Collection α (List α) where
  subset_iff := List.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Cons.cons]

instance Multiset.collection : Collection α (Multiset α) where
  subset_iff := Multiset.subset_iff
  not_mem_empty := by simp
  mem_cons_iff := by simp [Cons.cons]

instance Finset.collection [DecidableEq α] : Collection α (Finset α) where
  Subset a b := a ⊆ b
  subset_iff := Finset.subset_iff
  not_mem_empty := by simp
  mem_cons_iff := by simp [Cons.cons]

namespace Collection

variable {β α : Type*} [Collection β α]

/-- Imported declaration from the Incompleteness formalization. -/
def set : α → Set β := fun a ↦ {x | x ∈ a}

/--
@isnad1 id=iff.0h4v.s5.75a134d9567c from=translated src=- shape=715a9d10 vocab=08481e5b
-/
@[simp] lemma mem_set_iff {x : β} {a : α} : x ∈ (set a : Set β) ↔ x ∈ a := by simp [set]

/--
@isnad1 id=iff.0h4v.s5.f6fa3dc16635 from=translated src=- shape=7bf11ed6 vocab=3d7ffcf3
-/
lemma subset_iff_set_subset_set {a b : α} : a ⊆ b ↔ set a ⊆ set b := by simp [subset_iff, set]

/--
@isnad1 id=subset.0h3v.s4.a99d4a112adb from=translated src=- shape=7fdb9770 vocab=39b89325
-/
@[simp, refl] lemma subset_refl (a : α) : a ⊆ a := subset_iff_set_subset_set.mpr (Set.Subset.refl _)

/--
@isnad1 id=subset.2h5v.s5.66599c165a99 from=translated src=- shape=eea93a44 vocab=39b89325
-/
@[trans] lemma subset_trans {a b c : α} (ha : a ⊆ b) (hb : b ⊆ c) : a ⊆ c :=
  subset_iff_set_subset_set.mpr (Set.Subset.trans (subset_iff_set_subset_set.mp ha)
    (subset_iff_set_subset_set.mp hb))

/--
@isnad1 id=eq.2h4v.s5.88b293068300 from=translated src=- shape=ea04d4dc vocab=17623f6c
-/
lemma subset_antisymm {a b : α} (ha : a ⊆ b) (hb : b ⊆ a) : set a = set b :=
  Set.Subset.antisymm (subset_iff_set_subset_set.mp ha) (subset_iff_set_subset_set.mp hb)

/--
@isnad1 id=subset.0h3v.s4.82cff785c0f7 from=translated src=- shape=c17294d4 vocab=e64db3a0
-/
@[simp 1100] lemma empty_subset (a : α) : ∅ ⊆ a := by simp [subset_iff]

/--
@isnad1 id=mem.0h4v.s4.16eb898d6c7f from=translated src=- shape=a9eacf87 vocab=748bd97a
-/
@[simp 1100] lemma mem_cons (a : α) (x : β) : x ∈ cons x a := by simp [mem_cons_iff]

/--
@isnad1 id=subset.0h4v.s4.7342a9d923db from=translated src=- shape=8e650c91 vocab=0c9d7d77
-/
@[simp] lemma subset_cons (a : α) (x : β) :
    a ⊆ cons x a := by simp [subset_iff, mem_cons_iff]; tauto

/--
@isnad1 id=eq.0h2v.s4.9d0a596c52db from=translated src=- shape=8d06b88c vocab=3eba848c
-/
@[simp] lemma set_empty : set (∅ : α) = ∅ := by ext; simp [set]

/--
@isnad1 id=eq.0h4v.s5.70aad803f056 from=translated src=- shape=d6cc41c9 vocab=b1613f64
-/
@[simp] lemma set_cons (z : β) (a : α) : set (cons z a) = insert z (set a) := by ext; simp [set]

/-- Imported declaration from the Incompleteness formalization. -/
def Finite (a : α) : Prop := (set a).Finite

/--
@isnad1 id=finite.0h2v.s4.79754a1ca7f2 from=translated src=- shape=3d6731c5 vocab=f62d6fc3
-/
@[simp] lemma empty_finite : Finite (∅ : α) := by simp [Finite]

lemma _root_.Collection.Finite.of_subset {a b : α} (ha : Finite a) (h : b ⊆ a) : Finite b :=
  Set.Finite.subset ha (subset_iff_set_subset_set.mp h)

/--
@isnad1 id=iff.0h4v.s4.beb2b11b9795 from=translated src=- shape=87dc0cc3 vocab=2ec23e6b
-/
@[simp] lemma cons_finite_iff {z : β} {a : α} : Finite (cons z a) ↔ Finite a :=
  ⟨fun h ↦ h.of_subset (by simp), fun h ↦ by
    rw [Finite, set_cons]
    exact Set.Finite.insert z h⟩

/-- Imported declaration from the Incompleteness formalization. -/
def addList (a : α) : List β → α
  | [] => a
  | x :: xs => cons x (addList a xs)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.List.toCollection : List β → α
  | [] => ∅
  | x :: xs => cons x xs.toCollection

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def _root_.Finset.toCollection : Finset β → α := fun s ↦ s.toList.toCollection

/--
@isnad1 id=iff.0h4v.s5.2851b1d807cf from=translated src=- shape=6c070cb2 vocab=8e7b89d5
-/
@[simp] lemma mem_list_toCollection {x : β} {l : List β} : x ∈ (l.toCollection : α) ↔ x ∈ l := by
  induction l <;> simp [List.toCollection, *]

/--
@isnad1 id=iff.0h4v.s5.fd95c5e8799a from=translated src=- shape=6c070cb2 vocab=44cb9da4
-/
@[simp] lemma mem_finset_toCollection {x : β} {s : Finset β} : x ∈ (s.toCollection :
    α) ↔ x ∈ s := by simp [Finset.toCollection]

/--
@isnad1 id=finite.0h3v.s4.8aa51c841b3c from=translated src=- shape=bf7258da vocab=0374dede
-/
@[simp] lemma list_toCollection_finite (l : List β) : Finite (l.toCollection :
    α) := by simp [Finite, set]

/--
@isnad1 id=finite.0h3v.s4.955b2d9ba618 from=translated src=- shape=bf7258da vocab=228e44d2
-/
@[simp] lemma finset_toCollection_finite (s : Finset β) : Finite (s.toCollection :
    α) := by simp [Finite, set]

end Collection

namespace Set

variable {α : Type*}

/--
@isnad1 id=eq.0h3v.s4.dcaf98fb4932 from=translated src=- shape=51b6e16c vocab=f0e02ce5
-/
lemma cons_eq (a : α) (s : Set α) : cons a s = insert a s := rfl

/--
@isnad1 id=eq.0h2v.s4.e102abdce4b3 from=translated src=- shape=68b02d52 vocab=709c8e84
-/
@[simp] lemma collection_set (s : Set α) : Collection.set s = s := rfl

/--
@isnad1 id=iff.0h2v.s4.f1706a25e151 from=translated src=- shape=66a2bcec vocab=ee6831a1
-/
@[simp] lemma collection_finite_iff (s : Set α) :
    Collection.Finite s ↔ s.Finite := by simp [Collection.Finite]

end Set
