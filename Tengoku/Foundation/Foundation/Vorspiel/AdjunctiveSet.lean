module

public import Tengoku.Seed.Data.Set.Finite.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section
namespace Tengoku.Foundation end Tengoku.Foundation open Tengoku.Foundation 
class Tengoku.Foundation.Adjoin (β : outParam Type*) (α : Type*) where
  adjoin : β → α → α
export Adjoin (adjoin)

instance (α : Type*) : Adjoin α (Set α) := ⟨insert⟩

instance (α : Type*) : Adjoin α (List α) := ⟨List.cons⟩

instance (α : Type*) : Adjoin α (Multiset α) := ⟨Multiset.cons⟩

instance (α : Type*) [DecidableEq α] : Adjoin α (Finset α) := ⟨insert⟩

class Tengoku.Foundation.AdjunctiveSet (β : outParam Type*) (α : Type*) extends Membership β α, HasSubset α, EmptyCollection α, Adjoin β α where
  subset_iff {a b : α} : a ⊆ b ↔ ∀ x ∈ a, x ∈ b
  not_mem_empty (x : β) : ¬x ∈ (∅ : α)
  mem_cons_iff {x z : β} {a : α} : x ∈ adjoin z a ↔ x = z ∨ x ∈ a

attribute [simp] AdjunctiveSet.not_mem_empty AdjunctiveSet.mem_cons_iff

instance Set.adjunctiveSet : AdjunctiveSet α (Set α) where
  Subset := (· ⊆ ·)
  subset_iff := iff_of_eq Set.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin]

instance List.adjunctiveSet : AdjunctiveSet α (List α) where
  subset_iff := List.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin]

instance Multiset.adjunctiveSet : AdjunctiveSet α (Multiset α) where
  subset_iff := Multiset.subset_iff
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin]

instance Finset.adjunctiveSet [DecidableEq α] : AdjunctiveSet α (Finset α) where
  Subset := (· ⊆ ·)
  subset_iff := Finset.subset_iff
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin]

namespace Tengoku.Foundation.AdjunctiveSet

variable {β α : Type*} [AdjunctiveSet β α]

def set : α → Set β := fun a ↦ {x | x ∈ a}

/--
@isnad1 id=iff.0h4v.s5.af3fdca5b01d from=translated src=- shape=715a9d10 vocab=d516e1f1
-/
@[simp] lemma mem_set_iff {x : β} {a : α} : x ∈ (set a : Set β) ↔ x ∈ a := by simp [set]

/--
@isnad1 id=iff.0h4v.s5.b71ead30b9ec from=translated src=- shape=7bf11ed6 vocab=dbe10b99
-/
lemma subset_iff_set_subset_set {a b : α} : a ⊆ b ↔ set a ⊆ set b := by simp [subset_iff, set]

/--
@isnad1 id=subset.0h3v.s4.f4616c845157 from=translated src=- shape=7fdb9770 vocab=15d53e40
-/
@[simp, refl] lemma subset_refl (a : α) : a ⊆ a := subset_iff_set_subset_set.mpr (Set.Subset.refl _)

/--
@isnad1 id=subset.0h3v.s4.34396109848c from=translated src=- shape=c17294d4 vocab=9bd6bd18
-/
@[simp] lemma empty_subset (a : α) : ∅ ⊆ a := by simp [subset_iff]

/--
@isnad1 id=mem.0h4v.s4.b1ab20978e0e from=translated src=- shape=a9eacf87 vocab=1e3be580
-/
@[simp] lemma mem_cons (a : α) (x : β) : x ∈ adjoin x a := by simp [mem_cons_iff]

/--
@isnad1 id=subset.0h4v.s4.352f05a4e08d from=translated src=- shape=8e650c91 vocab=b28d753e
-/
@[simp] lemma subset_cons (a : α) (x : β) : a ⊆ adjoin x a := by simp [subset_iff, mem_cons_iff]; tauto

/--
@isnad1 id=eq.0h2v.s4.4c69fe648a9e from=translated src=- shape=8d06b88c vocab=ef7cad3d
-/
@[simp] lemma set_empty : set (∅ : α) = ∅ := by ext; simp [set]

/--
@isnad1 id=eq.0h4v.s5.8079d3247e85 from=translated src=- shape=d6cc41c9 vocab=65bf3062
-/
@[simp] lemma set_cons (z : β) (a : α) : set (adjoin z a) = insert z (set a) := by ext; simp [set]

def Finite (a : α) : Prop := (set a).Finite

/--
@isnad1 id=finite.0h2v.s4.0fdf7e735788 from=translated src=- shape=3d6731c5 vocab=2da9f4f9
-/
@[simp] lemma empty_finite : Finite (∅ : α) := by simp [Finite]

/--
@isnad1 id=finite.2h4v.s5.8ade1c15cfc0 from=translated src=- shape=0e6b9482 vocab=8a549359
-/
lemma Finite.of_subset {a b : α} (ha : Finite a) (h : b ⊆ a) : Finite b :=
  Set.Finite.subset ha (subset_iff_set_subset_set.mp h)

/--
@isnad1 id=iff.0h4v.s4.baec3919c9d1 from=translated src=- shape=87dc0cc3 vocab=0f1c2726
-/
@[simp] lemma cons_finite_iff {z : β} {a : α} : Finite (adjoin z a) ↔ Finite a :=
  ⟨fun h ↦ h.of_subset (by simp), by simp [Finite]⟩

def addList (a : α) : List β → α
  | [] => a
  | x :: xs => adjoin x (addList a xs)

def _root_.List.toAdjunctiveSet : List β → α
  | [] => ∅
  | x :: xs => adjoin x xs.toAdjunctiveSet

noncomputable def _root_.Finset.toAdjunctiveSet : Finset β → α := fun s ↦ s.toList.toAdjunctiveSet

/--
@isnad1 id=iff.0h4v.s5.9f6a7a349864 from=translated src=- shape=6c070cb2 vocab=1026075e
-/
@[simp] lemma mem_list_toAdjunctiveSet {x : β} {l : List β} : x ∈ (l.toAdjunctiveSet : α) ↔ x ∈ l := by
  induction l <;> simp [List.toAdjunctiveSet, *]

/--
@isnad1 id=iff.0h4v.s5.6d14bb6da552 from=translated src=- shape=6c070cb2 vocab=9633d73f
-/
@[simp] lemma mem_finset_toAdjunctiveSet {x : β} {s : Finset β} : x ∈ (s.toAdjunctiveSet : α) ↔ x ∈ s := by simp [Finset.toAdjunctiveSet]

/--
@isnad1 id=finite.0h3v.s4.ce791b30f0e1 from=translated src=- shape=bf7258da vocab=ab1b3531
-/
@[simp] lemma list_toAdjunctiveSet_finite (l : List β) : Finite (l.toAdjunctiveSet : α) := by simp [Finite, set]

/--
@isnad1 id=finite.0h3v.s4.d043d3a18188 from=translated src=- shape=bf7258da vocab=7a82c8ad
-/
@[simp] lemma finset_toAdjunctiveSet_finite (s : Finset β) : Finite (s.toAdjunctiveSet : α) := by simp [Finite, set]

end Tengoku.Foundation.AdjunctiveSet

namespace Set

variable {α : Type*}

/--
@isnad1 id=eq.0h2v.s4.6525cc3b3f35 from=translated src=- shape=68b02d52 vocab=312e026e
-/
@[simp] lemma adjunctiveSet_set (s : Set α) : AdjunctiveSet.set s = s := rfl

/--
@isnad1 id=iff.0h2v.s4.286bf3a99c36 from=translated src=- shape=66a2bcec vocab=89354f6b
-/
@[simp] lemma adjunctiveSet_finite_iff (s : Set α) : AdjunctiveSet.Finite s ↔ s.Finite := by simp [AdjunctiveSet.Finite]

end Set

end
-- Tengoku: root names of this library moved to Tengoku.Foundation so they do not collide with other libraries (generated)
