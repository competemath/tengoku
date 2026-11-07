module

public import Tengoku.Seed.Data.Option.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

namespace Option

variable {α : Type u}

inductive IsSubsetOf : Option α → Option α → Prop
| none : IsSubsetOf none o
| some (a : α) : IsSubsetOf (some a) (some a)

instance : HasSubset (Option α) := ⟨IsSubsetOf⟩

@[simp] lemma none_subset (o : Option α) : none ⊆ o := IsSubsetOf.none

@[simp] lemma some_subset_some_self (a : α) : some a ⊆ some a := IsSubsetOf.some a

@[simp] lemma subset_none_iff (o : Option α) : o ⊆ none ↔ o = none := by
  cases o
  · simp
  · simp only [reduceCtorEq, iff_false]; rintro ⟨⟩

@[simp] lemma some_subset_some {a b : α} :
    some a ⊆ some b ↔ a = b := by
  constructor
  · rintro ⟨⟩; rfl
  · rintro rfl; exact IsSubsetOf.some a

end Option
