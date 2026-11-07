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

/--
@isnad1 id=subset.0h2v.s3.73bd0b034731 from=translated src=- shape=0e3af3f8 vocab=d254aeea
-/
@[simp] lemma none_subset (o : Option α) : none ⊆ o := IsSubsetOf.none

/--
@isnad1 id=subset.0h2v.s3.38dbe6be602c from=translated src=- shape=e63ba82f vocab=99031204
-/
@[simp] lemma some_subset_some_self (a : α) : some a ⊆ some a := IsSubsetOf.some a

/--
@isnad1 id=iff.0h2v.s4.74da0010c5df from=translated src=- shape=936540c2 vocab=d254aeea
-/
@[simp] lemma subset_none_iff (o : Option α) : o ⊆ none ↔ o = none := by
  cases o
  · simp
  · simp only [reduceCtorEq, iff_false]; rintro ⟨⟩

/--
@isnad1 id=iff.0h3v.s4.7ed40b5a66e8 from=translated src=- shape=9a2a552b vocab=99031204
-/
@[simp] lemma some_subset_some {a b : α} :
    some a ⊆ some b ↔ a = b := by
  constructor
  · rintro ⟨⟩; rfl
  · rintro rfl; exact IsSubsetOf.some a

end Option
