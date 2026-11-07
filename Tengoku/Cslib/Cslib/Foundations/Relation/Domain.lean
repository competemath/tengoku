/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Tengoku.Seed.Data.Set.Basic
public import Tengoku.Cslib.Cslib.Foundations.Relation.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Relations: Domain and Codomain

This module proves basic properties of the domain and codomain of relations.

## References

* [*Simple Laws about Nonprominent Properties of Binary Relations*][Burghardt2018]

-/

@[expose] public section

namespace Relation

/--
@isnad1 id=eq.0h1v.s3.97baaad70f04 from=translated src=- shape=e7343cea vocab=effb579b
-/
@[simp, grind =]
theorem emptyHRelation_emptyRelation : (emptyHRelation : α → α → Prop) = emptyRelation := rfl

/--
@isnad1 id=iff.0h4v.s3.9c2e8b9763aa from=translated src=- shape=8519afb1 vocab=af38403c
-/
@[simp, grind =]
theorem emptyHrelation_apply (a : α) (b : β) : emptyHRelation a b ↔ False := .rfl

variable {β : Type*} {r : α → β → Prop}

/--
@isnad1 id=iff.0h4v.s5.818778de3cb8 from=translated src=- shape=5ad4530b vocab=de17c665
-/
@[simp, grind =] lemma mem_dom : a ∈ dom r ↔ ∃ b, r a b := .rfl
/--
@isnad1 id=iff.0h4v.s5.a645853395bb from=translated src=- shape=dc7f025d vocab=c052db56
-/
@[simp, grind =] lemma mem_cod : b ∈ cod r ↔ ∃ a, r a b := .rfl

/--
@isnad1 id=mem.0h6v.s4.6cccc7c80384 from=translated src=- shape=ef35d484 vocab=de17c665
-/
theorem of_dom (hab : r a b) : a ∈ dom r := by grind
/--
@isnad1 id=mem.0h6v.s4.862ee070106d from=translated src=- shape=78640411 vocab=c052db56
-/
theorem of_cod (hab : r a b) : b ∈ cod r := by grind

/--
@isnad1 id=le.1h4v.s5.ca926510f47b from=translated src=- shape=c6089c16 vocab=a5dd39e1
-/
@[gcongr] lemma dom_mono (h : r₁ ≤ r₂) : dom r₁ ⊆ dom r₂ := fun a ⟨b, hab⟩ => ⟨b, h a b hab⟩
/--
@isnad1 id=le.1h4v.s5.4cc150344eb2 from=translated src=- shape=03fe51d2 vocab=9c8b439f
-/
@[gcongr] lemma cod_mono (h : r₁ ≤ r₂) : cod r₁ ⊆ cod r₂ := fun b ⟨a, hab⟩ => ⟨a, h a b hab⟩

/--
@isnad1 id=eq.0h2v.s4.b5efd4bf5535 from=translated src=- shape=b5b4a323 vocab=5b70e2a1
-/
@[simp, grind =]
lemma dom_empty : dom (emptyHRelation : α → β → Prop) = ∅ := by grind

/--
@isnad1 id=eq.0h2v.s4.1d8c7c711932 from=translated src=- shape=f63d4d24 vocab=cc057a3a
-/
@[simp, grind =]
lemma cod_empty : cod (emptyHRelation : α → β → Prop) = ∅ := by grind

/--
@isnad1 id=iff.0h3v.s5.59aaf63ac434 from=translated src=- shape=780548b8 vocab=5b70e2a1
-/
@[simp, grind =]
lemma dom_eq_empty_iff : dom r = ∅ ↔ r = emptyHRelation where
  mp h := by
    ext a
    grind => have : a ∈ dom r; finish
  mpr := by grind

/--
@isnad1 id=iff.0h3v.s5.dc24f1f73ff3 from=translated src=- shape=f8d8e326 vocab=cc057a3a
-/
@[simp, grind =]
lemma cod_eq_empty_iff : cod r = ∅ ↔ r = emptyHRelation where
  mp h := by
    ext a b
    grind => have : b ∈ cod r; finish
  mpr h := by grind

/--
@isnad1 id=eq.0h3v.s4.9a6a8c026471 from=translated src=- shape=3943f3aa vocab=9ac5c9e2
-/
@[simp]
lemma cod_inv : cod (fun a b => r b a) = dom r := rfl

/--
@isnad1 id=eq.0h3v.s4.b8cba0145c86 from=translated src=- shape=3d32e3b5 vocab=9ac5c9e2
-/
@[simp]
lemma dom_inv : dom (fun a b => r b a) = cod r := rfl

/--
@isnad1 id=subsingl.0h2v.s4.4e4a58ee8081 from=translated src=- shape=f22ed751 vocab=ec3df128
-/
theorem _root_.Std.Trichotomous.subsingleton_cod (r : α → α → Prop) [Std.Trichotomous r] :
    Subsingleton ((cod r)ᶜ : Set α) := by
  constructor
  rintro ⟨b₁, _⟩ ⟨b₂, _⟩
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ b₁ b₂
  grind

/--
@isnad1 id=subsingl.0h2v.s4.f0bcfe902231 from=translated src=- shape=f22ed751 vocab=cc47e139
-/
theorem _root_.Std.Trichotomous.subsingleton_dom (r : α → α → Prop) [Std.Trichotomous r] :
    Subsingleton ((dom r)ᶜ : Set α) := by
  constructor
  rintro ⟨a₁, _⟩ ⟨a₂, _⟩
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ a₁ a₂
  grind

end Relation
