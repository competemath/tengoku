/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Tengoku.Cslib.Cslib.Foundations.Relation.Domain

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Relations: Properties on set restrictions

## References

* [*Simple Laws about Nonprominent Properties of Binary Relations*][Burghardt2018]

-/

@[expose] public section

open Relation

namespace Set

variable (r : α → α → Prop) (s : Set α)

/--
@isnad1 id=iff.0h3v.s5.4884040fa679 from=translated src=- shape=ebbd5ad0 vocab=1b9bd344
-/
@[simp, grind .]
theorem refl_iff_reflOn : Std.Refl (α := s) r ↔ s.ReflOn r := by
  constructor
  · exact fun ⟨h⟩ a ha ↦ h ⟨a, ha⟩
  · exact fun h ↦ ⟨fun ⟨a, ha⟩ ↦ h a ha⟩

/--
@isnad1 id=iff.0h3v.s5.7133a3d07788 from=translated src=- shape=ebbd5ad0 vocab=f6bb39db
-/
@[simp, grind .]
theorem symm_iff_symmOn : Std.Symm (α := s) r ↔ s.SymmOn r := by
  constructor
  · exact fun ⟨h⟩ a ha b hb ab ↦ h ⟨a, ha⟩ ⟨b, hb⟩ ab
  · exact fun h ↦ ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ ab ↦ h a ha b hb ab⟩

-- for special cases of (co)domain, we provide constructive shortcut lemmas

/--
@isnad1 id=var.1h5v.s4.911e260c757c from=translated src=- shape=f54d4d9f vocab=259624e3
-/
theorem ReflOn.of_dom {r} : (dom r).ReflOn r → r a b → r a a
| h, hab => h a (Relation.of_dom hab)

/--
@isnad1 id=var.1h5v.s4.3cf72a33aa0a from=translated src=- shape=6ecf0167 vocab=f68737ce
-/
theorem ReflOn.of_cod {r} : (cod r).ReflOn r → r a b → r b b
| h, hab => h b (Relation.of_cod hab)

/--
@isnad1 id=var.1h7v.s5.45be316b6b86 from=translated src=- shape=15ec5907 vocab=b6b9596b
-/
theorem SymmOn.of_dom {r} : (dom r).SymmOn r → r a b → r b c → r b a
| h, hab, hbc => h a (Relation.of_dom hab) b (Relation.of_dom hbc) hab

end Set
