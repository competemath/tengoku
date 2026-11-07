/-
Copyright (c) 2026 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Tengoku.Cslib.Cslib.Foundations.Relation.Basic
public import Tengoku.Seed.Logic.Function.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Relations: preservation of properties -/

@[expose] public section

namespace Relation

open scoped Function

/-- A predicate preserved by a relation is also preserved by its reflexive closure.
@isnad1 id=iff.0h3v.s4.d7552342dfa4 from=translated src=- shape=0506bafc vocab=c59b0044
-/
@[simp, scoped grind =]
theorem preserves_reflGen_iff : Preserves (ReflGen r) P  ↔ Preserves r P := by grind [Preserves]

/-- A predicate preserved by a relation is also preserved by its transitive closure.
@isnad1 id=iff.0h3v.s4.3d1cdd655d7a from=translated src=- shape=d846a41f vocab=a8844227
-/
@[simp, scoped grind =]
theorem preserves_transGen_iff : Preserves (TransGen r) P ↔ Preserves r P := by
  constructor <;> intro h
  · grind [Preserves]
  · intro _ _ hxy
    induction hxy <;> grind [Preserves]

/-- A predicate is preserved by a relation iff it is preserves by its reflexive and transitive
closure.
@isnad1 id=iff.0h3v.s4.80f7db691ef5 from=translated src=- shape=0506bafc vocab=416bcf05
-/
@[simp, scoped grind =]
theorem preserves_reflTransGen_iff : Preserves (ReflTransGen r) P ↔ Preserves r P := by
  constructor <;> intro h
  · intro _ _ hab
    exact h (ReflTransGen.single hab)
  · change ReflTransGen r ≤ ((· ≤ ·) on P)
    exact reflTransGen_le_of_le h

end Relation
