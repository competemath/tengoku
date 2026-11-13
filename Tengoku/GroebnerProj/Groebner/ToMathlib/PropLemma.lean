module

public import Lean

public section
namespace Tengoku.GroebnerProj end Tengoku.GroebnerProj open Tengoku.GroebnerProj 
-- submitted: https://github.com/leanprover-community/mathlib4/pull/34755
/--
@isnad1 id=iff.0h2v.s3.15eb927f0de5 from=translated src=- shape=cafd86d0 vocab=e3b0c442
-/
@[local simp]
theorem Tengoku.GroebnerProj.and_imp_iff_and {a b : Prop} : a ∧ (a → b) ↔ a ∧ b :=
  ⟨fun ⟨a, b'⟩ ↦ ⟨a, b' a⟩, fun ⟨a, b⟩ ↦ ⟨a, fun _ ↦ b⟩⟩

-- submitted: https://github.com/leanprover-community/mathlib4/pull/34755
/--
@isnad1 id=iff.0h2v.s3.8e56e4ef55a5 from=translated src=- shape=c0b986d3 vocab=e3b0c442
-/
@[local simp]
theorem Tengoku.GroebnerProj.imp_and_iff_and {a b : Prop} : (a → b) ∧ a ↔ b ∧ a :=
  ⟨fun ⟨b', a⟩ ↦ ⟨b' a, a⟩, fun ⟨b, a⟩ ↦ ⟨fun _ ↦ b, a⟩⟩
-- Tengoku: 2 registration(s) of this module made local so they do not change other libraries (generated)
-- Tengoku: root names of this library moved to Tengoku.GroebnerProj so they do not collide with other libraries (generated)
