import Tengoku

/--
@isnad1 id=leftinve.0h4v.s4.776f55c48b79 from=translated src=- shape=24bcd855 vocab=45de8532
-/
@[simp, nontriviality]
lemma Function.LeftInverse.of_subsingleton {α : Sort*} {β : Sort*} [Subsingleton β]
    (g : α → β) (f : β → α) : Function.LeftInverse g f := fun _ ↦ Subsingleton.allEq ..

/--
@isnad1 id=rightinv.0h4v.s4.93672d060857 from=translated src=- shape=da0ef1f9 vocab=c8825d0e
-/
@[local simp, nontriviality]
lemma Function.RightInverse.of_subsingleton {α : Sort*} [Subsingleton α] {β : Sort*}
    (g : α → β) (f : β → α) : Function.RightInverse g f := fun _ ↦ Subsingleton.allEq ..

/--
@isnad1 id=leftinve.0h4v.s4.1b40b0ef610e from=translated src=- shape=da0ef1f9 vocab=94991645
-/
@[local simp]
lemma Function.LeftInverse.of_empty {α : Sort*} [IsEmpty α] {β : Sort*} (g : α → β)
    (f : β → α) :
    Function.LeftInverse g f := have := Function.isEmpty f; LeftInverse.of_subsingleton g f

/--
@isnad1 id=rightinv.0h4v.s4.0b7614bc6816 from=translated src=- shape=24bcd855 vocab=b9c2fa12
-/
@[local simp]
lemma Function.RightInverse.of_empty {α : Sort*} {β : Sort*} [IsEmpty β] (g : α → β)
    (f : β → α) :
    Function.RightInverse g f := have := Function.isEmpty g; RightInverse.of_subsingleton g f
-- Tengoku: 3 registration(s) of this module made local so they do not change other libraries (generated)
