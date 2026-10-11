import Tengoku

@[simp, nontriviality]
lemma Function.LeftInverse.of_subsingleton {α : Sort*} {β : Sort*} [Subsingleton β]
    (g : α → β) (f : β → α) : Function.LeftInverse g f := fun _ ↦ Subsingleton.allEq ..

@[local simp, nontriviality]
lemma Function.RightInverse.of_subsingleton {α : Sort*} [Subsingleton α] {β : Sort*}
    (g : α → β) (f : β → α) : Function.RightInverse g f := fun _ ↦ Subsingleton.allEq ..

@[local simp]
lemma Function.LeftInverse.of_empty {α : Sort*} [IsEmpty α] {β : Sort*} (g : α → β)
    (f : β → α) :
    Function.LeftInverse g f := have := Function.isEmpty f; LeftInverse.of_subsingleton g f

@[local simp]
lemma Function.RightInverse.of_empty {α : Sort*} {β : Sort*} [IsEmpty β] (g : α → β)
    (f : β → α) :
    Function.RightInverse g f := have := Function.isEmpty g; RightInverse.of_subsingleton g f
-- Tengoku: 3 registration(s) of this module made local so they do not change other libraries (generated)
