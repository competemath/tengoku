module

public import Tengoku

public section

namespace Set
variable {α : Type*} {s t : Set α}

-- TODO: Rename `inter_eq_left` to `inter_eq_left_iff`
@[simp] alias ⟨_, inter_eq_left'⟩ := inter_eq_left
@[simp] alias ⟨_, inter_eq_right'⟩ := inter_eq_right

@[local simp] lemma ne_empty_iff_nonempty : s ≠ ∅ ↔ s.Nonempty := nonempty_iff_ne_empty.symm

end Set
-- Tengoku: 1 registration(s) of this module made local so they do not change other libraries (generated)
