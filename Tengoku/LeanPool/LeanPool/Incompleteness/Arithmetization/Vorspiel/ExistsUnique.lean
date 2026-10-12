/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku

/-! # ExistsUnique -/

@[expose] public section

namespace Classical
variable {α : Sort*} {p : α → Prop} {r : α → α → Prop}

lemma exitsUnique_extend (h : ∀ x, p x → ∃! y, r x y) (default : α) (x : α) :
    ∃! y, (p x → r x y) ∧ (¬p x → y = default) := by
  by_cases hx : p x
  · simpa [hx] using h _ hx
  · simp [hx]

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def «extendedChoose!» (h : ∀ x, p x → ∃! y, r x y)
    (default : α) (x : α) : α := choose (exitsUnique_extend h default x).exists

end Classical
