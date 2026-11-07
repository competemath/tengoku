module

public import Tengoku.Seed.Logic.IsEmpty.Basic

namespace Classical
end Classical

namespace FoundationFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose]
public section

namespace Classical
open _root_.Classical
variable {α : Sort*} {p : α → Prop} {r : α → α → Prop}

noncomputable def choose! (h : ∃! x, p x) : α := choose h.exists

lemma choose!_spec (h : ∃! x, p x) : p (choose! h) := choose_spec h.exists

lemma choose_uniq (h : ∃! x, p x) (hx : p x) : x = choose! h := h.unique hx (choose!_spec h)

@[simp] lemma choose!_eq_iff_right (h : ∃! x, p x) : x = choose! h ↔ p x :=
  ⟨by rintro rfl; exact choose!_spec h, choose_uniq _⟩

@[simp] lemma choose!_eq_iff_left (h : ∃! x, p x) : choose! h = x ↔ p x := by
  rw [eq_comm]
  exact choose!_eq_iff_right h

lemma exitsUnique_extend (h : ∀ x, p x → ∃! y, r x y) (default : α) (x : α) : ∃! y, (p x → r x y) ∧ (¬p x → y = default) := by
  by_cases hx : p x
  · simpa [hx] using h _ hx
  · simp [hx]

noncomputable def extendedChoose! (h : ∀ x, p x → ∃! y, r x y)
    (default : α) (x : α) : α := choose (exitsUnique_extend h default x).exists

end Classical

end
