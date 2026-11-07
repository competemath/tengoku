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

/--
@isnad1 id=var.1h2v.s4.0cff43e35db4 from=translated src=- shape=bc08f22d vocab=af73b5f9
-/
lemma choose!_spec (h : ∃! x, p x) : p (choose! h) := choose_spec h.exists

/--
@isnad1 id=eq.1h4v.s4.67375d45c23f from=translated src=- shape=58baea79 vocab=af73b5f9
-/
lemma choose_uniq (h : ∃! x, p x) (hx : p x) : x = choose! h := h.unique hx (choose!_spec h)

/--
@isnad1 id=iff.1h3v.s4.de202fff58b5 from=translated src=- shape=a028df09 vocab=af73b5f9
-/
@[simp] lemma choose!_eq_iff_right (h : ∃! x, p x) : x = choose! h ↔ p x :=
  ⟨by rintro rfl; exact choose!_spec h, choose_uniq _⟩

/--
@isnad1 id=iff.1h3v.s4.a5c0ecb9fceb from=translated src=- shape=3ecb26f5 vocab=af73b5f9
-/
@[simp] lemma choose!_eq_iff_left (h : ∃! x, p x) : choose! h = x ↔ p x := by
  rw [eq_comm]
  exact choose!_eq_iff_right h

/--
@isnad1 id=existsun.1h5v.s5.3e9983fb6044 from=translated src=- shape=b670e023 vocab=473e8df7
-/
lemma exitsUnique_extend (h : ∀ x, p x → ∃! y, r x y) (default : α) (x : α) : ∃! y, (p x → r x y) ∧ (¬p x → y = default) := by
  by_cases hx : p x
  · simpa [hx] using h _ hx
  · simp [hx]

noncomputable def extendedChoose! (h : ∀ x, p x → ∃! y, r x y)
    (default : α) (x : α) : α := choose (exitsUnique_extend h default x).exists

end Classical

end
