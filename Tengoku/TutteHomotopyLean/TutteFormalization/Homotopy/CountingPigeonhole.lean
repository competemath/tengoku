import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace TutteFormalization.Homotopy

/-- The exact two-slot pigeonhole argument in B.26: every object occupies one
of two slots, each slot has at most one occupant, and two distinct objects exist.
@isnad1 id=ex.4h3v.s6.7fd5a61bb304 from=translated src=- shape=7d106152 vocab=e3b0c442
-/
theorem two_slots_exactly_two {β : Type*} (P Q : β → Prop)
    (cover : ∀ x, P x ∨ Q x)
    (uniqueP : ∀ x y, P x → P y → x = y)
    (uniqueQ : ∀ x y, Q x → Q y → x = y)
    (two : ∃ x y : β, x ≠ y) :
    ∃ x y, x ≠ y ∧ P x ∧ Q y ∧ ¬ Q x ∧ ¬ P y ∧ ∀ z, z = x ∨ z = y := by
  have finish : ∀ x y, x ≠ y → P x → Q y →
      x ≠ y ∧ P x ∧ Q y ∧ ¬ Q x ∧ ¬ P y ∧ ∀ z, z = x ∨ z = y := by
    intro x y hxy hx hy
    refine ⟨hxy,hx,hy,fun h => hxy (uniqueQ x y h hy),fun h => hxy (uniqueP x y hx h),?_⟩
    intro z
    rcases cover z with h | h
    · exact Or.inl (uniqueP z x h hx)
    · exact Or.inr (uniqueQ z y h hy)
  obtain ⟨x,y,hxy⟩ := two
  rcases cover x with hx | hx <;> rcases cover y with hy | hy
  · exact False.elim (hxy (uniqueP x y hx hy))
  · exact ⟨x,y,finish x y hxy hx hy⟩
  · exact ⟨y,x,finish y x hxy.symm hy hx⟩
  · exact False.elim (hxy (uniqueQ x y hx hy))
end TutteFormalization.Homotopy
