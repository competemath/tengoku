module

public import Tengoku.Seed.Logic.Small.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose]
public section

section Small

variable {α : Type uα} {β : Type uβ}

theorem small_preimage_of_injective (f : α → β) (h : Function.Injective f) (s : Set β) [Small.{u} s] :
    Small.{u} (f ⁻¹' s) := small_of_injective (β := s) (f := fun x ↦ ⟨f x, x.prop⟩) fun x y ↦ by
  simp [Function.Injective.eq_iff h, SetCoe.ext_iff]

end Small

end
