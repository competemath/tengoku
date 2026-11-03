import Tengoku.Seed.Data.Fintype.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Exact incoming sums under finite relabelling -/
set_option autoImplicit false
open scoped BigOperators
namespace MagnitudeConjecture
universe u v

/--
@isnad1 id=eq.1h6v.s6.c1e6c88f51d2 from=translated src=- shape=fabb6efd vocab=e9d686b1
-/
theorem incoming_sum_eq_of_equiv {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : α → α → ℕ) (g : β → β → ℕ)
    (h : ∀ a b, f a b = g (e a) (e b)) (b : α) :
    (∑ a, f a b) = ∑ a, g a (e b) :=
  (Finset.sum_congr rfl (fun a _ ↦ h a b)).trans (e.sum_comp (fun a ↦ g a (e b)))

end MagnitudeConjecture
